module WellConnectedComponents {
  // Chapel modules.
  use Reflection;
  use Map;
  use List;
  use Set;
  use Random;
  use IO;
  use Time;
  use Sort;
  use Math;
  use Search;
  use CTypes;

  // Arachne modules.
  use WellConnectedComponentsMsg;
  use GraphArray;
  use Utils;
  use ConnectedComponents;
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;
  use Logging;

  // C header and object files.
  require "viecut_helpers/computeMinCut.h",
          "viecut_helpers/computeMinCut.o",
          "viecut_helpers/logger.cpp.o";
  
  extern proc c_computeMinCut(partition_arr: [] int, src: [] int, dst: [] int, n: int, m: int): int;

  /* Modified version of the standard set module intersection method to only return the size of
     the intersection. */
  proc setIntersectionSize(const ref a: set(?t, ?), const ref b: set(t, ?)) {
    // Internal way to force processor atomic instead of network atomic in multilocale mode.
    var size:chpl__processorAtomicType(int) = 0;

    /* Iterate over the smaller set */
    if a.size <= b.size {
      if a.parSafe && b.parSafe {
        forall x in a do if b.contains(x) then size.add(1);
      } else {
        for x in a do if b.contains(x) then size.add(1);
      }
    } else {
      if a.parSafe && b.parSafe {
        forall x in b do if a.contains(x) then size.add(1);
      } else {
        for x in b do if a.contains(x) then size.add(1);
      }
    }
    
    return size.read();
  }

  // Helper methods to return a specified criterion.
  proc log10Criterion(n:int, m:real) { return floor(log10(n:real)); }
  proc log2Criterion(n:int,  m:real) { return floor(log2(n:real)); }
  proc sqrtCriterion(n:int,  m:real) { return floor(sqrt(n:real)/5); }
  proc multCriterion(n:int,  m:real) { return floor(m*n:real); }

  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string, outputType: string,
               connectednessCriterion: string, connectednessCriterionMultValue: real, 
               preFilterMinSize: int, postFilterMinSize: int): int throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG1 = toSymEntry(g1.getComp("NEIGHBORS_SET_SDI"), set(int)).a;
    
    var finalVertices = new list(int, parSafe=true);
    var finalClusters = new list(int, parSafe=true);
    var globalId:atomic int = 0;

    
    var newClusterIdToOriginalClusterId = new map(int, int);
    var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
                            else if connectednessCriterion == "log2" then log2Criterion
                            else if connectednessCriterion == "sqrt" then sqrtCriterion
                            else if connectednessCriterion == "mult" then multCriterion
                            else log10Criterion;
      writeln("/************* graph info**************/");
      var totalVolume: int = 0;  // To store the total degree sum of the graph
      var graphMinDegree: int = g1.n_vertices;
      for v in 0..<g1.n_vertices{
        var degree = neighborsSetGraphG1[v].size;
        totalVolume += degree;
        graphMinDegree = if degree < graphMinDegree then degree else graphMinDegree;
      }
      var meanDegreeGraph :real = totalVolume / g1.n_vertices: real;

      writeln("graph totalVolume: ", totalVolume);
      writeln("graph MinDegree: ", graphMinDegree);

      writeln("meanDegreeGraph: ", meanDegreeGraph);
      writeln();
    /*
      Process file that lists clusterID with one vertex on each line to a map where each cluster
      ID is mapped to all of the vertices with that cluster ID. 
    */
    proc readClustersFile(filename: string) throws {
      var clusters = new map(int, set(int));
      var file = open(filename, ioMode.r);
      var reader = file.reader(locking=false);

      for line in reader.lines() {
        var fields = line.split();
        if fields.size >= 2 {
          var originalNode = fields(0): int;
          var clusterID = fields(1): int;
          const (found, idx) = binarySearch(nodeMapGraphG1, originalNode);

          if found {
            var mappedNode = idx;
            if clusters.contains(clusterID) {
              clusters[clusterID].add(mappedNode);
            } else {
              var s = new set(int);
              s.add(mappedNode);
              clusters[clusterID] = s;
            }
          }
          else {
            if logLevel == LogLevel.DEBUG {
              var outMsg = "Vertex not found in the graph: " + originalNode:string;
              wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            }
          }
        }
      }
      reader.close();
      file.close();
      var outMsg = "Number of clusters originally found in file: " + clusters.size:string;
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      return clusters;
    }

    /* Returns the edge list of the induced subgraph given a set of vertices. */
    proc getEdgeList(ref vertices: set(int)) throws {
      var srcList = new list(int);
      var dstList = new list(int);

      var v2idx = new map(int, int);
      var idx2v = vertices.toArray();
      sort(idx2v);

      for (v,idx) in zip(idx2v, idx2v.domain) do v2idx[v] = idx;

      // Gather the edges of the subgraph induced by the given vertices.
      for u in vertices {
        const ref neighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];
        for v in neighbors {
          if v2idx.contains(v) {
            srcList.pushBack(v2idx[u]);
            dstList.pushBack(v2idx[v]);
          }
        }
      }      

      // Convert lists to arrays since we need arrays for our edge list processing methods.
      var src = srcList.toArray();
      var dst = dstList.toArray();

      // Sort the redges and remove any multiples if they exist.
      // TODO: Do we actually need to sort and remove multiple edges? If the input graph is simple, 
      //       wouldn't any induced subgraphs also be simple?
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);

      return (uniqueSrc, uniqueDst, idx2v);
    }


    /* Define a custom tuple comparator. */
    record TupleComparator {
      proc compare(a: (int, int), b: (int, int)) {
        if a(0) != b(0) then return a(0)-b(0);
        else return a(1)-b(1);
      }
    }

    /* Function to sort edge lists based on src and dst nodes */
    proc sortEdgeList(ref src: [] int, ref dst: [] int) {
      // Move elements of src and dst to an array of tuples.
      var edges: [0..<src.size] (int, int);
      for i in 0..<src.size do edges[i] = (src[i], dst[i]);

      // Sort the array of tuples.
      var TupleComp: TupleComparator;
      sort(edges, comparator=TupleComp);
      
      // Split sorted edge list into two different arrays.
      var sortedSrc: [0..<src.size] int;
      var sortedDst: [0..<dst.size] int;
      for i in 0..<src.size {
        sortedSrc[i] = edges[i][0];
        sortedDst[i] = edges[i][1];
      }

      return (sortedSrc, sortedDst);
    }
 
    /* Function to remove duplicate edges from sorted edge lists. */
    proc removeMultipleEdges(ref src: [] int, ref dst: [] int) {
      var uniqueSrc = new list(int);
      var uniqueDst = new list(int);

      if src.size == 0 then return (src, dst);

      uniqueSrc.pushBack(src[0]);
      uniqueDst.pushBack(dst[0]);

      for i in 1..<src.size {
        if src[i] != src[i-1] || dst[i] != dst[i-1] {
          uniqueSrc.pushBack(src[i]);
          uniqueDst.pushBack(dst[i]);
        }
      }

      var noDupsSrc = uniqueSrc.toArray();
      var noDupsDst = uniqueDst.toArray();

      return (noDupsSrc, noDupsDst);
    }

    /* Function to calculate the degree of a vertex within a component/cluster/community. */
    proc calculateClusterDegree(ref members: set(int), vertex: int) throws {
      const ref neighbors = neighborsSetGraphG1[vertex];
      return setIntersectionSize(neighbors,members);
    }

    /* Writes a cluster out to a file DURING its well-connectedness check. Contains verbose output
      for debugging purposes. */
    proc writeClustersToFile(ref members:set(int), id:int, currentId:int, d:int, c:int) throws {
      var filename = outputPath + "_" + newClusterIdToOriginalClusterId[id]:string + "_" + id:string 
                   + currentId:string + "_" + members.size:string + "_" + d:string + "_" + c:string 
                   + ".tsv";
      var file = open(filename, ioMode.cw);
      var fileWriter = file.writer(locking=false);
      var mappedArr = nodeMapGraphG1[members.toArray()];

      fileWriter.writeln("# Original Cluster ID:             " + newClusterIdToOriginalClusterId[id]:string);
      fileWriter.writeln("# Connected Components Cluster ID: " + id:string);
      fileWriter.writeln("# Final Cluster ID:                " + currentId:string);
      fileWriter.writeln("# Cluster Depth:                   " + d:string);
      fileWriter.writeln("# Number of Members:               " + members.size:string);
      fileWriter.writeln("# Minimum Cut:                     " + c:string);
      fileWriter.writeln("# Members:                         ");
      for m in mappedArr do fileWriter.writeln(m:string);
      
      try fileWriter.close();
      try file.close();
    }

    /* Writes all clusters out to a file AFTER they are deemed well-connected. */
    proc writeClustersToFile() throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(finalVertices, finalClusters) do writer.writeln(nodeMapGraphG1[v], " ", c);

      writer.close();
      outfile.close();
    }

    /* Writes a cluster out to a file DURING its well-connectedness check. */
    proc writeClustersToFile(ref vertices: set(int), cluster:int) throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.a);
      var writer = outfile.writer(locking=true);

      for v in vertices do writer.writeln(nodeMapGraphG1[v], " ", cluster);

      writer.close();
      outfile.close();
    }

    /* Given a specific partition, removes vertices with degree one, and returns a new set. */
    proc removeDegreeOne(ref partition:set(int)): set(int) throws{
      writeln("*****************removeDegreeOne called***********************");

      if partition.size <= 1 {
        var zeroset = new set(int);
        return zeroset;
      }
      var reducedPartition = partition;
      for v in partition {
        var memberDegree = calculateClusterDegree(partition, v);
        if memberDegree < 2 then reducedPartition.remove(v);
      }
      return reducedPartition;
    }
    /*
    An O(m) Algorithm for Cores Decomposition of Networks
    Vladimir Batagelj and Matjaz Zaversnik, 2003.
    https://arxiv.org/abs/cs.DS/0310049
    
    // Currently, k_max is passed as a parameter but not utilized within the function.
 */


    // Define the kCoreDecomposition function
    proc kCoreDecomposition(ref clusterNodes: set(int), k_max: int) : set(int) throws {
        writeln("/////////////////////////kCoreDecomposition///////////////////////");
        writeln("clusterNodes: ", clusterNodes);
        // writeln("k_max: ", k_max);

        // Domain and degree initialization
        const coreKDomain: domain(int) = clusterNodes.toArray();
        var degrees: [coreKDomain] int = 0;  // Degree of each node
        var cores: [coreKDomain] int = 0;    // Core number of each node
        var maxDegree = 0;

        // Step 1: Calculate degrees and determine max degree
        // writeln("\nStep 1: Calculating degrees for each node...");
        for v in coreKDomain {
            degrees[v] = calculateClusterDegree(clusterNodes, v);
            if degrees[v] > maxDegree then maxDegree = degrees[v];
        }
        // writeln("Degrees of nodes: ", degrees);
        // writeln("Max degree: ", maxDegree);

        // Step 2: Initialize bins and fill bins based on degrees
        // writeln("\nStep 2: Initializing bins based on degrees...");
        var bins: [0..maxDegree] list(int);

        for v in coreKDomain {
            bins[degrees[v]].pushBack(v);  // Place each node in the appropriate bin based on its degree
        }
        // writeln("Initial bins: ", bins);

        // Step 3: Set up degree counters and cumulative start positions in bin array
        // writeln("\nStep 3: Setting up degree counters and bin start positions...");
        var degreeCount: [0..maxDegree] int = 0;

        // Count the number of vertices with each degree
        for d in 0..maxDegree {
            degreeCount[d] = bins[d].size;
        }
        // writeln("degreeCount: ", degreeCount);

        // Calculate cumulative starting positions for each degree in vert
        var binStart: [0..maxDegree] int = 1;  // Initialize all to 1
        for d in 1..maxDegree {
            binStart[d] = binStart[d-1] + degreeCount[d-1];
        }
        // writeln("Bin start positions: ", binStart);

        // Step 4: Initialize vert and pos arrays and populate with vertices ordered by degree
        // writeln("\nStep 4: Initializing vert and pos arrays...");
        // Extend vert array to n +1 to prevent out-of-bounds access
        var vert: [1..clusterNodes.size +1] int;  // 1..9 in your case
        var pos: [coreKDomain] int;

        // Populate vert and pos arrays
        for d in 0..maxDegree {
            for v in bins[d] {
                pos[v] = binStart[d];         // Store position of vertex v
                vert[binStart[d]] = v;        // Place vertex v in vert array at the start position
                binStart[d] += 1;             // Increment start position for the next vertex of the same degree
            }
        }
        // writeln("Initial vert array (vertices ordered by degree): ", vert);
        // writeln("Initial pos array (positions of vertices in vert): ", pos);

        // Step 4.1: Restore bin start positions to original
        //writeln("\nStep 4.1: Restoring bin start positions...");
        for d in 0..maxDegree {
            binStart[d] = binStart[d] - degreeCount[d];
        }
        // writeln("Restored bin start positions: ", binStart);

        // Step 5: Core decomposition process
        // writeln("\nStep 5: Starting core decomposition process...");
        for i in 1..clusterNodes.size {
            const v = vert[i];
            cores[v] = degrees[v];  // Assign core number based on degree
            // writeln("Processing vertex ", v, " with initial core value: ", cores[v]);

            // Update degrees of neighbors with higher degree
            const ref neighbors = neighborsSetGraphG1[v];
            for u in neighbors {
                if clusterNodes.contains(u) && degrees[u] > degrees[v] {
                    const du = degrees[u];
                    const pu = pos[u];
                    const pw = binStart[du];
                    const w = vert[pw];

                    // **Added Bounds Check: Ensure pw and pu are within valid range**
                    if (pw < 1 || pw > clusterNodes.size +1) {
                        // writeln("Error: 'pw' (", pw, ") is out of bounds for 'vert' array.");
                        continue;  // Skip this neighbor if index is out of bounds
                    }
                    if (pu < 1 || pu > clusterNodes.size +1) {
                        // writeln("Error: 'pu' (", pu, ") is out of bounds for 'vert' array.");
                        continue;  // Skip this neighbor if index is out of bounds
                    }

                    // Swap u and w in vert and update positions
                    if u != w {
                        pos[u] = pw;
                        vert[pu] = w;
                        pos[w] = pu;
                        vert[pw] = u;
                        // writeln("Swapped vertices ", u, " and ", w, " in vert array.");
                    }

                    // Increment start position in bin and decrease degree of u
                    binStart[du] += 1;
                    degrees[u] -= 1;

                    // writeln("Updated degree of neighbor ", u, " to ", degrees[u]);
                    // writeln("Updated pos[" , u, "] = ", pos[u], ", vert[" , pw, "] = ", u);
                }
            }
        }

        //writeln("\nFinal cores: ", cores);

        // Step 6: Populate coresSet with core numbers
        var coresSet: set(int);
        var peripherySet: set(int);
        //writeln("cores: ",cores);
        //writeln("cores domain: ",cores.domain);
        for v in coreKDomain {
            if cores[v] >= k_max{
              coresSet.add(v);
            }else{
              peripherySet.add(v);/////////////////I added but I should check correctness!!!!!!!!!!
            }
        }
        writeln("coresSet: ", coresSet);
        writeln("peripherySet: ", peripherySet);
        writeln("/////////////////////////kCoreDecomposition ENDED!///////////////////////");
        //Find Edges Connecting Periphery to Core
        // writeln("Edges connecting periphery to core:");
        // for edge in connectingEdges {
        //     writeln("Edge between Node ", edge(0), " and Node ", edge(1));
        return coresSet;
    } // end of kCoreDecomposition

    /* Function to calculate the conductance of a cluster */
    proc calculateConductance(ref cluster: set(int)) throws {
      var cutSizePrevios: int = totalVolume;
      var SumOutEdges: int = 0;
      var volumeCluster: int = 0;
      var volumeComplement: int = 0;
      var minDegreeCluster: int = g1.n_edges;  // 
      var maxCutSizePrevios = 0;       // Initialize with a low value for max comparison

      // Iterate through all vertices to calculate volumes, cutSize, and total graph volume
      for v in cluster {
        var neighbors = neighborsSetGraphG1[v];
        if v== 37 || v == 38 {
          writeln("neighbors ",v," are: ", neighbors);
        }
        volumeCluster += neighbors.size;
        var outEdge = neighbors - cluster;
        //writeln("outEdge: ", outEdge);
        SumOutEdges += outEdge.size;

        // Update minimum outEdge size
        cutSizePrevios = if outEdge.size < cutSizePrevios &&  outEdge.size > 0 then outEdge.size else cutSizePrevios;

        // Update maximum outEdge size
        maxCutSizePrevios = if outEdge.size > maxCutSizePrevios then outEdge.size else maxCutSizePrevios;

        // Update minimum degree in cluster
        minDegreeCluster = if neighbors.size < minDegreeCluster then neighbors.size else minDegreeCluster;
      }

      volumeComplement = totalVolume - volumeCluster;

      //writeln("*****************calculateConductance called***********************");


      // Calculate mean degrees for cluster and overall graph
      var meanDegreeCluster = volumeCluster / cluster.size: real;


      // Compute conductance
      var denom = min(volumeCluster, volumeComplement);
      var conductance: real;

      if denom > 0 then
        conductance = SumOutEdges / denom: real;
      else
        conductance = 0.0;
      var output: [0..4] real;
      output[0] = conductance;
      output[1] = SumOutEdges;
      output[2] = minDegreeCluster;
      output[3] = meanDegreeCluster;
      //output[0] = conductance;
      writeln("conductance: ", conductance);
      if conductance == 0 then writeln("This cluster seems to be far from other clusters (outlier cluster)!!"); 

      // writeln("volumeCluster: ", volumeCluster);
      // writeln("volumeComplement: ", volumeComplement);
      // Output intermediate calculations for verification
      writeln(cutSizePrevios, " <= Est. of Previos cutsize ");
      // writeln("Cluster SumOutEdges : ", SumOutEdges);
      writeln("Cluster Mean degree: ",meanDegreeCluster );
      writeln("Based on Mader's theorem for sure we have a ",((meanDegreeCluster+2)/2):int,"-edge-connected subgraph. (a lower bound)" );
      writeln("Based on Iequlaity. MinCut <= ", minDegreeCluster);
      // Calculate lower and upper bounds of lambda2
      var lambda2_lower = (conductance * conductance) / 2;
      var lambda2_upper = 2 * conductance;
      writeln("Based on Cheeger's Inequalit: ",lambda2_lower," <= λ2 <= ", lambda2_upper);
      writeln("λ2 Midpoint Approximation: ",(lambda2_lower + lambda2_upper)/2 );
      writeln("My metric: ",2 * conductance/(lambda2_lower + lambda2_upper) );
      //alpha*lambda2_lower + (1-alpha)* lambda2_upper

 
      writeln("//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*");
      writeln("λ2 == 0    --> Cluster is disconnected!");
      writeln("λ2 near 0  --> Cluster is weakly connected, and for sure there is 2 subcluster in it.");
      writeln("0 << λ2 < 1 --> Cluster is reasonably well-connected structure, with some potential for partitioning.");
      writeln("λ2 >= 1    --> Cluster has strong connectivity and robustness");
      writeln("//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*\n");

      return output;
    }// end of calculateConductance
    ////////////////////////////////////////////// find all mincut  ///////////////////////////
    /* Helper function to merge vertices */
    proc mergeVertices(v1: int, v2: int, ref adjCopy: map(int, set(int)), ref mergeMap: map(int, set(int))) {
        writeln("\nMerging vertex ", v2, " into ", v1);
        
        // Update merge tracking
        mergeMap[v1] |= mergeMap[v2];
        mergeMap.remove(v2);
        
        // Remove self references
        adjCopy[v1].remove(v1);
        adjCopy[v1].remove(v2);
        
        // Merge adjacency lists
        for u in adjCopy[v2] {
            if u != v1 {  // Avoid self-loops
                adjCopy[v1].add(u);
                adjCopy[u].remove(v2);
                adjCopy[u].add(v1);
            }
        }
        
        // Remove merged vertex
        adjCopy.remove(v2);
    }
    /* Calculate cut weight between two sets */
    proc calculateCutWeight(cutSet: set(int), ref adjCopy: map(int, set(int)), ref adj: map(int, set(int)), 
                          ref mergeMap: map(int, set(int))): (int, set((int, int))) {
        var cutWeight = 0;
        var cutEdges = new set((int, int));
        
        // For each vertex in the cut set
        for v in cutSet {
            // For each adjacent vertex
            for u in adjCopy[v] {
                if !cutSet.contains(u) {
                    // Count original edges between merged components
                    for orig_v in mergeMap[v] {
                        for orig_u in mergeMap[u] {
                            if adj[orig_v].contains(orig_u) {
                                cutEdges.add((min(orig_v, orig_u), max(orig_v, orig_u)));
                            }
                        }
                    }
                }
            }
        }
        
        cutWeight = cutEdges.size;
        return (cutWeight, cutEdges);
    }


    /* Stoer-Wagner algorithm to find the global minimum cut */
    proc stoerWagnerMinCut(ref members: set(int), ref adj: map(int, set(int))): (int, set(int), set((int, int))) throws {

        var minCutValue = max(int);
        var minCutSet = new set(int);
        var minCutEdges = new set((int, int));

        // Deep copy the adjacency lists to avoid modifying the original graph
        var adjCopy = new map(int, set(int));
        for v in adj.keys() {
            adjCopy[v] = new set(int);
            adjCopy[v] = adj[v];
        }

        // Keep track of merged vertices
        var mergeMap = new map(int, set(int)); // maps vertex -> set of vertices merged into it
        for v in members {
            mergeMap[v] = new set(int);
            mergeMap[v].add(v);
        }

        // Working set of vertices
        var vertices = new set(int);
        vertices = members;

        writeln("Starting Stoer-Wagner with vertices: ", vertices);
        writeln("Initial adjacency lists:");
        for v in adjCopy.keys() {
            writeln(v, " -> ", adjCopy[v]);
        }
        // Continue while more than one vertex remains
        while vertices.size > 1 {
            // Set of vertices included in the current phase
            // Track vertices in set A and their connectivity weights
            var inA = new set(int);
            var weights = new map(int, int); // Maps vertex -> total weight of edges to set A
            
            // Select first vertex arbitrarily (set in Chapel has no function for this so I wrote my own way)
            var first = -1;
            for v in vertices {
                first = v;
                break;
            }

            var prev = -1;  // Second to last vertex added
            var last = first;  // Last vertex added
            
            inA.add(first);
            writeln("\nNew phase starting with first vertex: ", first);

            // Initialize weights for all vertices not in A
            for v in vertices {
                if v != first {
                    weights[v] = 0;
                    if adjCopy[first].contains(v) {
                        weights[v] = 1; // Initialize with weight 1 for connected vertices
                    }
                }
            }
            writeln("Initial weights: ", weights);

            // Main phase loop - add vertices until all are in A
            while inA.size < vertices.size {
                // Find vertex not in A with maximum connectivity to A
                var maxWeight = -1;
                var maxVertex = -1;

                for v in vertices {
                    if !inA.contains(v) && weights[v] > maxWeight {
                        maxWeight = weights[v];
                        maxVertex = v;
                    }
                }
                if maxVertex == -1 {
                    writeln("Warning: No more connected vertices found");
                    break;
                }

                // Update tracking variables
                prev = last;
                last = maxVertex;
                inA.add(maxVertex);

                writeln("Added vertex ", maxVertex, " with weight ", maxWeight);
                
                // Update weights for remaining vertices
                for v in vertices {
                    if !inA.contains(v) {
                        if adjCopy[maxVertex].contains(v) {
                            weights[v] += 1; // Add weight 1 for each new edge
                        }
                    }
                }
                writeln("Updated weights: ", weights);
            }

            // Calculate CUT weight (sum of edges from last vertex to all others)
            var cutSet = new set(int);
            for v in vertices {
                if v != last {
                    cutSet.add(v);
                }
            }


            // Count edges crossing the cut in original graph
            var cutWeight = 0;
            var currentCutEdges = new set((int, int));
            var lastVertices = mergeMap[last];
            var cutSetVertices = new set(int);
            for v in cutSet {
                cutSetVertices |= mergeMap[v];
            }

            // Check edges between original vertices
            for v in cutSetVertices {
                for u in lastVertices {
                    if adj[v].contains(u) {
                        cutWeight += 1;
                        currentCutEdges.add((min(v,u), max(v,u)));
                    }
                }
            }

          writeln("\nPhase complete. \nCut weight: ", cutWeight, ", previous min: ", minCutValue, "Cut set: ", cutSet);
          // Update minimum cut if this is better
            if cutWeight < minCutValue {
                minCutValue = cutWeight;
                minCutSet.clear();
                minCutSet |= cutSetVertices;
                minCutEdges = currentCutEdges;

                writeln("\nNew minimum cut found!");
                writeln("Cut value: ", minCutValue);
                writeln("Cut set: ", minCutSet);
                writeln("Cut edges: ", minCutEdges);
            }

            // Merge the last two vertices (last into prev)
            if prev != -1 && last != -1 && prev != last {
                writeln("\nMerging vertex ", last, " into ", prev);
                writeln("Before merge adjacency lists:");
                for v in adjCopy.keys() {
                    writeln(v, " -> ", adjCopy[v]);
                }
                
                // Update merge tracking
                mergeMap[prev] |= mergeMap[last];
                mergeMap.remove(last);
                
                // Remove self-loops
                adjCopy[prev].remove(prev);
                adjCopy[prev].remove(last);
                
                // Merge adjacency lists
                for v in adjCopy[last] {
                    if v != prev {
                        adjCopy[prev].add(v);
                        adjCopy[v].remove(last);
                        adjCopy[v].add(prev);
                    }
                }
                
                // Remove merged vertex
                adjCopy.remove(last);
                vertices.remove(last);

                writeln("\nAfter merge:");
                writeln("Vertices remaining: ", vertices);
                writeln("Updated adjacency lists:");
                for v in adjCopy.keys() {
                    writeln(v, " -> ", adjCopy[v]);
                }
                writeln("Merge map:", mergeMap);
            }
        }

        writeln("\nFinal result:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Cut set: ", minCutSet);
        writeln("Cut edges: ", minCutEdges);

        return (minCutValue, minCutSet, minCutEdges);
    }// end of stoerWagnerMinCut

    /* Helper proc to print a graph */
    proc printGraph(ref vertices: set(int), ref adj: map(int, set(int))) throws{
        writeln("Graph:");
        writeln("Vertices: ", vertices);
        writeln("Edges:");
        for v in vertices {
            for u in adj[v] {
                if v < u {  // Print each edge only once
                    writeln(v, " -- ", u);
                }
            }
        }
    }// end of printGraph


    /* Test function */
    /* Test cases for the Stoer-Wagner minimum cut algorithm */
    proc testStoerWagner() throws {
        writeln("\n=== Running Stoer-Wagner Algorithm Tests ===\n");

        // Test 1: Simple square graph (original test)
        {
            writeln("Test 1: Simple square graph with diagonal");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..4 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            addEdge(1, 2);
            addEdge(2, 3);
            addEdge(3, 4);
            addEdge(4, 1);
            addEdge(2, 4);
            
            writeln("\nInput graph:");
            printGraph(members, adj);
            
            var (minCutValue, minCutSet, minCutEdges) = stoerWagnerMinCut(members, adj);
            
            writeln("\nResults:");
            writeln("Expected min cut: 2");
            writeln("Actual min cut: ", minCutValue);
            writeln("Cut set: ", minCutSet);
            writeln("Cut edges: ", minCutEdges);
            assert(minCutValue == 2, "Test 1 failed: incorrect min cut value");
        }

        // Test 2: Triangle graph (no cut should be 2)
        {
            writeln("\nTest 2: Triangle graph");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..3 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            addEdge(1, 2);
            addEdge(2, 3);
            addEdge(3, 1);
            
            writeln("\nInput graph:");
            printGraph(members, adj);
            
            var (minCutValue, minCutSet, minCutEdges) = stoerWagnerMinCut(members, adj);
            
            writeln("\nResults:");
            writeln("Expected min cut: 2");
            writeln("Actual min cut: ", minCutValue);
            writeln("Cut set: ", minCutSet);
            writeln("Cut edges: ", minCutEdges);
            assert(minCutValue == 2, "Test 2 failed: incorrect min cut value");
        }

        // Test 3: Path graph (should have min cut 1)
        {
            writeln("\nTest 3: Path graph");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..4 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            addEdge(1, 2);
            addEdge(2, 3);
            addEdge(3, 4);
            
            writeln("\nInput graph:");
            printGraph(members, adj);
            
            var (minCutValue, minCutSet, minCutEdges) = stoerWagnerMinCut(members, adj);
            
            writeln("\nResults:");
            writeln("Expected min cut: 1");
            writeln("Actual min cut: ", minCutValue);
            writeln("Cut set: ", minCutSet);
            writeln("Cut edges: ", minCutEdges);
            assert(minCutValue == 1, "Test 3 failed: incorrect min cut value");
        }

        // Test 4: Butterfly graph (should have min cut 2)
        {
            writeln("\nTest 4: Butterfly graph");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..5 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            // Center vertex is 1
            addEdge(1, 2);
            addEdge(1, 3);
            addEdge(1, 4);
            addEdge(1, 5);
            addEdge(2, 3);
            addEdge(4, 5);
            
            writeln("\nInput graph:");
            printGraph(members, adj);
            
            var (minCutValue, minCutSet, minCutEdges) = stoerWagnerMinCut(members, adj);
            
            writeln("\nResults:");
            writeln("Expected min cut: 2");
            writeln("Actual min cut: ", minCutValue);
            writeln("Cut set: ", minCutSet);
            writeln("Cut edges: ", minCutEdges);
            assert(minCutValue == 2, "Test 4 failed: incorrect min cut value");
        }

        // Test 5: Complete graph with 4 vertices (should have min cut 3)
        {
            writeln("\nTest 5: Complete graph K4");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..4 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            // Add all possible edges
            for i in 1..4 {
                for j in i+1..4 {
                    addEdge(i, j);
                }
            }
            
            writeln("\nInput graph:");
            printGraph(members, adj);
            
            var (minCutValue, minCutSet, minCutEdges) = stoerWagnerMinCut(members, adj);
            
            writeln("\nResults:");
            writeln("Expected min cut: 3");
            writeln("Actual min cut: ", minCutValue);
            writeln("Cut set: ", minCutSet);
            writeln("Cut edges: ", minCutEdges);
            assert(minCutValue == 3, "Test 5 failed: incorrect min cut value");
        }

        // Test 6: Disconnected graph (should have min cut 0)
        {
            writeln("\nTest 6: Disconnected graph");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..4 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            // Two disconnected edges
            addEdge(1, 2);
            addEdge(3, 4);
            
            writeln("\nInput graph:");
            printGraph(members, adj);
            
            var (minCutValue, minCutSet, minCutEdges) = stoerWagnerMinCut(members, adj);
            
            writeln("\nResults:");
            writeln("Expected min cut: 0");
            writeln("Actual min cut: ", minCutValue);
            writeln("Cut set: ", minCutSet);
            writeln("Cut edges: ", minCutEdges);
            assert(minCutValue == 0, "Test 6 failed: incorrect min cut value");
        }

        writeln("\n=== All tests completed ===\n");
    }





    /* Recursive function to find all minimum cuts */
    proc findAllMinCutsRecursive(
        ref members: set(int), 
        ref adj: map(int, set(int)),
        globalMinValue: int
    ): list((set(int), set((int,int)))) throws {
        var minCuts: list((set(int), set((int,int)))) = new list((set(int), set((int,int))));
        
        writeln("\nExploring subgraph with vertices: ", members);
        
        if members.size <= 1 then return minCuts;

        // Find min cut in current subgraph
        var (minCutValue, minCutSet, minCutEdges) = stoerWagnerMinCut(members, adj);
        
        writeln("Found cut of value ", minCutValue, " in current subgraph");
        writeln("Cut set: ", minCutSet);
        writeln("Cut edges: ", minCutEdges);

        // If this is a minimum cut, store it
        if minCutValue == globalMinValue {
            minCuts.pushBack((minCutSet, minCutEdges));
            writeln("Added to minimum cuts list");
        }

        // Split graph into two components based on the cut
        var setB = members - minCutSet;
        
        // Create adjacency lists for the two subgraphs
        var adjA = new map(int, set(int));
        var adjB = new map(int, set(int));
        
        // Build subgraph A
        for v in minCutSet {
            adjA[v] = new set(int);
            for u in adj[v] {
                if minCutSet.contains(u) {
                    adjA[v].add(u);
                }
            }
        }
        
        // Build subgraph B
        for v in setB {
            adjB[v] = new set(int);
            for u in adj[v] {
                if setB.contains(u) {
                    adjB[v].add(u);
                }
            }
        }
        
        // Recursively find min cuts in both subgraphs
        writeln("\nRecursing on subgraph A: ", minCutSet);
        var cutsA = findAllMinCutsRecursive(minCutSet, adjA, globalMinValue);
        minCuts.pushBack(cutsA);
        
        writeln("\nRecursing on subgraph B: ", setB);
        var cutsB = findAllMinCutsRecursive(setB, adjB, globalMinValue);
        minCuts.pushBack(cutsB);

        return minCuts;
    }

    /* Main function to find all minimum cuts */
    proc findAllMinCuts(
        ref members: set(int), 
        ref adj: map(int, set(int))
    ): (int, list((set(int), set((int,int))))) throws {
        // First find the global minimum cut value
        var (globalMinValue, _, _) = stoerWagnerMinCut(members, adj);
        writeln("\nGlobal minimum cut value: ", globalMinValue);
        
        // Get all minimum cuts through recursive process
        var allMinCuts = findAllMinCutsRecursive(members, adj, globalMinValue);
        
        writeln("\nAll minimum cuts found (", allMinCuts.size, " total):");
        for (cutSet, cutEdges) in allMinCuts {
            writeln("Cut set: ", cutSet);
            writeln("Cut edges: ", cutEdges);
            writeln("---");
        }

        return (globalMinValue, allMinCuts);
    }

    /* Comprehensive test suite for minimum cut algorithms */
    proc runAllTests() throws {
        writeln("\n=== Running Comprehensive Tests ===\n");

        // Test 1: Simple square with diagonal
        {
            writeln("Test 1: Square with diagonal (Original test case)");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..4 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            addEdge(1, 2);
            addEdge(2, 3);
            addEdge(3, 4);
            addEdge(4, 1);
            addEdge(2, 4);
            
            writeln("\nGraph structure:");
            printGraph(members, adj);
            
            var (minValue, allCuts) = findAllMinCuts(members, adj);
            writeln("\nExpected min cut: 2");
            writeln("Found min cut: ", minValue);
            writeln("Number of min cuts found: ", allCuts.size);
        }

        // Test 2: Triangle graph
        {
            writeln("\n\nTest 2: Triangle graph");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..3 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            addEdge(1, 2);
            addEdge(2, 3);
            addEdge(3, 1);
            
            writeln("\nGraph structure:");
            printGraph(members, adj);
            
            var (minValue, allCuts) = findAllMinCuts(members, adj);
            writeln("\nExpected min cut: 2");
            writeln("Found min cut: ", minValue);
            writeln("Number of min cuts found: ", allCuts.size);
        }

        // Test 3: Path graph
        {
            writeln("\n\nTest 3: Path graph (should have min cut 1)");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..4 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            addEdge(1, 2);
            addEdge(2, 3);
            addEdge(3, 4);
            
            writeln("\nGraph structure:");
            printGraph(members, adj);
            
            var (minValue, allCuts) = findAllMinCuts(members, adj);
            writeln("\nExpected min cut: 1");
            writeln("Found min cut: ", minValue);
            writeln("Number of min cuts found: ", allCuts.size);
        }

        // Test 4: Complete graph K4
        {
            writeln("\n\nTest 4: Complete graph K4 (should have min cut 3)");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..4 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            // Add all possible edges
            for i in 1..4 {
                for j in i+1..4 {
                    addEdge(i, j);
                }
            }
            
            writeln("\nGraph structure:");
            printGraph(members, adj);
            
            var (minValue, allCuts) = findAllMinCuts(members, adj);
            writeln("\nExpected min cut: 3");
            writeln("Found min cut: ", minValue);
            writeln("Number of min cuts found: ", allCuts.size);
        }

        // Test 5: Butterfly graph
        {
            writeln("\n\nTest 5: Butterfly graph");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..5 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            // Center vertex is 1
            addEdge(1, 2);
            addEdge(1, 3);
            addEdge(1, 4);
            addEdge(1, 5);
            addEdge(2, 3);
            addEdge(4, 5);
            
            writeln("\nGraph structure:");
            printGraph(members, adj);
            
            var (minValue, allCuts) = findAllMinCuts(members, adj);
            writeln("\nExpected min cut: 2");
            writeln("Found min cut: ", minValue);
            writeln("Number of min cuts found: ", allCuts.size);
        }

        // Test 6: Disconnected graph
        {
            writeln("\n\nTest 6: Disconnected graph (should have min cut 0)");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..4 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            // Two disconnected components
            addEdge(1, 2);
            addEdge(3, 4);
            
            writeln("\nGraph structure:");
            printGraph(members, adj);
            
            var (minValue, allCuts) = findAllMinCuts(members, adj);
            writeln("\nExpected min cut: 0");
            writeln("Found min cut: ", minValue);
            writeln("Number of min cuts found: ", allCuts.size);
        }

        // Test 7: Star graph
        {
            writeln("\n\nTest 7: Star graph");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..5 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            // Center is vertex 1
            addEdge(1, 2);
            addEdge(1, 3);
            addEdge(1, 4);
            addEdge(1, 5);
            
            writeln("\nGraph structure:");
            printGraph(members, adj);
            
            var (minValue, allCuts) = findAllMinCuts(members, adj);
            writeln("\nExpected min cut: 1");
            writeln("Found min cut: ", minValue);
            writeln("Number of min cuts found: ", allCuts.size);
        }

        // Test 8: Cycle graph
        {
            writeln("\n\nTest 8: Cycle graph");
            var members = new set(int);
            var adj = new map(int, set(int));
            
            for i in 1..5 {
                members.add(i);
                adj[i] = new set(int);
            }
            
            proc addEdge(u: int, v: int) {
                adj[u].add(v);
                adj[v].add(u);
            }
            
            addEdge(1, 2);
            addEdge(2, 3);
            addEdge(3, 4);
            addEdge(4, 5);
            addEdge(5, 1);
            
            writeln("\nGraph structure:");
            printGraph(members, adj);
            
            var (minValue, allCuts) = findAllMinCuts(members, adj);
            writeln("\nExpected min cut: 2");
            writeln("Found min cut: ", minValue);
            writeln("Number of min cuts found: ", allCuts.size);
        }

        writeln("\n=== Test Suite Completed ===");
    }

/* Use minimum cuts to find subclusters in a cluster */
proc findClusters(
    ref members: set(int), 
    ref adj: map(int, set(int)),
    threshold: int
) throws {
    var clusters: list(set(int)) = new list(set(int));
    var toProcess: list((set(int), map(int, set(int)))) = new list((set(int), map(int, set(int))));
    
    // Start with the whole graph
    toProcess.pushBack((members, adj));
    
    while toProcess.size > 0 {
        var (currentMembers, currentAdj) = toProcess.pop();
        
        if currentMembers.size <= 1 {
            if currentMembers.size == 1 {
                clusters.pushBack(currentMembers);
            }
            continue;
        }
        
        var (cutValue, cutSet, cutEdges) = stoerWagnerMinCut(currentMembers, currentAdj);
        
        // If cut value is above threshold, this is a cluster
        if cutValue > threshold {
            clusters.pushBack(currentMembers);
            continue;
        }
        
        // Otherwise, split into two subgraphs and continue processing
        var setB = currentMembers - cutSet;
        
        // Create subgraphs
        var adjA = new map(int, set(int));
        var adjB = new map(int, set(int));
        
        // Build adjacency lists for subgraphs
        for v in cutSet {
            adjA[v] = new set(int);
            for u in currentAdj[v] {
                if cutSet.contains(u) {
                    adjA[v].add(u);
                }
            }
        }
        
        for v in setB {
            adjB[v] = new set(int);
            for u in currentAdj[v] {
                if setB.contains(u) {
                    adjB[v].add(u);
                }
            }
        }
        
        toProcess.pushBack((cutSet, adjA));
        toProcess.pushBack((setB, adjB));
    }
    
    writeln("\nFound ", clusters.size, " clusters:");
    for cluster in clusters {
        writeln("Cluster: ", cluster);
    }
}
    ///////////////////////////////////////findBridgesInCluster////////////////////////////////////////////////////////

    // /* Define the threshold for small subclusters */
    // const threshold = 10;

    /* DFS function implementing Tarjan's Algorithm on the cluster */
    //The time complexity of implementation is O(N + E), where:

    // N is the number of vertices (nodes) in the cluster.
    // E is the number of edges within the cluster.
    proc DFS(u: int, parentNode: int, ref members: set(int),
            ref disc: [?D1] int, ref low: [?D2] int,
            ref subtree_size: [?D3] int, ref bridges: list((int, int)),
            ref time: int, const total_nodes: int, const threshold:int,
            ref min_diff: int, ref best_bridge: (int, int, int, int),
            ref parent: [?D4] int) {

        time += 1;
        disc[u] = time;
        low[u] = time;
        subtree_size[u] = 1;                       // Initialize subtree size
        parent[u] = parentNode;                    // Record the parent node

        // Access neighbors within the cluster
        var neig = neighborsSetGraphG1[u];
        var neighbors = members & neig; //neighbors are in cluster

        for v in neighbors {
            if v == parentNode {
                continue;                           // Skip the parent node
            }
            if disc[v] == -1 {
                //DFS(v, u, members, disc, low, subtree_size, bridges, time, total_nodes);
                DFS(v, u, members, disc, low, subtree_size, bridges, time, total_nodes, threshold, min_diff, best_bridge, parent);

                low[u] = min(low[u], low[v]);
                subtree_size[u] += subtree_size[v];  // Update subtree size

                // Check for bridge
                if low[v] > disc[u] {
                    // Edge (u, v) is a bridge
                    var component_size_v = subtree_size[v];
                    var component_size_u = total_nodes - subtree_size[v];

                    // Compute the absolute difference
                    var diff = abs(component_size_u - component_size_v);

                    // Update min_diff and best_bridge if this bridge gives a smaller difference
                    if diff < min_diff {
                        min_diff = diff;
                        best_bridge = (u, v, component_size_u, component_size_v);
                    }
                    // Check if one component is a small subcluster
                    if component_size_v <= threshold || component_size_u <= threshold {
                      //writeln("(",u," ,",v,") added. component_size_u: ", component_size_u, " component_size_v: ", component_size_v);
                        bridges.pushBack((u, v));
                    }
                }
            } else {
                low[u] = min(low[u], disc[v]);
            }
        }
    }

    /* Function to collect nodes in a component after removing the bridge */
    proc collectComponent(u: int, ref members: set(int), ref component: set(int), 
                             const excludeNode: int, ref visited: [?D1] bool) {
        component.add(u);
        visited[u] = true;
        var neig = neighborsSetGraphG1[u];
        var neighbors = members & neig;

        for v in neighbors {
            if v == excludeNode {
                continue; // Skip the bridge edge
            }
            if !visited[v] {
                collectComponent(v, members, component, excludeNode, visited);
            }
        }
    }// end of collectComponent

    /* Function to find bridges and small subclusters in the cluster */
    proc findBridgesInCluster(ref members: set(int)) {
        const total_nodes = members.size;  // Declare total_nodes here
        const memberDomain: domain(int) = members.toArray();
        var disc: [memberDomain] int = -1;
        var low : [memberDomain] int = -1;
        var subtree_size: [memberDomain] int = 0;
        var bridges: list((int, int));
        var parent: [memberDomain] int = -1; // Array to store parent of each node
        var time = 0;
        const threshold = members.size;  // find a way to set the threshold. square root of m?

        // Variables to keep track of the minimum difference and the best bridge
        var min_diff = total_nodes;
        var best_bridge: (int, int, int, int) = (-1, -1, -1, -1); // (u, v, component_size_u, component_size_v)

        // Call DFS for each unvisited vertex in the cluster
        for u in members {
            if disc[u] == -1 {
                //DFS(u, -1, members, disc, low, subtree_size, bridges, time, total_nodes, threshold = 10);
                DFS(u, -1, members, disc, low, subtree_size, bridges, time, total_nodes, threshold, min_diff, best_bridge, parent);

            }
        }

        // Output the bridge with the minimum difference
        if best_bridge(0) != -1 {
            writeln("\nThe best bridge in this cluster is between ", best_bridge(0), " and ", best_bridge(1));
            writeln("Component sizes are ", best_bridge(2), " and ", best_bridge(3));
            //writeln("Minimum size difference is ", min_diff);
                    
            // Collect nodes in the component containing best_bridge(1)
            var component_v = new set(int);
            var visited: [memberDomain] bool = false;

            collectComponent(best_bridge(1), members, component_v, best_bridge(0), visited);

            // The other component is the remaining nodes
            var component_u = members - component_v;

            writeln("Nodes in component containing ", best_bridge(1), ": ", component_v);
            writeln("Nodes in component containing ", best_bridge(0), ": ", component_u);

        } else {
            writeln("\nNo bridges found.");
        }
    }
///////////////////////////////////////////////////////////////////////////////////////////////

    /* Recursive method that processes a given set of vertices (partition), denotes if it is 
       well-connected or not, and if not calls itself on the new generated partitions. */
    proc wccRecursiveChecker(ref vertices: set(int), id: int, depth: int) throws {
      writeln("*****************wccRecursiveChecker called***********************");
      writeln("****** Let's check the cluster METRICS: \n");
      calculateConductance(vertices);
      var (src, dst, mapper) = getEdgeList(vertices);

      // If the generated edge list is empty, then return.
      if src.size < 1 then return;

      var n = mapper.size;
      var m = src.size;

      var partitionArr: [{0..<n}] int;
      var cut = c_computeMinCut(partitionArr, src, dst, n, m);
      writeln("cluster ",id, " passed to Viecut and cut_size is: ", cut);

      var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue):int;
      if cut > criterionValue { // Cluster is well-connected.
        var currentId = globalId.fetchAdd(1);
      writeln("$$$$$$ cluster ",id," with currentId " ,currentId," at depth ", depth," with cut ", cut, " is well Connected. ", "memebers are: ", vertices);

        if outputType == "debug" then writeClustersToFile(vertices, id, currentId, depth, cut);
        else if outputType == "during" then writeClustersToFile(vertices, currentId);
        for v in vertices {
          finalVertices.pushBack(v);
          finalClusters.pushBack(currentId);
        }
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " with depth " + depth:string + " and cutsize " 
                    + cut:string + " is well-connected with " + vertices.size:string + " vertices.";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        return;
      }
      else { // Cluster is not well-connected.
        var cluster1, cluster2 = new set(int);
        
        // Separate vertices into two partitions.
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.add(mapper[v]);
          else cluster2.add(mapper[v]);
        }
        
        // Make sure the partitions meet the minimum size denoted by postFilterMinSize.
        if cluster1.size > postFilterMinSize {
        //writeln("//////before clusterC2D///////// ");
        writeln("cluster1(",id,")"," with size: ", cluster1.size, " created!"," members: ", cluster1);
        calculateConductance(cluster1);
        
        var inPartition = cluster1;
        //var inPartition = kCoreDecomposition(cluster1, 2);

        //var inPartition = removeDegreeOne(cluster1);
          //var inPartition = clusterC2D(cluster1);

        writeln("cluster1(",id,")"," with size: ", inPartition.size);
        calculateConductance(inPartition);



          wccRecursiveChecker(inPartition, id, depth+1);
        }
        if cluster2.size > postFilterMinSize {
        writeln("cluster2(",id,")"," with size: ", cluster2.size, " created!"," members: ", cluster2);
        calculateConductance(cluster2);
        var outPartition =cluster2;
        //var outPartition = kCoreDecomposition(cluster2, 2);

        //var outPartition = removeDegreeOne(cluster2);
          //var outPartition = clusterC2D(cluster2);

        writeln("cluster2(",id,")"," with size: ", outPartition.size);
        calculateConductance(outPartition);
          wccRecursiveChecker(outPartition, id, depth+1);
        }
      }
      return;
    }

    /* Main executing function for well-connected components. */
    proc wcc(g1: SegGraph): int throws {
      var outMsg = "Graph loaded with " + g1.n_vertices:string + " vertices and " 
                 + g1.n_edges:string + " edges.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      var originalClusters = readClustersFile(inputcluster_filePath);
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),
                     "Reading clusters file finished.");

      var newClusterIds: chpl__processorAtomicType(int) = 0;
      var newClusters = new map(int, set(int));
      
      // NOTE: Sequential for now since connected components is highly parallel. We need to discuss
      //       the tradeoff if it is more important to run connected components on the original
      //       clusters in parallel or run connected components in parallel.
      //
      // NOTE: This is probably noy even needed here. We could add a pre-filtering step to run this
      //       during graph construction or as a totally separate process instead of here.
      
      // for key in originalClusters.keysToArray() {
      //   writeln("key: ",key,"originalClusters.size: ", originalClusters.size," cluster memebers: ", originalClusters);
      // }
      for key in originalClusters.keysToArray() {
        var (src, dst, mapper) = getEdgeList(originalClusters[key]);
        if src.size > 0 { // If no edges were generated, then do not process this component.
          // Call connected components and decide if multiple connected components exist or not.
          var components = connectedComponents(src, dst, mapper.size);
          var multipleComponents:bool = false;
          for c in components do if c != 0 { multipleComponents = true; break; }
          
          // Add each vertex in each connected component to its own cluster, or just add the whole
          // cluster if it is composed of only one connected component.
          if multipleComponents {
            var tempMap = new map(int, set(int));
            for (c,v) in zip(components,components.domain) { // NOTE: Could be parallel.
              if tempMap.contains(c) then tempMap[c].add(mapper[v]);
              else {
                var s = new set(int);
                s.add(mapper[v]);
                tempMap[c] = s;
              }
            }
            for c in tempMap.keys() { // NOTE: Could be parallel.
              var newId = newClusterIds.fetchAdd(1);
              if tempMap[c].size > preFilterMinSize {
                newClusters[newId] = tempMap[c];
                newClusterIdToOriginalClusterId[newId] = key;
              }
            }
            if logLevel == LogLevel.DEBUG {
              var outMsg = "Original cluster " + key:string + " was split up into " 
                        + tempMap.size:string + " clusters.";
              wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            }
          } else {
            if originalClusters[key].size > preFilterMinSize {
              var newId = newClusterIds.fetchAdd(1);
              newClusters[newId] = originalClusters[key];
              newClusterIdToOriginalClusterId[newId] = key;
            }
          }
        }
      }
      outMsg = "Splitting up clusters yielded " + newClusters.size:string + " new clusters.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      //forall key in newClusters.keysToArray() with (ref newClusters) {
      for key in newClusters.keysToArray() {
        ref clusterToAdd = newClusters[key];
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Processing cluster " + key:string + " which is a subcluster of " 
                    + newClusterIdToOriginalClusterId[key]:string + ".";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        writeln("-*-*-*-*-*-*-*-*-*-*at the beginning for cluster(",key,")"," and has ", clusterToAdd);
        calculateConductance(clusterToAdd);
        findBridgesInCluster(clusterToAdd);
        //findAllMinCutsInCluster(clusterToAdd);
        //testStoerWagner();
        runAllTests();
        //wccRecursiveChecker(clusterToAdd, key, 0);
      }
      if outputType == "post" then writeClustersToFile();
      
      outMsg = "WCC found " + globalId.read():string + " clusters to be well-connected.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      return globalId.read();
    } // end of wcc
    
    var numClusters = wcc(g1);
    return numClusters;
  } // end of runWCC
} // end of WellConnectedComponents module