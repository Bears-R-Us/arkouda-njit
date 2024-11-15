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
  use Heap;
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

    /* Helper function to print graph */
    proc printGraph(members: set(int), adj: map(int, set(int))) throws {
        writeln("Graph:");
        writeln("Vertices: ", members);
        writeln("Edges:");
        for v in members {
            for u in adj[v] {
                if v < u then writeln(v, " -- ", u);
            }
        }
    }
    /* Main Stoer-Wagner implementation */
    proc stoerWagnerMinCut(ref members: set(int), ref adj: map(int, set(int))): (int, set(int), set((int, int))) throws {
        // Special cases
        if members.size == 0 || members.size == 1 {
            return (0, new set(int), new set((int, int)));
        }
        
        var minCutValue = max(int);
        var minCutSet = new set(int);
        var minCutEdges = new set((int, int));

        // Deep copy the adjacency lists
        var adjCopy = new map(int, set(int));
        for v in adj.keys() {
            adjCopy[v] = new set(int);
            adjCopy[v] = adj[v];
        }

        // Keep track of merged vertices
        var mergeMap = new map(int, set(int));
        for v in members {
            mergeMap[v] = new set(int);
            mergeMap[v].add(v);
        }

        // Working set of vertices
        var vertices = new set(int);
        vertices = members;

        writeln("Starting Stoer-Wagner with vertices: ", vertices);
        //writeln("Initial adjacency lists:");
        // for v in adjCopy.keys() {
        //     writeln(v, " -> ", adjCopy[v]);
        // }

        // Main algorithm loop
        while vertices.size > 1 {
            var inA = new set(int);
            var weights = new map(int, int);
            
            // Select first active vertex
            var first = -1;
            for v in vertices {
                first = v;
                break;
            }

            var prev = -1;
            var last = first;
            
            inA.add(first);
            //writeln("\nNew phase starting with first vertex: ", first);

            // Initialize weights
            for v in vertices {
                if v != first {
                    weights[v] = 0;
                    if adjCopy[first].contains(v) {
                        weights[v] = 1;
                    }
                }
            }
            //writeln("Initial weights: ", weights);

            // Main phase loop
            while inA.size < vertices.size {
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

                prev = last;
                last = maxVertex;
                inA.add(maxVertex);

                //writeln("Added vertex ", maxVertex, " with weight ", maxWeight);
                
                // Update weights
                for v in vertices {
                    if !inA.contains(v) {
                        if adjCopy[maxVertex].contains(v) {
                            weights[v] += 1;
                        }
                    }
                }
                //writeln("Updated weights: ", weights);
            }

            // Build cut set
            var cutSet = new set(int);
            for v in vertices {
                if v != last {
                    cutSet.add(v);
                }
            }

            // Calculate cut weight
            var cutWeight = 0;
            var currentCutEdges = new set((int, int));
            var lastVertices = mergeMap[last];
            var cutSetVertices = new set(int);
            for v in cutSet {
                cutSetVertices |= mergeMap[v];
            }

            // Count edges crossing the cut
            for v in cutSetVertices {
                for u in lastVertices {
                    if adj[v].contains(u) {
                        cutWeight += 1;
                        currentCutEdges.add((min(v,u), max(v,u)));
                    }
                }
            }

            // writeln("\nPhase complete.");
            // writeln("Cut weight: ", cutWeight, ", previous min: ", minCutValue);
            // writeln("Cut set: ", cutSet);

            // Update minimum cut if better
            if cutWeight < minCutValue {
                minCutValue = cutWeight;
                minCutSet.clear();
                minCutSet |= cutSetVertices;
                minCutEdges = currentCutEdges;

                // writeln("\nNew minimum cut found!");
                // writeln("Cut value: ", minCutValue);
                // writeln("Cut set: ", minCutSet);
                // writeln("Cut edges: ", minCutEdges);
            }
            // Merge vertices
            if prev != -1 && last != -1 && prev != last {
                // writeln("\nMerging vertex ", last, " into ", prev);
                // writeln("Before merge adjacency lists:");
                // for v in adjCopy.keys() {
                //     writeln(v, " -> ", adjCopy[v]);
                // }
                
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

                // writeln("\nAfter merge:");
                // writeln("Vertices remaining: ", vertices);
                // writeln("Updated adjacency lists:");
                // for v in adjCopy.keys() {
                //     writeln(v, " -> ", adjCopy[v]);
                // }
                // writeln("Merge map:", mergeMap);
            }
        }

        writeln("\nStoer-Wagner MinCut Final result:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Cut set: ", minCutSet);
        writeln("Cut edges: ", minCutEdges);

        return (minCutValue, minCutSet, minCutEdges);
    }
/////////////////////////////////////////Nagamochi-Ibaraki Algorithm//////////////////////////
/* Graph representation using optimized data structures for shared memory */
record Graph {
    var numVertices: int;
    var vertexDomain: domain(1);
    var edgeDomain: domain(2*int);  // Stores edges as (v1,v2) where v1 < v2
    var adjList: [vertexDomain] list(int);  // Adjacency lists using Chapel lists
    var degree: [vertexDomain] int;         // Track degree of each vertex

    /* Initialize a graph with n vertices */
    proc init(n: int) {
        this.numVertices = n;
        this.vertexDomain = {1..n};
        // Note: edgeDomain starts empty and grows as edges are added
    }

    /* Add an undirected edge between vertices v1 and v2 */
    proc addEdge(v1: int, v2: int) {
        if v1 == v2 then return;  // No self-loops
        
        // Ensure v1 < v2 for consistent edge representation
        var (minV, maxV) = if v1 < v2 then (v1, v2) else (v2, v1);
        
        // Add to edge domain if not already present
        if !edgeDomain.contains((minV, maxV)) {
            edgeDomain += (minV, maxV);
            adjList[minV].append(maxV);
            adjList[maxV].append(minV);
            degree[minV] += 1;
            degree[maxV] += 1;
        }
    }

    /* Check if edge exists between vertices v1 and v2 */
    proc hasEdge(v1: int, v2: int): bool {
        var (minV, maxV) = if v1 < v2 then (v1, v2) else (v2, v1);
        return edgeDomain.contains((minV, maxV));
    }

    /* Get all neighbors of a vertex */
    proc neighbors(v: int): list(int) {
        return adjList[v];
    }

    /* Get number of edges */
    proc numEdges(): int {
        return edgeDomain.size;
    }

    /* Print graph statistics */
    proc printStats() {
        writeln("Graph Statistics:");
        writeln("  Vertices: ", numVertices);
        writeln("  Edges: ", numEdges());
        writeln("  Maximum degree: ", max reduce degree);
        writeln("  Average degree: ", (+ reduce degree):real / numVertices:real);
    }
}
/* Cut representation for storing minimum cuts with ratio information */
record Cut {
    var vertices: domain(1);    // Vertices in the cut set
    var edges: domain(2*int);   // Cut edges
    var value: int;             // Cut value
    var ratio: real;            // Ratio of smaller part to total vertices
    var totalVertices: int;     // Total number of vertices in graph

    /* Initialize an empty cut */
    proc init(numVertices: int) {
        this.value = 0;
        this.ratio = 0.0;
        this.totalVertices = numVertices;
    }

    /* Add a vertex to the cut set */
    proc addVertex(v: int) {
        vertices += v;
        updateRatio();
    }

    /* Add an edge to the cut */
    proc addEdge(v1: int, v2: int) {
        var (minV, maxV) = if v1 < v2 then (v1, v2) else (v2, v1);
        edges += (minV, maxV);
        value += 1;  // For unweighted graphs
    }

    /* Update ratio after changes to vertex set */
    proc updateRatio() {
        var setSize = vertices.size;
        var complementSize = totalVertices - setSize;
        // Ratio is always the size of smaller set / total vertices
        ratio = min(setSize:real / totalVertices:real, 
                   complementSize:real / totalVertices:real);
    }

    /* Check if vertex is in cut set */
    proc contains(v: int): bool {
        return vertices.contains(v);
    }

    /* Get difference from target ratio */
    proc getRatioDifference(targetRatio: real): real {
        return abs(ratio - targetRatio);
    }

    /* Get the complement of current cut set */
    proc getComplement(): domain(1) {
        var complement: domain(1) = {1..totalVertices};
        for v in vertices do
            complement -= v;
        return complement;
    }

    /* Print cut information */
    proc printInfo() {
        writeln("Cut Information:");
        writeln("  Vertices in cut: ", vertices);
        writeln("  Complement: ", getComplement());
        writeln("  Cut value: ", value);
        writeln("  Cut ratio: ", ratio);
        writeln("  Cut edges: ", edges);
    }
}

/* Container for storing multiple cuts with ratio considerations */
record CutSet {
    var cuts: list(Cut);
    var minCutValue: int = max(int);
    var targetRatio: real = -1.0;  // -1.0 means no target ratio
    var bestRatioDiff: real = max(real);

    /* Initialize cut set with optional target ratio */
    proc init(ratio: real = -1.0) {
        this.targetRatio = ratio;
    }

    /* Add a new cut considering both value and ratio */
    proc addCut(newCut: Cut) {
        if targetRatio < 0.0 {
            // No target ratio, just consider cut value
            if newCut.value < minCutValue {
                minCutValue = newCut.value;
                cuts.clear();
                cuts.append(newCut);
            } else if newCut.value == minCutValue {
                cuts.append(newCut);
            }
        } else {
            // Consider both cut value and ratio
            var ratioDiff = newCut.getRatioDifference(targetRatio);
            
            if newCut.value < minCutValue {
                // New minimum cut value, reset everything
                minCutValue = newCut.value;
                bestRatioDiff = ratioDiff;
                cuts.clear();
                cuts.append(newCut);
            } else if newCut.value == minCutValue {
                if abs(ratioDiff - bestRatioDiff) < 1e-10 {
                    // Same cut value and ratio, add to list
                    cuts.append(newCut);
                } else if ratioDiff < bestRatioDiff {
                    // Better ratio for same cut value
                    bestRatioDiff = ratioDiff;
                    cuts.clear();
                    cuts.append(newCut);
                }
            }
        }
    }

    /* Get the cuts closest to target ratio */
    proc getBestRatioCuts(): list(Cut) {
        if targetRatio < 0.0 || cuts.size <= 1 then
            return cuts;

        var bestCuts: list(Cut);
        var bestDiff = max(real);

        // Find best ratio among existing cuts
        for cut in cuts {
            var diff = cut.getRatioDifference(targetRatio);
            if diff < bestDiff {
                bestDiff = diff;
                bestCuts.clear();
                bestCuts.append(cut);
            } else if abs(diff - bestDiff) < 1e-10 {
                bestCuts.append(cut);
            }
        }

        return bestCuts;
    }

    /* Get number of minimum cuts found */
    proc size(): int {
        return cuts.size;
    }

    /* Print all cuts with their ratios */
    proc printCuts() {
        writeln("Found ", cuts.size, " minimum cuts with value ", minCutValue);
        if targetRatio >= 0.0 then
            writeln("Target ratio: ", targetRatio, ", Best achieved difference: ", bestRatioDiff);
        
        for cut in cuts {
            cut.printInfo();
            writeln("---");
        }
    }
}
/* Performs maximum adjacency search to find an ordering of vertices.
   Takes a graph represented by vertices and adjacency lists, and a starting vertex.
   Returns a tuple containing:
   1. The vertex ordering (important for finding minimum cuts)
   2. A parent map showing how vertices are connected in the resulting forest
   
   Key operations:
   - Computes and maintains attachment numbers for vertices
   - Selects vertices based on maximum attachment numbers
   - Builds a forest structure through parent relationships
   
   Parameters:
   - vertices: set of all vertices in the graph
   - adj: map of adjacency lists for each vertex
   - weights: map of edge weights (tuple of vertices -> weight)
   - startVertex: the vertex to start the search from
*/
proc scanningPhase(
    const ref graph: Graph,    // Now using Graph record
    startVertex: int
): (list(int), [graph.vertexDomain] int) throws {
    writeln("\n=== Starting scanning phase from vertex ", startVertex, " ===");
    
    var ordering = new list(int);
    var inS: [graph.vertexDomain] bool = false;     // Using array instead of set
    var d: [graph.vertexDomain] int = 0;            // Using array instead of map
    var parent: [graph.vertexDomain] int = -1;      // Using array instead of map
    
    // Add start vertex
    inS[startVertex] = true;
    ordering.append(startVertex);
    
    writeln("Initial attachment numbers for neighbors of ", startVertex, ":");
    for neighbor in graph.neighbors(startVertex) {
        // In unweighted graph, all attachments start at 1
        d[neighbor] = 1;
        writeln("  d[", neighbor, "] = ", d[neighbor]);
    }

    while ordering.size < graph.numVertices {
        var maxVertex = -1;
        var maxD = -1;
        
        // Find vertex not in S with maximum attachment number
        for v in graph.vertexDomain {
            if !inS[v] && d[v] > maxD {
                maxVertex = v;
                maxD = d[v];
            }
        }
        
        if maxVertex == -1 {
            for v in graph.vertexDomain {
                if !inS[v] {
                    maxVertex = v;
                    break;
                }
            }
        }
        
        writeln("Selected vertex ", maxVertex, " with attachment number ", d[maxVertex]);

        // Find parent with maximum weight connection
        var maxNeighbor = -1;
        var maxWeight = -1;
        for neighbor in graph.neighbors(maxVertex) {
            if inS[neighbor] {
                // In unweighted graph, all weights are 1
                if maxNeighbor == -1 || d[neighbor] > maxWeight {
                    maxWeight = d[neighbor];
                    maxNeighbor = neighbor;
                }
            }
        }
        parent[maxVertex] = maxNeighbor;
        writeln("Parent of ", maxVertex, " is ", maxNeighbor);

        inS[maxVertex] = true;
        ordering.append(maxVertex);

        writeln("Updating attachment numbers:");
        for neighbor in graph.neighbors(maxVertex) {
            if !inS[neighbor] {
                var oldD = d[neighbor];
                d[neighbor] += 1;  // Unweighted graph
                writeln("  d[", neighbor, "] updated from ", oldD, " to ", d[neighbor]);
            }
        }
    }

    writeln("Final ordering: ", ordering);
    return (ordering, parent);
}

/* Builds a k-edge-connected certificate of the input graph.
   This is a sparse subgraph that preserves all cuts up to size k.
   
   Key operations:
   - Performs k scanning phases from different start vertices
   - Combines the resulting forests into a certificate
   - Preserves minimum cuts while potentially reducing graph density
   
   Parameters:
   - vertices: set of all vertices in the graph
   - adj: map of adjacency lists for each vertex
   - weights: map of edge weights
   - k: connectivity parameter (usually set to the minimum cut value)
   
   Returns:
   - Tuple containing the certificate's adjacency lists and edge weights
*/
proc buildCertificate(
    const ref graph: Graph,
    k: int
): Graph throws {
    writeln("\n=== Building certificate with k = ", k, " ===");
    
    var certGraph = new Graph(graph.numVertices);
    
    writeln("Performing ", k, " scanning phases");
    
    for i in 1..k {
        var startVertex = ((i - 1) % graph.numVertices) + 1;
        writeln("\nPhase ", i, " starting from vertex ", startVertex);
        
        var (ordering, parent) = scanningPhase(graph, startVertex);

        // Add forest edges to certificate
        for v in graph.vertexDomain {
            if parent[v] != -1 {
                certGraph.addEdge(v, parent[v]);
                writeln("Added edge ", v, " -- ", parent[v], " to certificate");
            }
        }
    }

    writeln("\nCertificate construction complete");
    writeln("Certificate edges:");
    for v in certGraph.vertexDomain {
        writeln(v, " -> ", certGraph.neighbors(v));
    }

    return certGraph;
}

/* Finds all minimum cuts in an undirected graph using the Nagamochi-Ibaraki algorithm.
   Optionally finds balanced minimum cuts if a balance ratio is provided.
   
   Key operations:
   - Performs scanning phases from each vertex
   - Identifies all minimum cuts and their cut edges
   - If balance ratio provided, filters cuts based on partition sizes
   - Handles complementary cuts appropriately
   
   Parameters:
   - vertices: set of all vertices in the graph
   - adj: map of adjacency lists for each vertex
   - balanceRatio: (optional) desired ratio between partition sizes (0 to 1)
   
   Returns:
   - Tuple containing:
     1. Global minimum cut value
     2. List of minimum cuts (each cut is a tuple of cut set and cut edges)
*/
proc findAllMinCutsNI(
    const ref graph: Graph,
    balanceRatio: real = -1.0
): (int, CutSet) throws {
    writeln("\n=== Starting Nagamochi-Ibaraki algorithm ===");
    if balanceRatio > 0.0 then
        writeln("Target balance ratio: ", balanceRatio);
    
    var cutSet = new CutSet(balanceRatio);
    var globalMinValue = max(int);
    
    writeln("\nFinding minimum cuts:");
    for startVertex in graph.vertexDomain {
        var (ordering, _) = scanningPhase(graph, startVertex);
        writeln("\nProcessing ordering: ", ordering);
        
        // Process all prefixes
        var currentCut = new Cut(graph.numVertices);
        
        for idx in 0..(ordering.size - 2) {
            var v = ordering[idx];
            currentCut.addVertex(v);
            
            // Calculate cut edges
            var cutEdges = new set((int, int));
            var cutWeight = 0;
            for u in currentCut.vertices {
                for neighbor in graph.neighbors(u) {
                    if !currentCut.contains(neighbor) {
                        var edge = if u < neighbor then (u, neighbor) else (neighbor, u);
                        if !cutEdges.contains(edge) {
                            cutEdges.add(edge);
                            cutWeight += 1;  // Unweighted graph
                        }
                    }
                }
            }
            
            // Create new cut with the calculated values
            var newCut = new Cut(graph.numVertices);
            for v in currentCut.vertices do newCut.addVertex(v);
            for e in cutEdges do newCut.addEdge(e[1], e[2]);
            
            writeln("Cut value for set ", newCut.vertices, " is ", cutWeight,
                   " (ratio: ", newCut.ratio, ")");

            // Update cuts based on minimum value and ratio
            if cutWeight <= globalMinValue {
                if cutWeight < globalMinValue {
                    writeln("New minimum cut value found: ", cutWeight);
                    globalMinValue = newCut.value;
                    cutSet = new CutSet(balanceRatio);
                }
                cutSet.addCut(newCut);
                writeln("Added cut: ", newCut.vertices, " with edges ", newCut.edges);
            }
        }
    }

    writeln("\nGlobal minimum cut value: ", globalMinValue);
    
    return (globalMinValue, cutSet);
}
/* Comprehensive test suite for the Nagamochi-Ibaraki algorithm implementation.
   Tests various graph types and algorithm features.
*/
proc testNagamochiIbaraki() throws {
    writeln("===================== Testing Nagamochi-Ibaraki Algorithm =====================\n");

    // Test 1: Simple cycle graph (4 vertices)
    {
        writeln("===========Test 1: Simple cycle graph (4 vertices)");
        
        var vertices = new set(int);
        var adj = new map(int, set(int));
        
        // Add vertices
        for i in 1..4 do vertices.add(i);
        
        // Initialize adjacency lists
        for v in vertices do adj[v] = new set(int);
        
        // Add edges for cycle: 1-2-3-4-1
        adj[1].add(2); adj[2].add(1);
        adj[2].add(3); adj[3].add(2);
        adj[3].add(4); adj[4].add(3);
        adj[4].add(1); adj[1].add(4);

        writeln("Original graph:");
        writeln("Graph:");
        writeln("Vertices: ", vertices);
        writeln("Edges:");
        var printed = new set((int, int));
        for v in vertices {
            for u in adj[v] {
                var edge = if v < u then (v, u) else (u, v);
                if !printed.contains(edge) {
                    writeln(v, " -- ", u);
                    printed.add(edge);
                }
            }
        }

        // Test without ratio
        var (minCutValue, cuts) = findAllMinCutsNI(vertices, adj);
        writeln("\nResults for cycle graph:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Expected value: 2");

        // Test with different ratios
        var ratios = [0.5, 0.25, 0.75];
        for ratio in ratios {
            writeln("\nTesting cycle graph with balance ratio: ", ratio);
            var (balancedMinCutValue, balancedCuts) = findAllMinCutsNI(vertices, adj, ratio);
        }
    }

    // Test 2: Path graph (4 vertices)
    {
        writeln("===========Test 2: Path graph (4 vertices)");
        
        var vertices = new set(int);
        var adj = new map(int, set(int));
        
        // Add vertices
        for i in 1..4 do vertices.add(i);
        
        // Initialize adjacency lists
        for v in vertices do adj[v] = new set(int);
        
        // Add edges for path: 1-2-3-4
        adj[1].add(2); adj[2].add(1);
        adj[2].add(3); adj[3].add(2);
        adj[3].add(4); adj[4].add(3);

        writeln("Original graph:");
        writeln("Graph:");
        writeln("Vertices: ", vertices);
        writeln("Edges:");
        var printed = new set((int, int));
        for v in vertices {
            for u in adj[v] {
                var edge = if v < u then (v, u) else (u, v);
                if !printed.contains(edge) {
                    writeln(v, " -- ", u);
                    printed.add(edge);
                }
            }
        }

        var (minCutValue, cuts) = findAllMinCutsNI(vertices, adj);
        
        writeln("\nResults for path graph:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Expected value: 1\n");
    }

    // Test 3: Complete graph (4 vertices)
    {
        writeln("===========Test 3: Complete graph (4 vertices)");
        
        var vertices = new set(int);
        var adj = new map(int, set(int));
        
        // Add vertices
        for i in 1..4 do vertices.add(i);
        
        // Initialize adjacency lists
        for v in vertices do adj[v] = new set(int);
        
        // Add all possible edges
        for i in 1..4 {
            for j in i+1..4 {
                adj[i].add(j);
                adj[j].add(i);
            }
        }

        writeln("Original graph:");
        writeln("Graph:");
        writeln("Vertices: ", vertices);
        writeln("Edges:");
        var printed = new set((int, int));
        for v in vertices {
            for u in adj[v] {
                var edge = if v < u then (v, u) else (u, v);
                if !printed.contains(edge) {
                    writeln(v, " -- ", u);
                    printed.add(edge);
                }
            }
        }

        var (minCutValue, cuts) = findAllMinCutsNI(vertices, adj);
        
        writeln("\nResults for complete graph:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Expected value: 3\n");
    }

    // Test 4: Star graph (center vertex 1, 4 vertices total)
    {
        writeln("===========Test 4: Star graph (4 vertices)");
        
        var vertices = new set(int);
        var adj = new map(int, set(int));
        
        // Add vertices
        for i in 1..4 do vertices.add(i);
        
        // Initialize adjacency lists
        for v in vertices do adj[v] = new set(int);
        
        // Add edges from center (vertex 1) to all others
        for i in 2..4 {
            adj[1].add(i);
            adj[i].add(1);
        }

        writeln("Original graph:");
        writeln("Graph:");
        writeln("Vertices: ", vertices);
        writeln("Edges:");
        var printed = new set((int, int));
        for v in vertices {
            for u in adj[v] {
                var edge = if v < u then (v, u) else (u, v);
                if !printed.contains(edge) {
                    writeln(v, " -- ", u);
                    printed.add(edge);
                }
            }
        }

        var (minCutValue, cuts) = findAllMinCutsNI(vertices, adj);
        
        writeln("\nResults for star graph:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Expected value: 1\n");
    }

    // Test 5: Disconnected graph (two components)
    {
        writeln("===========Test 5: Disconnected graph (4 vertices, two components)");
        
        var vertices = new set(int);
        var adj = new map(int, set(int));
        
        // Add vertices
        for i in 1..4 do vertices.add(i);
        
        // Initialize adjacency lists
        for v in vertices do adj[v] = new set(int);
        
        // Add edges: 1-2 and 3-4 (two separate components)
        adj[1].add(2); adj[2].add(1);
        adj[3].add(4); adj[4].add(3);

        writeln("Original graph:");
        writeln("Graph:");
        writeln("Vertices: ", vertices);
        writeln("Edges:");
        var printed = new set((int, int));
        for v in vertices {
            for u in adj[v] {
                var edge = if v < u then (v, u) else (u, v);
                if !printed.contains(edge) {
                    writeln(v, " -- ", u);
                    printed.add(edge);
                }
            }
        }

        var (minCutValue, cuts) = findAllMinCutsNI(vertices, adj);
        
        writeln("\nResults for disconnected graph:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Expected value: 0\n");
    }
// Test 6: Bridge graph (new test)
    {
        writeln("\nTest 6: Bridge graph");
        
        var vertices = new set(int);
        var adj = new map(int, set(int));
        
        // Add vertices
        for i in 1..6 do vertices.add(i);
        
        // Initialize adjacency lists
        for v in vertices do adj[v] = new set(int);
        
        // Add edges to create two triangles connected by a bridge
        // Triangle 1: 1-2-3-1
        adj[1].add(2); adj[2].add(1);
        adj[2].add(3); adj[3].add(2);
        adj[3].add(1); adj[1].add(3);
        
        // Triangle 2: 4-5-6-4
        adj[4].add(5); adj[5].add(4);
        adj[5].add(6); adj[6].add(5);
        adj[6].add(4); adj[4].add(6);
        
        // Bridge: 3-4
        adj[3].add(4); adj[4].add(3);

        writeln("Original graph:");
        writeln("Graph:");
        writeln("Vertices: ", vertices);
        writeln("Edges:");
        var printed = new set((int, int));
        for v in vertices {
            for u in adj[v] {
                var edge = if v < u then (v, u) else (u, v);
                if !printed.contains(edge) {
                    writeln(v, " -- ", u);
                    printed.add(edge);
                }
            }
        }

        // Test without ratio
        var (minCutValue, cuts) = findAllMinCutsNI(vertices, adj);
        writeln("\nResults for bridge graph:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Expected value: 1");  // Bridge should give min cut of 1

        // Test with balanced ratio
        var (balancedMinCutValue, balancedCuts) = findAllMinCutsNI(vertices, adj, 0.5);
        writeln("\nResults for bridge graph with balanced cuts (ratio 0.5):");
        writeln("Minimum cut value: ", balancedMinCutValue);
    }

    // Test 7: Multiple bridges graph (new test)
    {
        writeln("\nTest 7: Multiple bridges graph");
        
        var vertices = new set(int);
        var adj = new map(int, set(int));
        
        // Add vertices
        for i in 1..8 do vertices.add(i);
        
        // Initialize adjacency lists
        for v in vertices do adj[v] = new set(int);
        
        // Create a graph with multiple bridges
        // Component 1: 1-2
        adj[1].add(2); adj[2].add(1);
        
        // Bridge 1: 2-3
        adj[2].add(3); adj[3].add(2);
        
        // Component 2: 3-4-5
        adj[3].add(4); adj[4].add(3);
        adj[4].add(5); adj[5].add(4);
        
        // Bridge 2: 5-6
        adj[5].add(6); adj[6].add(5);
        
        // Component 3: 6-7-8
        adj[6].add(7); adj[7].add(6);
        adj[7].add(8); adj[8].add(7);

        writeln("Original graph:");
        writeln("Graph:");
        writeln("Vertices: ", vertices);
        writeln("Edges:");
        var printed = new set((int, int));
        for v in vertices {
            for u in adj[v] {
                var edge = if v < u then (v, u) else (u, v);
                if !printed.contains(edge) {
                    writeln(v, " -- ", u);
                    printed.add(edge);
                }
            }
        }

        // Test without ratio
        var (minCutValue, cuts) = findAllMinCutsNI(vertices, adj);
        writeln("\nResults for multiple bridges graph:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Expected value: 1");  // Bridges should give min cut of 1

        // Test with different ratios
        var ratios = [0.5, 0.33, 0.66];
        for ratio in ratios {
            writeln("\nTesting multiple bridges graph with balance ratio: ", ratio);
            var (balancedMinCutValue, balancedCuts) = findAllMinCutsNI(vertices, adj, ratio);
        }
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
        //runAllTests();
        //testWeightedStoerWagner();
        //testStoerWagner();
        //if key == 0 then testStoerWagner();
        if key == 0{
          writeln("we are here");
          testNagamochiIbaraki();
        }
        
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