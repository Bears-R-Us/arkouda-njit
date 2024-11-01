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

    /* K-core decomposition function optimized for shared memory

      This function computes the k-core decomposition of a cluster of nodes
      up to a specified maximum k (k_max). The k-core of a graph is a maximal
      subgraph in which each vertex has degree at least k.

      Parameters:
        clusterNodes: set(int) - the set of nodes in the cluster
        k_max: int - the maximum k value up to which to compute the k-core decomposition

      Returns:
        cores: array[int] of int - an array mapping each node to its core number
        cluster
    */
 proc kCoreDecomposition(ref clusterNodes: set(int), k_max: int) throws {
    writeln("/////////////////////////kCoreDecomposition///////////////////////");
    var clusterArr = clusterNodes.toArray();
    var coreKDomain: domain(int) = clusterArr;
    var degrees: [coreKDomain] int = 0;
    var cores: [coreKDomain] int = 0; // Initialize cores to 0

    // Initialize degrees
    writeln("Initializing degrees and cores...");
    for i in coreKDomain {
        degrees[i] = calculateClusterDegree(clusterNodes, i);
    }
    writeln("Initial degrees: ", degrees);
    writeln("Initial cores  : ", cores);

    // Initialize bins based on degree values
    var bins: [1..k_max] list(int);  // Bins for each degree from 1 to k_max
    var processed: set(int);  // Track nodes that have already been assigned a core

    for i in coreKDomain {
        const deg = degrees[i];
        if deg >= k_max then bins[k_max].pushBack(i);  // If degree >= k_max, put it in max bin
        else if deg > 0 then bins[deg].pushBack(i);    // Place in corresponding bin if degree > 0
    }
    writeln("Initial bins: ", bins);

    var k = 1;
    // Process bins iteratively
    while k <= k_max {
        writeln("\nIteration k = ", k);
        while !bins[k].isEmpty() {
            var v = bins[k].popBack();  // Remove a node with degree <= k
            if v in processed {
                continue;  // Skip if the node has already been processed
            }
            cores[v] = k;  // Assign core value to v
            processed.add(v);  // Mark the node as processed
            writeln("Processing[", v, "] in bins[", k, "]");

            // Process neighbors of v
            const ref neighbors = neighborsSetGraphG1[v];
            var adjacent = clusterNodes & neighbors;  // Filter neighbors within the cluster
            for u in adjacent {
                if cores[u] == 0 && u !in processed {  // Only update degrees if core not yet assigned
                    const oldDeg = degrees[u];
                    degrees[u] -= 1;  // Decrease degree
                    const newDeg = max(degrees[u], 1);  // Ensure non-negative

                    // Move u from old degree bin to new degree bin if needed
                    if oldDeg <= k_max then bins[oldDeg].remove(u);
                    if newDeg >= k_max {
                        bins[k_max].pushBack(u);
                    } else if !bins[newDeg].contains(u) {
                        bins[newDeg].pushBack(u);
                    }

                    writeln("Updated degree of neighbor ", u, " to ", degrees[u]);
                    writeln(" bins are: ", bins);
                }
            }
        }
        writeln("End of iteration k = ", k, ", bins are: ", bins);

        k += 1;
    }

    // Collect nodes with cores >= k_max for output
    var outSet: set(int);
    for elem in coreKDomain {
        if cores[elem] >= k_max then outSet.add(elem);  
    }
    writeln("outSet: ", outSet);
    writeln("/////////////////////////kCoreDecomposition ENDED!///////////////////////");

    return outSet;
} // end of kCoreDecomposition


    //   var clusterArr = clusterNodes.toArray();
    //   var coreKDomain: domain(int) = clusterArr;
    //   var degrees: [coreKDomain] int = 0;
    //   var cores: [coreKDomain] int = 0; // Initialize cores to 0

    //   // Initialize degrees and cores
    //   writeln("Initializing degrees and cores...");
    //   for i in coreKDomain {
    //     degrees[i] = calculateClusterDegree(clusterNodes, i);
    //   }
    //   writeln("clusterArr     : ", clusterArr);
    //   writeln("Initial degrees: ", degrees);
    //   writeln("Initial cores  : ", cores);

    //   // Create a list for vertices to process
    //   var vertexList = new list(int);

    //   // Initialize the list with all vertices in the cluster
    //   writeln("Initializing vertex list...");
    //   for i in 0..<clusterNodes.size {
    //     vertexList.pushBack(clusterArr[i]);
    //   }
    //   writeln("Initial vertex list: ", vertexList);
    //   var k = 1;

    //   // Boolean array to track if a node has been added to nextList
    //   //var maxVertexID = clusterArr.reduce((a, b) => max(a, b));
    //   //var inNextList: [0..maxVertexID] bool = false; // Initialize to false

    //   // Loop until the vertex list is empty or k exceeds k_max
    //   while !vertexList.isEmpty() && k < k_max {

    //     writeln("\nProcessing k = ", k);
    //     var nextList = new list(int);

    //     // Process vertices sequentially to avoid race conditions
    //     while !vertexList.isEmpty() {
    //       var v = vertexList.popBack();

    //       // **Check if the node has already been assigned a core**
    //       if cores[v] == 0 {
    //         writeln("Processing vertex v = ", v, " with degree ", degrees[v]);

    //         if degrees[v] <= k {
    //           // Assign core number k to vertex v
    //           //cores[v] = k;
    //           cores[v] = degrees[v];
    //           writeln("Assigned core[", v, "] = ", k);

    //           // Decrease the degree of neighbors in the cluster
    //           const ref neighbors = neighborsSetGraphG1[v];
    //           var adjacent = clusterNodes & neighbors;
    //           writeln("Neighbors of ", v, ": ", adjacent);

    //           for u in adjacent {
    //             // **Only decrease the degree if the neighbor hasn't been assigned a core**
    //             if cores[u] == 0 {
    //               degrees[u] -= 1;  // Update degrees of neighbor u
    //               writeln("Decreased degree of neighbor ", u, " to ", degrees[u]);

    //               if degrees[u] <= k {
    //                 // **Avoid adding duplicates to nextList**
    //                 if !nextList.contains(u) {
    //                   nextList.pushBack(u);
    //                   writeln("Added neighbor ", u, " to nextList");
    //                 }
    //               }
    //             }
    //           }
    //         } else {
    //           // Keep vertex v in the list to be processed in the next iteration
    //           nextList.pushBack(v);
    //           writeln("Vertex ", v, " degree ", degrees[v], " > ", k, ", added back to nextList");
    //         }
    //       } else {
    //         // Node v has already been assigned a core
    //         writeln("Vertex ", v, " has already been assigned core ", cores[v], ", skipping");
    //       }
    //     }

    //     // Swap lists for the next iteration
    //     vertexList = nextList;
    //     writeln("End of iteration k = ", k);
    //     writeln("Next vertex list: ", vertexList);
    //     writeln("\nFinal cores: ", cores);
    //     k += 1;
    //     writeln("k became = ",k);

    //   }

    //   writeln("\nFinal cores: ", cores);
    //   var outSet: set(int);
    //   for elem in coreKDomain{
    //     if cores[elem] >= k_max then outSet.add(elem);  
    //   }
    //   writeln("outSet: ", outSet);
    //   writeln("/////////////////////////kCoreDecomposition ENDED!///////////////////////");

    //   return outSet;
    // } // end of kCoreDecomposition

        

    /* Function to calculate the conductance of a cluster */
    proc calculateConductance(ref cluster: set(int)) throws {
      var cutSizePrevios: int = totalVolume;
      var SumOutEdges: int = 0;
      var volumeCluster: int = 0;
      var volumeComplement: int = 0;
      var minDegreeCluster: int = g1.n_edges;  // 

      // Iterate through all vertices to calculate volumes, cutSize, and total graph volume
      for v in cluster {
        var neighbors = neighborsSetGraphG1[v];
        volumeCluster += neighbors.size;
        var outEdge = neighbors - cluster;
        //writeln("outEdge: ", outEdge);
        SumOutEdges += outEdge.size;
        cutSizePrevios = if outEdge.size < cutSizePrevios &&  outEdge.size > 0 then outEdge.size else cutSizePrevios;
        minDegreeCluster = if neighbors.size < minDegreeCluster then neighbors.size else minDegreeCluster;
      }

      volumeComplement = totalVolume - volumeCluster;

      writeln("*****************calculateConductance called***********************");


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
      // writeln("volumeCluster: ", volumeCluster);
      // writeln("volumeComplement: ", volumeComplement);
      // Output intermediate calculations for verification
      writeln("Estimated Previos cutsize greater than: ", cutSizePrevios);
      // writeln("Cluster SumOutEdges : ", SumOutEdges);
      // writeln("Cluster mean degree: ", meanDegreeCluster);
      writeln("Cluster minimum degree: ", minDegreeCluster);
      return output;
    }
  

    /* Recursive method that processes a given set of vertices (partition), denotes if it is 
       well-connected or not, and if not calls itself on the new generated partitions. */
    proc wccRecursiveChecker(ref vertices: set(int), id: int, depth: int) throws {
      writeln("*****************wccRecursiveChecker called***********************");

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
      writeln("$$$$$$clster ",id,"with currentId " ,currentId,"at depth ", depth," with cut", cut, " is well Connected.");
      writeln("memebers are: ", vertices);

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
          writeln("//////before clusterC2D///////// ");
        writeln("cluster1(",id,")"," with size: ", cluster1.size, " created!"," members: ", cluster1);
        calculateConductance(cluster1);
        
        var inPartition = kCoreDecomposition(cluster1, 2);

          //var inPartition = removeDegreeOne(cluster1);
          //var inPartition = clusterC2D(cluster1);
         writeln("//////After clusterC2D///////// ");

        writeln("cluster1(",id,")"," with size: ", inPartition.size);
        calculateConductance(inPartition);



          wccRecursiveChecker(inPartition, id, depth+1);
        }
        if cluster2.size > postFilterMinSize {
          writeln("//////before clusterC2D///////// ");
        writeln("cluster2(",id,")"," with size: ", cluster2.size, " created!"," members: ", cluster2);
        calculateConductance(cluster2);
        var outPartition = kCoreDecomposition(cluster2, 2);

          //var outPartition = removeDegreeOne(cluster2);
          //var outPartition = clusterC2D(cluster2);
                    //kCoreDecomposition(cluster2);

                   writeln("//////After clusterC2D///////// ");

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
        wccRecursiveChecker(clusterToAdd, key, 0);
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