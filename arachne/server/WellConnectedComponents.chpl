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

  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string, outputType: string) throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG1 = toSymEntry(g1.getComp("NEIGHBORS_SET_SDI"), set(int)).a;
    
    var finalVertices = new list(int, parSafe=true);
    var finalClusters = new list(int, parSafe=true);
    var globalId:atomic int = 0;

    var clusterArrtemp = wcc(g1);
    const ref clusterArr = clusterArrtemp; // TODO: Is this needed?
    
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
            var outMsg = "Vertex not found in the graph: " + originalNode:string;
            wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          }
        }
      }
      reader.close();
      file.close();
      var outMsg = "Number of clusters originall found in file: " + clusters.size:string;
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      return clusters;
    }

    /* Returns the edge list of the induced subgraph given a set of vertices. */
    proc getEdgeList(ref vertices: set(int)) throws {
      var srcList = new list(int, parSafe=true);
      var dstList = new list(int, parSafe=true);

      // Map to assign new indices to vertices. 
      var mapper = new map(int, int);
      var reverseMapper = new map(int, int);
      var idx = 0;
      // TODO: This seems like a lot of work. Would it be easier to just sort vertices? Once sorted
      //       we automatically get reverseMapper and then we just have to populate mapper.
      for v in vertices {
        mapper[v] = idx;
        reverseMapper[idx] = v;
        idx += 1;
      }

      // Gather the edges of the subgraph induced by the given vertices.
      for u in vertices {
        const ref neighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];
        for v in neighbors {
          if mapper.contains(v) {
            srcList.pushBack(mapper[u]);
            dstList.pushBack(mapper[v]);
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

      // Create mapper array. This holds the new index values mapped to the original vertex ids.
      var n = mapper.size;
      var mapperArray:[{0..<n}] int;
      for i in reverseMapper.keysToArray() {
        var originalV = reverseMapper[i];
        mapperArray[i] = originalV;
      }

      return (uniqueSrc, uniqueDst, mapperArray);
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
        sortedSrc[i]= edges[i][0];
        sortedDst[i]= edges[i][1];
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
      const ref neighbors1 = neighborsSetGraphG1[vertex];
      return setIntersectionSize(neighbors1,members);
    }

    /* Uses the vertices confirmed to be a well-connected cluster subgraph to write out debugging
       information per-cluster during execution of WCC. */
    proc writeClustersToFile(ref membersA:set(int), id: int, depth: int, cut: int) throws {
      var filename = outputPath + "_" + id:string + "_" + depth:string + "_" 
                                + membersA.size:string + "_" + cut:string + ".txt";
      var file = open(filename, ioMode.cw);
      var fileWriter = file.writer(locking=false);
      var mappedArr = nodeMapGraphG1[membersA.toArray()];

      fileWriter.writeln("# cluster ID: " + id: string); 
      fileWriter.writeln("# cluster Depth: " + depth: string); 
      fileWriter.writeln("# number of members: " + membersA.size: string);
      fileWriter.writeln("# cutsize: " + cut: string);
      fileWriter.writeln("# members: " + mappedArr: string);
      
      try fileWriter.close();
      try file.close();
    }

    /* Uses the global finalvertices and finalClusters list to write out the new cluster information
       after WCC completes. */
    proc writeClustersToFile() throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(finalVertices, finalClusters) do writer.writeln(nodeMapGraphG1[v], " ", c);

      writer.close();
      outfile.close();
    }

    /* Uses the vertices confirmed to be a well-connected cluster subgraph to write out the clusters
       as they are confirmed. */
    proc writeClustersToFile(ref vertices: set(int), cluster:int) throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=true);

      for v in vertices do writer.writeln(nodeMapGraphG1[v], " ", cluster);

      writer.close();
      outfile.close();
    }

    /* Given a specific partition, removes vertices with degree one, and returns a new partition 
       set. */
    proc removeDegOne(ref partition:set(int)): set(int) throws{
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

    /* Recursive method that processes a given set of vertices (partition), denotes if it is 
       well-connected or not, and if not calls itself on the new generated partitions. */
    proc callMinCut(ref vertices: set(int), id: int, depth: int): list(int) throws {
      var allWCC: list(int, parSafe=true);
      
      // Base condition 1: the partition is a singleton.
      if vertices.size < 2 then return allWCC;

      var (src, dst, mapper) = getEdgeList(vertices);

      // Base condition 2: the generated edge list does not contain any edges.
      if src.size < 1 then return allWCC;

      var components = connectedComponents(src, dst, mapper.size);
      var multipleComponents:bool = false;
      for c in components do if c != 0 { multipleComponents = true; break; }

      var n = mapper.size;
      var m = src.size;

      var partitionArr: [{0..<n}] int;
      var cut = c_computeMinCut(partitionArr, src, dst, n, m);

      var logN = floor(log10(vertices.size: real));
      var floorLog10N: int = logN:int;
      
      if cut > floorLog10N { // Cluster is well-connected.
        allWCC.pushBack(id);
        var currentId = globalId.fetchAdd(1);
        if outputType == "debug" then writeClustersToFile(vertices, id, depth, cut);
        else if outputType == "during" then writeClustersToFile(vertices, currentId);
        for v in vertices {
          finalVertices.pushBack(v);
          finalClusters.pushBack(currentId);
        }
        var outMsg = "Cluster " + id:string + " with depth " + depth:string + " and cutsize " 
                   + cut:string + " is well-connected with " + vertices.size:string + " vertices.";
        wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        return allWCC;
      }
      else{ // Cluster is not well-connected.
        var cluster1, cluster2 = new set(int);
        
        // Separate vertices into two partitions.
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.add(mapper[v]);
          else cluster2.add(mapper[v]);
        }

        var newSubClusters: list(int, parSafe=true);
        
        // Make sure the partitions are not singletons.
        if cluster1.size > 1 {
          var inPartition = removeDegOne(cluster1);
          newSubClusters = callMinCut(inPartition, id, depth+1);
        }
        if cluster2.size > 1 {
          var outPartition = removeDegOne(cluster2);
          newSubClusters = callMinCut(outPartition, id, depth+1);
        }
        
        // Append all findings to final allWCC list.
        for findings in newSubClusters do allWCC.pushBack(findings);
      }
      return allWCC;
    }
    

    /* TODO: Work in progress. Prove that it is better than removing vertices with degree one. */
    proc clusterC2D(ref clusterNodes: set(int)): set(int) throws {
      var coreMembers = clusterNodes;
      var coreDomain: domain(int, parSafe=true);
      
      for elem in coreMembers do coreDomain.add(elem);

      // Map from vertex id to its degree within the cluster.
      var degrees: [coreDomain] atomic int;

      // List of nodes with degree less than 2 to be removed.
      var nodesToRemove = new list(int);

      // Initialize degrees and nodesToRemove.
      forall vertex in coreMembers with (ref degrees, ref nodesToRemove, ref coreMembers) {
        degrees[vertex].write(calculateClusterDegree(coreMembers, vertex));
        if degrees[vertex].read() < 2 then nodesToRemove.pushBack(vertex);
      }

      // Iteratively remove nodes with degree less than 2.
      while !nodesToRemove.isEmpty() {
        // Collect node to be processed in this iteration.
        var currentNodesToRemove = nodesToRemove.popBack();
        const ref neighbors = dstNodesG1[segGraphG1[currentNodesToRemove]..<segGraphG1[currentNodesToRemove+1]];
        writeln("currentNodesToRemove: ", currentNodesToRemove);
        writeln("it's neighbours: ", neighbors);

        // Update degrees for each vertex.
        for u in clusterNodes {
          if neighbors.find(u) != -1 && degrees[u].read() >= 2 {
            degrees[u].sub(1);
            if degrees[u].read() < 2 then nodesToRemove.pushBack(u);
          }
        }
        writeln("currentNodesToRemove checked: ", currentNodesToRemove);
        degrees[currentNodesToRemove].write(-1);
      }

      // Step 4: Collect nodes with degrees >= 2 and update cluster
      var newMembers = new set(int);
      for v in degrees.domain {
        if degrees[v].read() >= 2 {
          newMembers.add(v);
        }
      }
      writeln("core2Decomposition returned cluster with size:",newMembers.size);
      writeln("core2Decomposition returned cluster with size:",newMembers);
      return newMembers;
    }

    /* Main executing function for well-connected components. */
    proc wcc(g1: SegGraph): [] int throws {
      var outMsg = "Graph loaded with " + g1.n_vertices:string + " vertices and " 
                 + g1.n_edges:string + " edges.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      var results: list(int, parSafe=true);
      var originalClusters = readClustersFile(inputcluster_filePath);
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),
                     "Reading clusters file finished.");

      var newClusterIds: chpl__processorAtomicType(int) = 0;
      var newClusters = new map(int, set(int));
      var newClusterIdToOriginalClusterId = new map(int, int);
      
      // TODO: Sequential for now since connected components is highly parallel. We need to discuss
      //       the tradeoff if it is more important to run connected components on the original
      //       clusters in parallel or run connected components in parallel.
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
            for (c,v) in zip(components,components.domain) {
              if tempMap.contains(c) then tempMap[c].add(mapper[v]);
              else {
                var s = new set(int);
                s.add(mapper[v]);
                tempMap[c] = s;
              }
            }
            for c in tempMap.keys() {
              var newId = newClusterIds.fetchAdd(1);
              newClusters[newId] = tempMap[c];
              newClusterIdToOriginalClusterId[newId] = key;
            }
            var outMsg = "Original cluster " + key:string + " was split up into " 
                       + tempMap.size:string + " clusters.";
            wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          } else { 
            var newId = newClusterIds.fetchAdd(1);
            newClusters[newId] = originalClusters[key];
            newClusterIdToOriginalClusterId[newId] = key;
          }
        }
      }

      forall key in newClusters.keysToArray() with (ref results, ref newClusters) {
        ref clusterToAdd = newClusters[key];
        var outMsg = "Processing cluster " + key:string + " which is a subcluster of " 
                   + newClusterIdToOriginalClusterId[key]:string;
        wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        if clusterToAdd.size > 1 { // The cluster is not a singleton.
          var newResults:list(int, parSafe=true);
          newResults = callMinCut(clusterToAdd, key, 0); 
          for mapping in newResults do results.pushBack(mapping);
        }
      }

      var subClusterArrToReturn: [0..#results.size] int;
      subClusterArrToReturn = results.toArray();

      if outputType == "post" then writeClustersToFile();
      
      return subClusterArrToReturn;
    } // end of wcc
    
    return clusterArr;
  } // end of runWCC
} // end of WellConnectedComponents module