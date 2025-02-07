module ClusterModifierTwo {
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
  use ClusterModifierTwoMsg;
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

  // C header and object files.
  require "Clustering_Algorithms/bin/run_leiden.o",
          "Clustering_Algorithms/src/run_leiden.h",
          "-ligraph",
          "-llibleidenalg";

  extern proc c_runLeiden(
    src: [] int,
    dst: [] int,
    NumEdges: int,
    NumNodes: int,
    modularity_option: int,
    resolution: real,
    communities: [] int,
    numCommunities: int
  ): int;


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

  proc runCM2 (g1: SegGraph, st: borrowed SymTab, 
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
    
    // // Example graph
    // var src: [0..7] int = [0, 1, 2, 3, 4, 5, 6, 7];
    // var dst: [0..7] int = [1, 2, 3, 4, 5, 6, 7, 0];
    // var NumEdges: int = src.size;  // Number of edges
    // var NumNodes: int = 8;         // Number of nodes

    // // Array to store community assignments
    // var communities: [0..NumNodes-1] int;

    // // Variable to store number of communities
    // var numCommunities: int(64) = 0;

    // // Printing the initialized arrays
    // writeln("Src: ", src);
    // writeln("Dst: ", dst);
    // writeln("NumEdges: ", NumEdges);
    // writeln("NumNodes: ", NumNodes);
    // writeln("Communities: ", communities);
    // writeln("numCommunities: ", numCommunities);

    // c_runLeiden(src, dst, NumEdges, NumNodes, 1, 0.5, communities, numCommunities);
    
    // writeln("AFTEER");
    // writeln("Communities: ", communities);
    // var numCom = max reduce communities;
    // writeln("numCom: ", numCom);
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
              cm2Logger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            }
          }
        }
      }
      reader.close();
      file.close();
      var outMsg = "Number of clusters originally found in file: " + clusters.size:string;
      cm2Logger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
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

    /* Returns first node found with lowest possible degree < threshold, or -1 if no such node exists */
    proc findMinDegreeNode(ref members: set(int), threshold: int) throws {
        //writeln("Finding min degree node with threshold: ", threshold);
        
        // If threshold is 1, we can return immediately since no node can have degree < 1
        if threshold <= 1 {
          //writeln("  Threshold <= 1, no need to check for lower degrees");
          return -1;
        }
        
        // Start from degree 1 and work up to threshold-1
        // Note: We don't need to check for degree 0 as those would be singleton nodes
        for degree in 1..<threshold {
          //writeln("  Checking for nodes with degree: ", degree);
            // Return the first node we find with this degree
          for v in members {
            var nodeDegree = calculateClusterDegree(members, v);
              if nodeDegree == degree {
                //writeln("  Found node ", v, " with degree ", degree);
                return v;
              }
          }
        }
        //writeln("  No nodes found with degree < ", threshold);
        return -1;  // No node found with degree < threshold
    }

    /* Try to determine if cluster is not well-connected by removing low degree nodes */
    proc quickMinCutCheck(ref vertices: set(int)) throws {
        writeln("Starting quick mincut check");
        var currentVertices = vertices;
        var removedNodes = new set(int);  // Track removed nodes
        
        while currentVertices.size > 0 {
            var criterionValue = criterionFunction(currentVertices.size, connectednessCriterionMultValue):int;
            // var minDegreeThreshold = criterionValue + 1;
            var minDegreeThreshold = criterionValue;
            writeln("Current cluster size: ", currentVertices.size, ", criterion value: ", criterionValue);
            
            var nodeToRemove = findMinDegreeNode(currentVertices, minDegreeThreshold);
            if nodeToRemove == -1 {
                writeln("No more low degree nodes found - need proper mincut check");
                vertices = currentVertices;  // Update original vertices to current state
                return (false, removedNodes);
            }
            
            // Remove the node and track it
            currentVertices.remove(nodeToRemove);
            removedNodes.add(nodeToRemove);
            writeln("Removed node ", nodeToRemove, ", remaining vertices: ", currentVertices.size);
            
            // If we've removed enough nodes that criterionValue can't be met
            if currentVertices.size <= criterionValue {
                writeln("Criterion value can't be met after removals");
                vertices = currentVertices;  // Update original vertices to current state
                return (true, removedNodes);
            }
        }
        vertices = currentVertices;  // Update original vertices to current state
        return (true, removedNodes);
    }

    /* Recursive method that processes a given set of vertices (partition), denotes if it is 
       well-connected or not, and if not calls itself on the new generated partitions/clusters. */
    /* Modified */   
    proc cmTwoRecursiveChecker(ref vertices: set(int), id: int, depth: int) throws {
        writeln("-+-+-+-+-Cluster ", id, " starting check");
        writeln("at the beginning vertices: ", vertices);
        
        // First try quick mincut check
        var (quickResult, removedNodes) = quickMinCutCheck(vertices);
        if quickResult {
            writeln("Quick mincut determined cluster ", id, " is not well-connected");
            writeln("Removed nodes: ", removedNodes);
            writeln("Remaining vertices: ", vertices.size);
            
            // If we don't have enough vertices remaining, return
            if vertices.size <= postFilterMinSize {
                writeln("Remaining vertices too small (", vertices.size, " <= ", postFilterMinSize, "), skipping");
                return;
            }
        }
        
        // Check removedNodes against vertices
        writeln("after quickMinCutCheck vertices: ", vertices);

        // Either quick check didn't determine result, or we have enough vertices to continue
        var (src, dst, mapper) = getEdgeList(vertices);

        // If the generated edge list is empty, then return
        if src.size < 1 {
            writeln("Empty edge list for cluster ", id, ", returning");
            return;
        }

        var n = mapper.size;
        var m = src.size;
        
        writeln("src: ", src);
        writeln("dst: ", dst);
        writeln("m: ", m);
        writeln("n: ", n);

        // If quick check didn't determine result, check if cluster is well-connected using min-cut
        if !quickResult {
            var partitionArr: [{0..<n}] int;
            var cut = c_computeMinCut(partitionArr, src, dst, n, m);
            var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue):int;

            writeln("cut: ", cut);
            writeln("criterionValue: ", criterionValue);

            if cut > criterionValue { // Cluster is well-connected
                writeln("Cluster ", id, " IS well-connected!");
                var currentId = globalId.fetchAdd(1);
                if outputType == "debug" then writeClustersToFile(vertices, id, currentId, depth, cut);
                else if outputType == "during" then writeClustersToFile(vertices, currentId);
                for v in vertices {
                    finalVertices.pushBack(v);
                    finalClusters.pushBack(currentId);
                }
                if logLevel == LogLevel.DEBUG {
                    var outMsg = "Cluster " + id:string + " with depth " + depth:string + " and cutsize " 
                                + cut:string + " is well-connected with " + vertices.size:string + " vertices.";
                    cm2Logger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                }
                return;
            }
        }

        // If we're here, cluster is not well-connected (either from quick check or min-cut)
        writeln("-+-+-+-+-Cluster ", id, " is NOT well-connected");
        
        // Run Leiden algorithm to get communities
        var communities: [0..<n] int;
        var numCommunities: int(64) = 0;
        
        writeln("Running Leiden algorithm...");
        c_runLeiden(src, dst, m, n, 1, 0.5, communities, numCommunities);

        writeln("node       : ", communities.domain);
        writeln("communities: ", communities);

        // Convert communities into sets
        var communityMap = new map(int, set(int));
        for (vertex, community) in zip(communities.domain, communities) {
            if !communityMap.contains(community) {
                communityMap[community] = new set(int);
            }
            communityMap[community].add(mapper[vertex]);
        }
        
        writeln("communityMap: ", communityMap);

        // If Leiden couldn't split the cluster (only one community found),
        // fall back to using the min-cut partitions
        if communityMap.size <= 1 {
            writeln("Leiden couldn't split cluster ", id, ", falling back to min-cut partitions");
            var cluster1, cluster2 = new set(int);
            var partitionArr: [{0..<n}] int;
            var cut = c_computeMinCut(partitionArr, src, dst, n, m);
                
            // Separate vertices into two partitions using the min-cut result
            for (v,p) in zip(partitionArr.domain, partitionArr) {
                if p == 1 then cluster1.add(mapper[v]);
                else cluster2.add(mapper[v]);
            }
            
            writeln("Min-cut partition sizes - cluster1: ", cluster1.size, ", cluster2: ", cluster2.size);
                
            // Make sure the partitions meet the minimum size
            if cluster1.size > postFilterMinSize {
                writeln("Recursing on cluster1 from cluster ", id);
                cmTwoRecursiveChecker(cluster1, id, depth+1);
            } else {
                writeln("cluster1 too small (", cluster1.size, " <= ", postFilterMinSize, "), skipping");
            }
            
            if cluster2.size > postFilterMinSize {
                writeln("Recursing on cluster2 from cluster ", id);
                cmTwoRecursiveChecker(cluster2, id, depth+1);
            } else {
                writeln("cluster2 too small (", cluster2.size, " <= ", postFilterMinSize, "), skipping");
            }
        }
        else {
            writeln("Leiden found ", communityMap.size, " communities");
            // Recurse on each Leiden community that meets the size threshold
            for community in communityMap.keys() {
                ref communitySet = communityMap[community];
                if communitySet.size > postFilterMinSize {
                    writeln("Recursing on Leiden community ", community, " (size ", communitySet.size, ") from cluster ", id);
                    cmTwoRecursiveChecker(communitySet, id, depth+1);
                } else {
                    writeln("Leiden community ", community, " too small (", communitySet.size, " <= ", postFilterMinSize, "), skipping");
                }
            }
        }
        writeln("Finished processing cluster ", id);
        return;
    }

    /* Main executing function for well-connected components. */
    proc cmTwo(g1: SegGraph): int throws {
      var outMsg = "Graph loaded with " + g1.n_vertices:string + " vertices and " 
                 + g1.n_edges:string + " edges.";
      cm2Logger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      var originalClusters = readClustersFile(inputcluster_filePath);
      cm2Logger.info(getModuleName(),getRoutineName(),getLineNumber(),
                     "Reading clusters file finished.");

      var newClusterIds: chpl__processorAtomicType(int) = 0;
      var newClusters = new map(int, set(int));
      
      // NOTE: Sequential for now since connected components is highly parallel. We need to discuss
      //       the tradeoff if it is more important to run connected components on the original
      //       clusters in parallel or run connected components in parallel.
      //
      // NOTE: This is probably noy even needed here. We could add a pre-filtering step to run this
      //       during graph construction or as a totally separate process instead of here.
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
            for c in tempMap.keys() { // NOTE: Could be parallel.Oliver why we did'nt ??
              var newId = newClusterIds.fetchAdd(1);
              if tempMap[c].size > preFilterMinSize {
                newClusters[newId] = tempMap[c];
                newClusterIdToOriginalClusterId[newId] = key;
              }
            }
            if logLevel == LogLevel.DEBUG {
              var outMsg = "Original cluster " + key:string + " was split up into " 
                        + tempMap.size:string + " clusters.";
              cm2Logger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
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
      cm2Logger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      forall key in newClusters.keysToArray() with (ref newClusters) {
        ref clusterToAdd = newClusters[key];
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Processing cluster " + key:string + " which is a subcluster of " 
                    + newClusterIdToOriginalClusterId[key]:string + ".";
          cm2Logger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        cmTwoRecursiveChecker(clusterToAdd, key, 0);
      }
      if outputType == "post" then writeClustersToFile();
      
      outMsg = "CM2 found " + globalId.read():string + " clusters to be well-connected.";
      cm2Logger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      return globalId.read();
    } // end of cmTwo
    
    var numClusters = cmTwo(g1);
    return numClusters;
  } // end of runCM2
} // end of ClusterModifierTwo module