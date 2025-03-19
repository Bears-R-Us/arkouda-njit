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

  /* Define a custom tuple comparator. */
  record TupleComparator {
    proc compare(a: (int, int), b: (int, int)) {
      if a(0) != b(0) then return a(0)-b(0);
      else return a(1)-b(1);
    }
  }

  /* Record to store the result of finding well-connected clusters */
  record ClusterResult {
    var vertices: list(int, parSafe=true);
    var clusterIds: list(int, parSafe=true);
    
    proc init() {
      this.vertices = new list(int, parSafe=true);
      this.clusterIds = new list(int, parSafe=true);
    }
    
    /* Add a cluster to the result */
    proc addCluster(ref clusterVertices: set(int), clusterId: int) {
      for v in clusterVertices {
        this.vertices.pushBack(v);
        this.clusterIds.pushBack(clusterId);
      }
    }
    
    /* Merge another result into this one */
    proc merge(const ref other: ClusterResult) {
      for (v, c) in zip(other.vertices, other.clusterIds) {
        this.vertices.pushBack(v);
        this.clusterIds.pushBack(c);
      }
    }
    
    /* Number of clusters in the result */
    proc numClusters(): int {
      var uniqueIds = new set(int);
      for id in this.clusterIds do uniqueIds.add(id);
      return uniqueIds.size;
    }
    
    /* Reassign cluster IDs to be sequential starting from 0 */
    proc reassignIds(): (list(int, parSafe=true), list(int, parSafe=true)) throws{
      var oldToNew = new map(int, int);
      var uniqueIds: list(int) = new list(int);
      
      // Collect unique cluster IDs
      for id in this.clusterIds {
        if !oldToNew.contains(id) {
          oldToNew[id] = uniqueIds.size;
          uniqueIds.pushBack(id);
        }
      }
      
      // Create new lists with reassigned IDs
      var newVertices = new list(int, parSafe=true);
      var newClusterIds = new list(int, parSafe=true);
      
      for (v, c) in zip(this.vertices, this.clusterIds) {
        newVertices.pushBack(v);
        newClusterIds.pushBack(oldToNew[c]);
      }
      
      return (newVertices, newClusterIds);
    }
  }

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
    
    var newClusterIdToOriginalClusterId = new map(int, int);
    var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
                            else if connectednessCriterion == "log2" then log2Criterion
                            else if connectednessCriterion == "sqrt" then sqrtCriterion
                            else if connectednessCriterion == "mult" then multCriterion
                            else log10Criterion;
    
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
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);

      return (uniqueSrc, uniqueDst, idx2v);
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

    /* Writes all clusters out to a file AFTER they are deemed well-connected. */
    proc writeClustersToFile(ref vertices: list(int), ref clusterIds: list(int)) throws {
      var TESTCC: bool = true;  // To OLIVER: Flag to enable/disable final CC check
      if TESTCC {
        writeln("Performing final connected components check before writing.");
        
        // Group vertices by cluster ID
        var clusterMap = new map(int, set(int));
        for (v, c) in zip(vertices, clusterIds) {
          if clusterMap.contains(c) {
            clusterMap[c].add(v);
          } else {
            var s = new set(int);
            s.add(v);
            clusterMap[c] = s;
          }
        }

        // Check each cluster for connectedness
        var nonCCClusters = 0;
        for c in clusterMap.keys() {
          ref clusterVertices = clusterMap[c];
          var (src, dst, mapper) = getEdgeList(clusterVertices);
          
          if src.size > 0 {
            var components = connectedComponents(src, dst, mapper.size);
            
            // Check if there are multiple components
            var hasMultipleComponents = false;
            for comp in components do if comp != 0 { hasMultipleComponents = true; break; }
            
            if hasMultipleComponents {
              writeln("WARNING: Cluster ", c, " (size ", clusterVertices.size, ") is NOT CONNECTED at final output stage!");
              nonCCClusters += 1;
            }
          }
        }
        if nonCCClusters > 0 {
          writeln("FINAL WARNING: Found ", nonCCClusters, " non-connected clusters out of ", clusterMap.size, " total clusters!");
        } else {
          writeln("All clusters are connected. Output complete.");
        }
      }

    // Write clusters to file regardless of connectivity
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(vertices, clusterIds) do writer.writeln(nodeMapGraphG1[v], " ", c);

      writer.close();
      outfile.close();
    }

    /* Returns first node found with degree 1, or -1 if no such node exists */
    proc findMinDegreeNode(ref members: set(int)) throws {
      // Only look for degree 1 nodes, regardless of threshold
      for v in members {
        var nodeDegree = calculateClusterDegree(members, v);
        if nodeDegree == 1 {
          return v;
        }
      }
      return -1;  // No node found with degree 1
    }

    /* Try to determine if cluster is not well-connected by removing degree 1 nodes only */
    proc quickMinCutCheck(ref vertices: set(int)) throws {
      writeln("Starting quick mincut check (degree 1 only)");
      var currentVertices = vertices;
      var removedNodes = new set(int);  // Track removed nodes
      
      while currentVertices.size > 0 {
        var criterionValue = criterionFunction(currentVertices.size, connectednessCriterionMultValue):int;
        //writeln("Current cluster size: ", currentVertices.size, ", criterion value: ", criterionValue);
        
        // Find a node with degree 1
        var nodeToRemove = findMinDegreeNode(currentVertices);
        if nodeToRemove == -1 {
          writeln("No more degree 1 nodes found - need proper mincut check");
          vertices = currentVertices;  // Update original vertices to current state
          return (false, removedNodes);
        }
        
        // Remove the node and track it
        currentVertices.remove(nodeToRemove);
        removedNodes.add(nodeToRemove);
        //writeln("Removed node ", nodeToRemove, " with degree 1, remaining vertices: ", currentVertices.size);
        
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

    /* 
       Recursive method that processes a given set of vertices (partition), determines if it is 
       well-connected, and if not splits it using Viecut. Returns a ClusterResult with the
       well-connected clusters found.
    */
    proc wccRecursiveChecker(ref vertices: set(int), id: int, depth: int, localClusterId: int): ClusterResult throws{
      //writeln("-+-+-+-+-Cluster ", id, " starting check with local ID ", localClusterId);
      var result = new ClusterResult();
      
      // First try quick mincut check
      var (quickResult, removedNodes) = quickMinCutCheck(vertices);
      if quickResult {
        // writeln("Quick mincut determined cluster ", id, " is not well-connected");
        // writeln("Removed nodes: ", removedNodes);
        // writeln("Remaining vertices: ", vertices.size);
        
        // If we don't have enough vertices remaining, return empty result
        if vertices.size <= postFilterMinSize {
          //writeln("Remaining vertices too small (", vertices.size, " <= ", postFilterMinSize, "), skipping");
          return result;
        }
      }
      
      // Either quick check didn't determine result, or we have enough vertices to continue
      var (src, dst, mapper) = getEdgeList(vertices);

      // If the generated edge list is empty, then return empty result
      if src.size < 1 {
        //writeln("Empty edge list for cluster ", id, ", returning");
        return result;
      }

      var n = mapper.size;
      var m = src.size;

      // Run Viecut to both check well-connectedness and get the partition if needed
      var partitionArr: [{0..<n}] int;
      var cut = c_computeMinCut(partitionArr, src, dst, n, m);
      var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue):int;

      // writeln("cut: ", cut);
      // writeln("criterionValue: ", criterionValue);

      if cut > criterionValue { // Cluster is well-connected
        // writeln("Cluster ", id, " IS well-connected! Assigning local ID ", localClusterId);
        
        // Add cluster to result with the local cluster ID
        result.addCluster(vertices, localClusterId);
        
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " with depth " + depth:string + " and cutsize " 
                     + cut:string + " is well-connected with " + vertices.size:string + " vertices.";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        return result;
      }

      // If we're here, cluster is not well-connected
      //writeln("-+-+-+-+-Cluster ", id, " is NOT well-connected");
      
      // Use the partition from Viecut to split the cluster into two partitions
      var cluster1 = new set(int);
      var cluster2 = new set(int);
          
      // Separate vertices into two partitions using the min-cut result
      for (v,p) in zip(partitionArr.domain, partitionArr) {
        if p == 1 then cluster1.add(mapper[v]);
        else cluster2.add(mapper[v]);
      }
      
      // writeln("Min-cut partition sizes - cluster1: ", cluster1.size, ", cluster2: ", cluster2.size);
          
      // Process cluster1 if it meets the size threshold
      var nextLocalId = localClusterId;
            
      // Process cluster1 if it meets the size threshold
      if cluster1.size > postFilterMinSize {
        // Get edge list for recursion
        var (c1src, c1dst, c1mapper) = getEdgeList(cluster1);
        if c1src.size > 0 {
          // Remove all connected components checks
          // Directly recurse on cluster1
          var cluster1Result = wccRecursiveChecker(cluster1, id, depth+1, nextLocalId);
          result.merge(cluster1Result);
          nextLocalId += cluster1Result.numClusters();
        } else {
          //writeln("Empty edge list for cluster1, skipping");
        }
      } else {
        //writeln("cluster1 too small (", cluster1.size, " <= ", postFilterMinSize, "), skipping");
      }

      // Process cluster2 if it meets the size threshold
      if cluster2.size > postFilterMinSize {
        // Get edge list for recursion
        var (c2src, c2dst, c2mapper) = getEdgeList(cluster2);
        if c2src.size > 0 {
          // Remove all connected components checks
          // Directly recurse on cluster2
          var cluster2Result = wccRecursiveChecker(cluster2, id, depth+1, nextLocalId);
          result.merge(cluster2Result);
          nextLocalId += cluster2Result.numClusters();
        } else {
          //writeln("Empty edge list for cluster2, skipping");
        }
      } else {
        //writeln("cluster2 too small (", cluster2.size, " <= ", postFilterMinSize, "), skipping");
      }
      
      //writeln("Finished processing cluster ", id);
      return result;
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
      
      // Process original clusters and split into connected components
      for key in originalClusters.keysToArray() {
        var (src, dst, mapper) = getEdgeList(originalClusters[key]);
        if src.size > 0 { 
          var components = connectedComponents(src, dst, mapper.size);
          var multipleComponents:bool = false;
          for c in components do if c != 0 { multipleComponents = true; break; }
          
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
              if tempMap[c].size > preFilterMinSize {
                newClusters[newId] = tempMap[c];
                newClusterIdToOriginalClusterId[newId] = key;
              }
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

      // Process each cluster in parallel
      var allResults = new ClusterResult();
      var lock: sync bool = true;
      
      // Track the starting local ID for each task
      var clusterCount: atomic int = 0;
      
      forall key in newClusters.keysToArray() with (ref newClusters, ref allResults) {
        ref clusterToAdd = newClusters[key];
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Processing cluster " + key:string + " which is a subcluster of " 
                    + newClusterIdToOriginalClusterId[key]:string + ".";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        
        // Get a starting local ID for this task's clusters
        var localStartId = clusterCount.fetchAdd(1000); // Allocate space for up to 1000 clusters per task
        
        // Process the cluster with thread-local cluster IDs
        var result = wccRecursiveChecker(clusterToAdd, key, 0, localStartId);
        
        // If we found well-connected clusters, add them to the combined results
        if result.vertices.size > 0 {
          lock.readFE(); // acquire lock
          allResults.merge(result);
          lock.writeEF(true); // release lock
        }
      }
      
      // Reassign cluster IDs to be sequential starting from 0
      var (finalVerticesList, finalClustersList) = allResults.reassignIds();
      
      // Write clusters to file if requested
      if outputType == "post" then writeClustersToFile(finalVerticesList, finalClustersList);
      
      outMsg = "WCC found " + allResults.numClusters():string + " clusters to be well-connected.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      return allResults.numClusters();
    } // end of wcc
    
    var numClusters = wcc(g1);
    return numClusters;
  } // end of runWCC
} // end of WellConnectedComponents module