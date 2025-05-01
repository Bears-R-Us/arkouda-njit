module ConnectivityModifier {
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
  use ConnectivityModifierMsg;
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
  use Unique;

  // C header and object files.
  require "viecut_helpers/computeMinCut.h",
          "viecut_helpers/computeMinCut.o",
          "viecut_helpers/logger.cpp.o";
  
  extern proc c_computeMinCut(partition_arr: [] int, src: [] int, dst: [] int, n: int, m: int): int;

  // C header and object files.
  require "leiden_helpers/computeLeiden.h",
          "leiden_helpers/computeLeiden.o",
          "-ligraph",
          "-llibleidenalg";

  extern proc c_computeLeiden(
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

  proc runCM(g1: SegGraph, st: borrowed SymTab, 
             inputcluster_filePath: string, outputPath: string,
             connectednessCriterion: string, connectednessCriterionMultValue: real, 
             preFilterMinSize: int, postFilterMinSize: int): int throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG1 = toSymEntry(g1.getComp("NEIGHBORS_SET_SDI"), set(int)).a;
    
    var newClusterIdToOriginalClusterId = new map(int, int);
    var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
                            else if connectednessCriterion == "log2" then log2Criterion
                            else if connectednessCriterion == "sqrt" then sqrtCriterion
                            else if connectednessCriterion == "mult" then multCriterion
                            else log10Criterion;

    var newClusterId: atomic int = 0;

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
              cmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            }
          }
        }
      }
      reader.close();
      file.close();
      var outMsg = "Number of clusters originally found in file: " + clusters.size:string;
      cmLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
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

    /* If every u in src and every v in dst exists in vertices then that edge stays, otherwise it is
    removed. */
    proc getEdgeList(ref vertices, ref src, ref dst) throws {
      var srcList = new list(int);
      var dstList = new list(int);

      var v2idx = new map(int, int);
      var idx2v = vertices.toArray();
      sort(idx2v);

      for (v,idx) in zip(idx2v, idx2v.domain) do v2idx[v] = idx;

      for (u,v) in zip(src,dst) {
        if vertices.contains(u) && vertices.contains(v) {
          srcList.pushBack(v2idx[u]);
          dstList.pushBack(v2idx[v]);
        } else {
          continue;
        }
      }

      // Convert lists to arrays since we need arrays for our edge list processing methods.
      var newSrc = srcList.toArray();
      var newDst = dstList.toArray();

      return (newSrc, newDst, idx2v);
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

    // /* Function to calculate the degree of a vertex within a component/cluster/community. */
    // proc calculateClusterDegree(ref members: set(int), vertex: int) throws {
    //   const ref neighbors = neighborsSetGraphG1[vertex];
    //   return setIntersectionSize(neighbors,members);
    // }

    /* Writes all clusters out to a file AFTER they are deemed well-connected. */
    proc writeClustersToFile(ref vertices, ref clusterIds) throws {
      if logLevel == LogLevel.DEBUG {
        var outMsg = "Performing final connected components check before writing to output file.";
        cmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        
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
              var outMsg = "Cluster " + c:string + " with " + clusterVertices.size:string
                         + " vertices is DISCONNECTED";
              cmLogger.warn(getModuleName(),getRoutineName(),getLineNumber(),outMsg);   
              nonCCClusters += 1;
            }
          }
        }
        if nonCCClusters > 0 {
          var outMsg = "Found " + nonCCClusters:string + " disconnected clusters out of " 
                     + clusterMap.size:string + " total clusters!";
          cmLogger.warn(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        } else {
          var outMsg = "All clusters are connected. Writing output.";
          cmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
      }
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(vertices, clusterIds) do writer.writeln(nodeMapGraphG1[v], " ", c);

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

    /* Given src array it returns the first vertex with degree one or -1 if not found. */
    proc checkForDegreeOne(ref src) {
      var degreeOneVertex = -1;
      var high = src[src.size-1];
      var degrees: [{0..high}] int;
      for u in src do degrees[u] += 1;
      for (u,c) in zip(degrees.domain, degrees) {
        if c == 1 {
          degreeOneVertex = u;
          break;
        }
      }
      return degreeOneVertex;
    }

    /* Recursive method that processes a given set of vertices (partition), denotes if it is 
       well-connected or not, and if not calls itself on the new generated partitions/clusters. */
    proc cmRecursiveChecker(ref vertices, ref src, ref dst, ref mapper,
                               pId: int, depth: int): list((int,int)) throws {
      var result = new list((int,int));
      if src.size < 1 then return result;

      var n = mapper.size;
      var m = src.size;

      var partitionArr: [{0..<n}] int;
      var cut:int;
      var degreeOneVertex = checkForDegreeOne(src); // check if a vertex with degree one exists 
        
      // If there is a vertex with degree one, intercept the cluster and split up into 
      // partitions of size 1 and n-1.
      if degreeOneVertex != -1 {
        cut = 1;
        for i in partitionArr.domain {
          if i == degreeOneVertex then partitionArr[i] = 1;
          else partitionArr[i] = 0;
        }
      } else cut = c_computeMinCut(partitionArr, src, dst, n, m);

      var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue):int;
      if cut > criterionValue { // Cluster is well-connected
        var id = newClusterId.fetchAdd(1);
        for v in vertices do result.pushBack((v,id));
        
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " from parent " + pId:string + " with depth " + 
                       depth:string + " and cutsize " + cut:string + " is well-connected with " + 
                       vertices.size:string + " vertices";
          cmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }

        return result;
      }

      // If we're here, cluster is not well-connected
      var communities: [0..<n] int;
      var numCommunities: int(64) = 0;
      c_computeLeiden(src, dst, m, n, 1, 0.5, communities, numCommunities);

      // Convert communities into sets
      var communityMap = new map(int, set(int));
      for (vertex, community) in zip(communities.domain, communities) {
        if !communityMap.contains(community) {
          communityMap[community] = new set(int);
        }
        communityMap[community].add(mapper[vertex]);
      }

      // If Leiden finds only one community, fall back to mincut partitions
      if communityMap.size <= 1 {
        // Use the partition from Viecut to split the cluster into two partitions
        var cluster1, cluster2 = new set(int);
            
        // Separate vertices into two partitions using the VieCut result
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.add(mapper[v]);
          else cluster2.add(mapper[v]);
        }

        // Convert src and dst to original vertex names.
        for (u,v,i) in zip(src,dst,src.domain) {
          src[i] = mapper[u];
          dst[i] = mapper[v];
        }
              
        // Process cluster1 if it meets the size threshold
        if cluster1.size > postFilterMinSize {
          var (c1src, c1dst, c1mapper) = getEdgeList(cluster1, src, dst);
          if c1src.size > 0 {
            var cluster1Result = cmRecursiveChecker(cluster1, c1src, c1dst, c1mapper, pId, depth+1);
            result.pushBack(cluster1Result);
          }
        }

        // Process cluster2 if it meets the size threshold
        if cluster2.size > postFilterMinSize {
          var (c2src, c2dst, c2mapper) = getEdgeList(cluster2, src, dst);
          if c2src.size > 0 {
            var cluster2Result = cmRecursiveChecker(cluster2, c2src, c2dst, c2mapper, pId, depth+1);
            result.pushBack(cluster2Result);
          }
        }
      }
      else {
        for community in communityMap.keys() {
          ref communitySet = communityMap[community];
          if communitySet.size > postFilterMinSize {
            var (communitySrc, communityDst, communityMapper) = getEdgeList(communitySet,src,dst);
            var communityResult = cmRecursiveChecker(communitySet,
                                                     communitySrc,
                                                     communityDst,
                                                     communityMapper,
                                                     pId,
                                                     depth+1);
            result.pushBack(communityResult);
          }
        }
      }
      return result;
    }

    /* Main executing function for cluster modifier. */
    proc cm(g1: SegGraph): int throws {
      var outMsg = "Graph loaded with " + g1.n_vertices:string + " vertices and " 
                + g1.n_edges:string + " edges.";
      cmLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      var originalClusters = readClustersFile(inputcluster_filePath);
      cmLogger.info(getModuleName(),getRoutineName(),getLineNumber(),
                    "Reading clusters file finished.");

      var newClusterIds: chpl__processorAtomicType(int) = 0;
      var newClusters = new map(int, set(int));
      
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
              cmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
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
      cmLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      // Check all connected components and/or clusters to see if they are well-connected or not
      var allResults = new list((int,int), parSafe=true);
      forall key in newClusters.keysToArray() with (ref newClusters, ref allResults) {
        ref clusterToAdd = newClusters[key];
        var (src, dst, mapper) = getEdgeList(clusterToAdd);
        var result = cmRecursiveChecker(clusterToAdd, src, dst, mapper, 
                                         newClusterIdToOriginalClusterId[key], 0);
        allResults.pushBack(result);
      }
      
      // Convert final results lists to arrays
      var finalVertices = makeDistArray(allResults.size, int);
      var finalClusters = makeDistArray(allResults.size, int);
      forall (tup,i) in zip(allResults, finalVertices.domain) {
        finalVertices[i] = tup[0];
        finalClusters[i] = tup[1];
      }
      
      // Write clusters to file
      writeClustersToFile(finalVertices, finalClusters);

      // Get number of cluster found
      var (values, counts) = uniqueSort(finalClusters);
      var numClusters = values.size;
      
      outMsg = "CM found " + numClusters:string + " clusters to be well-connected.";
      cmLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      return numClusters;
    } // end of cm
    
    var numClusters = cm(g1);
    return numClusters;
  } // end of runCM
} // end of ConnectivityModifier module