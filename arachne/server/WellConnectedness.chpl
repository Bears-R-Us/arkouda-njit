module WellConnectedness {
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
  use CommDiagnostics;
  import CopyAggregation.SrcAggregator;
  import CopyAggregation.DstAggregator;
  import ChplConfig;

  // Arachne modules.
  import WellConnectednessMsg.wcLogger;
  use BuildGraph;
  use GraphArray;
  use ConnectedComponents;

  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;
  use Logging;
  use ArgSortMsg;
  use Unique;

  // Header and object files required for external C procedure calls
  require "viecut_helpers/computeMinCut.h",
          "viecut_helpers/computeMinCut.o",
          "viecut_helpers/logger.cpp.o",
          "leiden_helpers/computeLeiden.h",
          "leiden_helpers/computeLeiden.o",
          "-ligraph",
          "-llibleidenalg";

  // Function headers for external C procedure calls
  extern proc c_computeMinCut(partition_arr: [] int, src: [] int, dst: [] int, n: int, m: int): int;
  extern proc c_computeLeiden(src: [] int, dst: [] int, NumEdges: int, NumNodes: int,
                              modularity_option: int, resolution: real, communities: [] int,
                              numCommunities: int): int;

  // First-class functions specifying well-connectedness criterions
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

  /* Runs either WCC or CM dynamically choosing between shared-memory or distributed-memory
     implementations of both. */
  proc runWellConnectedness(G: SegGraph, st: borrowed SymTab,
                            inputClustersFilePath: string, outputPath: string,
                            connectednessCriterion: string, connectednessCriterionMultValue: real,
                            preFilterMinSize: int, postFilterMinSize: int,
                            analysisType: string): int throws {
    // Extract graph structural data, can be distributed or not depending on the type of array a is
    var srcNodesG = toSymEntry(G.getComp("SRC_SDI"), int).a;
    var dstNodesG = toSymEntry(G.getComp("DST_SDI"), int).a;
    var segGraphG = toSymEntry(G.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG = toSymEntry(G.getComp("VERTEX_MAP_SDI"), int).a;

    // Variables needed for WCC or CM regardless if they are distributed or not
    var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
                        else if connectednessCriterion == "log2" then log2Criterion
                        else if connectednessCriterion == "sqrt" then sqrtCriterion
                        else if connectednessCriterion == "mult" then multCriterion
                        else log10Criterion;
    var newClusterIdToOriginalClusterId = new map(int,int);
    var newClusterId: atomic int = 0;

    // Variables needed for distributed WCC and CM
    var localeDom = blockDist.createDomain(0..<numLocales);
    var finalVerticesDistributed: [localeDom][{0..<1}] list(int, parSafe=true);
    var finalClustersDistributed: [localeDom][{0..<1}] list(int, parSafe=true);
    var newClusterIdDistributed: [localeDom][{0..<1}] chpl__processorAtomicType(int);
    coforall loc in Locales do on loc { newClusterIdDistributed[loc.id][0].write(1); }

    /* Reads in a tab-delimited file denoting vertices and the clusters they belong to. Returns a
       map with original cluster identifier to a set of vertices that make up that cluster. */
    proc readClustersFile(filename: string) throws {
      var (vertices, clusters, _) = if ChplConfig.CHPL_COMM == "none" then
                                      readTSVFileLocal(filename,false)
                                    else readTSVFileDistributed(filename,false);
      var civ = argsortDefault(clusters);
      var sortedClusters = clusters[civ]; // has comms in multilocale
      var sortedVertices = vertices[civ]; // has comms in multilocale

      var existingVertices = makeDistArray(vertices.size, bool);
      var internalVertices = makeDistArray(vertices.size, int);
      forall (v,i) in zip(sortedVertices,sortedVertices.domain) 
      with (ref existingVertices, ref internalVertices) {
        const(found,idx) = binarySearch(nodeMapGraphG, v); // has comms in multilocale
        if found {
          existingVertices[i] = true;
          internalVertices[i] = idx;
        }
      }
      var eviv = + scan existingVertices;
      var pop = eviv[eviv.size-1];
      var iv = makeDistArray(pop, int);
      forall i in existingVertices.domain with (ref iv) do
        if existingVertices[i] then iv[eviv[i]-1] = i; // has comms in multilocale

      var keptClusters = sortedClusters[iv]; // has comms in multilocale
      var keptInternalVertices = internalVertices[iv]; // has comms in multilocale

      var (uniqueClusters, clusterCounts) = uniqueFromSorted(keptClusters);
      var clusterCumulativeCounts = + scan clusterCounts;
      var segments = makeDistArray(uniqueClusters.size+1, int);
      segments[0] = 0;
      segments[1..] = clusterCumulativeCounts; // has comms in multilocale

      var clustersMap: [localeDom] map(int, set(int), parSafe=true);
      forall i in segments.domain {
        if i != 0 {
          var c = uniqueClusters[i-1];
          var vInC = keptInternalVertices[segments[i-1]..<segments[i]]; // has comms in multilocale
          var s = new set(int);
          for v in vInC do s.add(v);
          clustersMap[i%numLocales].add(c,s); // has comms in multilocale
        }
      }

      return clustersMap;
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
        const ref neighbors = dstNodesG[segGraphG[u]..<segGraphG[u+1]];
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

    /* Writes all clusters out to a file AFTER they are deemed well-connected. */
    proc writeClustersToFile(ref vertices, ref clusterIds) throws {
      if logLevel == LogLevel.DEBUG {
        var outMsg = "Performing final connected components check before writing to output file.";
        wcLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        
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
              wcLogger.warn(getModuleName(),getRoutineName(),getLineNumber(),outMsg);   
              nonCCClusters += 1;
            }
          }
        }
        if nonCCClusters > 0 {
          var outMsg = "Found " + nonCCClusters:string + " disconnected clusters out of " 
                     + clusterMap.size:string + " total clusters!";
          wcLogger.warn(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        } else {
          var outMsg = "All clusters are connected. Writing output.";
          wcLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
      }
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(vertices, clusterIds) do writer.writeln(nodeMapGraphG[v], " ", c);

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

    /* Recursive function that checks the well-connectedness of each passed cluster. Can execute
       both WCC and CM steps. */
    proc wellconnectednessRecursiveChecker(ref vertices, ref src, ref dst, ref mapper, 
                                           pId: int, depth: int): list((int,int)) throws {
      var result = new list((int,int));
      if src.size < 1 then return result;

      var n = mapper.size;
      var m = src.size;

      var partitionArr: [{0..<n}] int;
      var cut: int;
      var degreeOneVertex = checkForDegreeOne(src);

      if degreeOneVertex != -1 {
        cut = 1;
        for i in partitionArr.domain {
          partitionArr[i] = if i == degreeOneVertex then 1 else 0;
        }
      } else cut = c_computeMinCut(partitionArr, src, dst, n, m);

      var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue): int;
      if cut > criterionValue {
        var id = newClusterId.fetchAdd(1);
        for v in vertices do result.pushBack((v, id));

        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " from parent " + pId:string + " with depth " +
                      depth:string + " and cutsize " + cut:string + " is well-connected with " +
                      vertices.size:string + " vertices";
          wcLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
        }

        return result;
      }

      // If running CM, check for community structure.
      if analysisType == "CM" {
        var communities: [0..<n] int;
        var numCommunities: int(64) = 0;
        c_computeLeiden(src, dst, m, n, 1, 0.5, communities, numCommunities);

        var communityMap = new map(int, set(int));
        for (vertex, community) in zip(communities.domain, communities) {
          if !communityMap.contains(community) {
            communityMap[community] = new set(int);
          }
          communityMap[community].add(mapper[vertex]);
        }

        // If Leiden finds multiple communities, recurse on each
        if communityMap.size > 1 {
          for community in communityMap.keys() {
            ref communitySet = communityMap[community];
            if communitySet.size > postFilterMinSize {
              var (communitySrc, communityDst, communityMapper) = getEdgeList(communitySet, src, dst);
              var communityResult = wellconnectednessRecursiveChecker(communitySet, communitySrc, 
                                                                      communityDst, communityMapper, 
                                                                      pId, depth+1);
              result.pushBack(communityResult);
            }
          }
          return result; // Do not run the default VieCut partitioning
        }
      }

      // If WCC gets here or if CM finds only one Leiden community, then default to VieCut
      // partitioning
      var cluster1, cluster2 = new set(int);
      for (v, p) in zip(partitionArr.domain, partitionArr) {
        if p == 1 then cluster1.add(mapper[v]);
        else cluster2.add(mapper[v]);
      }

      for (u, v, i) in zip(src, dst, src.domain) {
        src[i] = mapper[u];
        dst[i] = mapper[v];
      }

      if cluster1.size > postFilterMinSize {
        var (c1src, c1dst, c1mapper) = getEdgeList(cluster1, src, dst);
        if c1src.size > 0 {
          var cluster1Result = wellconnectednessRecursiveChecker(cluster1, c1src, c1dst, c1mapper,
                                                                 pId, depth+1);
          result.pushBack(cluster1Result);
        }
      }

      if cluster2.size > postFilterMinSize {
        var (c2src, c2dst, c2mapper) = getEdgeList(cluster2, src, dst);
        if c2src.size > 0 {
          var cluster2Result = wellconnectednessRecursiveChecker(cluster2, c2src, c2dst, c2mapper,
                                                                 pId,depth+1);
          result.pushBack(cluster2Result);
        }
      }

      return result;
    }

    // /* Recursive method that processes a given set of vertices (partition), determines if it is 
    //    well-connected, and if not splits it using Viecut. */
    // proc wccRecursiveChecker(ref vertices, ref src, ref dst, ref mapper, 
    //                          pId: int, depth: int): list((int,int)) throws {
    //   var result = new list((int,int));
    //   if src.size < 1 then return result; // Make sure no empty src arrays are passed

    //   var n = mapper.size;
    //   var m = src.size;

    //   var partitionArr: [{0..<n}] int;
    //   var cut:int;
    //   var degreeOneVertex = checkForDegreeOne(src); // check if a vertex with degree one exists
      
    //   // If there is a vertex with degree one, intercept the cluster and split up into 
    //   // partitions of size 1 and n-1.
    //   if degreeOneVertex != -1 {
    //     cut = 1;
    //     for i in partitionArr.domain {
    //       if i == degreeOneVertex then partitionArr[i] = 1;
    //       else partitionArr[i] = 0;
    //     }
    //   } else cut = c_computeMinCut(partitionArr, src, dst, n, m);

    //   var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue):int;
    //   if cut > criterionValue { // Cluster is well-connected
    //     var id = newClusterId.fetchAdd(1);
    //     for v in vertices do result.pushBack((v,id));
        
    //     if logLevel == LogLevel.DEBUG {
    //       var outMsg = "Cluster " + id:string + " from parent " + pId:string + " with depth " + 
    //                    depth:string + " and cutsize " + cut:string + " is well-connected with " + 
    //                    vertices.size:string + " vertices";
    //       wcLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
    //     }

    //     return result;
    //   }
      
    //   // Use the partition from Viecut to split the cluster into two partitions
    //   var cluster1, cluster2 = new set(int);
          
    //   // Separate vertices into two partitions using the VieCut result
    //   for (v,p) in zip(partitionArr.domain, partitionArr) {
    //     if p == 1 then cluster1.add(mapper[v]);
    //     else cluster2.add(mapper[v]);
    //   }

    //   // Convert src and dst to original vertex names.
    //   for (u,v,i) in zip(src,dst,src.domain) {
    //     src[i] = mapper[u];
    //     dst[i] = mapper[v];
    //   }
            
    //   // Process cluster1 if it meets the size threshold
    //   if cluster1.size > postFilterMinSize {
    //     var (c1src, c1dst, c1mapper) = getEdgeList(cluster1, src, dst);
    //     if c1src.size > 0 {
    //       var cluster1Result = wccRecursiveChecker(cluster1, c1src, c1dst, c1mapper, pId, depth+1);
    //       result.pushBack(cluster1Result);
    //     }
    //   }

    //   // Process cluster2 if it meets the size threshold
    //   if cluster2.size > postFilterMinSize {
    //     var (c2src, c2dst, c2mapper) = getEdgeList(cluster2, src, dst);
    //     if c2src.size > 0 {
    //       var cluster2Result = wccRecursiveChecker(cluster2, c2src, c2dst, c2mapper, pId, depth+1);
    //       result.pushBack(cluster2Result);
    //     }
    //   }

    //   return result;
    // }

    // /* Recursive method that processes a given set of vertices (partition), denotes if it is 
    //   well-connected or not, and if not calls itself on the new generated partitions/clusters. */
    // proc cmRecursiveChecker(ref vertices, ref src, ref dst, ref mapper,
    //                            pId: int, depth: int): list((int,int)) throws {
    //   var result = new list((int,int));
    //   if src.size < 1 then return result;

    //   var n = mapper.size;
    //   var m = src.size;

    //   var partitionArr: [{0..<n}] int;
    //   var cut:int;
    //   var degreeOneVertex = checkForDegreeOne(src); // check if a vertex with degree one exists 
        
    //   // If there is a vertex with degree one, intercept the cluster and split up into 
    //   // partitions of size 1 and n-1.
    //   if degreeOneVertex != -1 {
    //     cut = 1;
    //     for i in partitionArr.domain {
    //       if i == degreeOneVertex then partitionArr[i] = 1;
    //       else partitionArr[i] = 0;
    //     }
    //   } else cut = c_computeMinCut(partitionArr, src, dst, n, m);

    //   var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue):int;
    //   if cut > criterionValue { // Cluster is well-connected
    //     var id = newClusterId.fetchAdd(1);
    //     for v in vertices do result.pushBack((v,id));
        
    //     if logLevel == LogLevel.DEBUG {
    //       var outMsg = "Cluster " + id:string + " from parent " + pId:string + " with depth " + 
    //                    depth:string + " and cutsize " + cut:string + " is well-connected with " + 
    //                    vertices.size:string + " vertices";
    //       wcLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
    //     }

    //     return result;
    //   }

    //   // If we're here, cluster is not well-connected
    //   var communities: [0..<n] int;
    //   var numCommunities: int(64) = 0;
    //   c_computeLeiden(src, dst, m, n, 1, 0.5, communities, numCommunities);

    //   // Convert communities into sets
    //   var communityMap = new map(int, set(int));
    //   for (vertex, community) in zip(communities.domain, communities) {
    //     if !communityMap.contains(community) {
    //       communityMap[community] = new set(int);
    //     }
    //     communityMap[community].add(mapper[vertex]);
    //   }

    //   // If Leiden finds only one community, fall back to mincut partitions
    //   if communityMap.size <= 1 {
    //     // Use the partition from Viecut to split the cluster into two partitions
    //     var cluster1, cluster2 = new set(int);
            
    //     // Separate vertices into two partitions using the VieCut result
    //     for (v,p) in zip(partitionArr.domain, partitionArr) {
    //       if p == 1 then cluster1.add(mapper[v]);
    //       else cluster2.add(mapper[v]);
    //     }

    //     // Convert src and dst to original vertex names.
    //     for (u,v,i) in zip(src,dst,src.domain) {
    //       src[i] = mapper[u];
    //       dst[i] = mapper[v];
    //     }
              
    //     // Process cluster1 if it meets the size threshold
    //     if cluster1.size > postFilterMinSize {
    //       var (c1src, c1dst, c1mapper) = getEdgeList(cluster1, src, dst);
    //       if c1src.size > 0 {
    //         var cluster1Result = cmRecursiveChecker(cluster1, c1src, c1dst, c1mapper, pId, depth+1);
    //         result.pushBack(cluster1Result);
    //       }
    //     }

    //     // Process cluster2 if it meets the size threshold
    //     if cluster2.size > postFilterMinSize {
    //       var (c2src, c2dst, c2mapper) = getEdgeList(cluster2, src, dst);
    //       if c2src.size > 0 {
    //         var cluster2Result = cmRecursiveChecker(cluster2, c2src, c2dst, c2mapper, pId, depth+1);
    //         result.pushBack(cluster2Result);
    //       }
    //     }
    //   }
    //   else {
    //     for community in communityMap.keys() {
    //       ref communitySet = communityMap[community];
    //       if communitySet.size > postFilterMinSize {
    //         var (communitySrc, communityDst, communityMapper) = getEdgeList(communitySet,src,dst);
    //         var communityResult = cmRecursiveChecker(communitySet,
    //                                                  communitySrc,
    //                                                  communityDst,
    //                                                  communityMapper,
    //                                                  pId,
    //                                                  depth+1);
    //         result.pushBack(communityResult);
    //       }
    //     }
    //   }
    //   return result;
    // }

    /* Main executing function for both well-connected components and connectivity modifier. */
    proc wellConnectednessExecutor(): int throws {
      var outMsg = "Analyzing graph with %i vertices and %i edges with %s".format(G.n_vertices,
                                                                                  G.n_edges,
                                                                                  analysisType);
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      var blockedClusters = readClustersFile(inputClustersFilePath);
      var originalClusters = blockedClusters[0];
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(), "Reading clusters finished");

      var newClusterIds: chpl__processorAtomicType(int) = 0;
      var newClusters = new map(int, set(int));
      
      // Process original clusters and split into connected components
      for key in originalClusters.keysToArray() {
        var currCluster = originalClusters.getAndRemove(key);
        var (src, dst, mapper) = getEdgeList(currCluster);
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
            if currCluster.size > preFilterMinSize {
              var newId = newClusterIds.fetchAdd(1);
              newClusters[newId] = currCluster;
              newClusterIdToOriginalClusterId[newId] = key;
            }
          }
        }
      }
      outMsg = "Splitting up clusters yielded " + newClusters.size:string + " new clusters";
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      // // Check all connected components and/or clusters to see if they are well-connected or not
      // var allResults = new list((int,int), parSafe=true);
      // forall key in newClusters.keysToArray() with (ref newClusters, ref allResults) {
      //   ref clusterToAdd = newClusters[key];
      //   var (src, dst, mapper) = getEdgeList(clusterToAdd);
      //   var result = if analysisType == "WCC" then 
      //                   wccRecursiveChecker(clusterToAdd, src, dst, mapper, 
      //                                       newClusterIdToOriginalClusterId[key], 0)
      //                else 
      //                   cmRecursiveChecker(clusterToAdd, src, dst, mapper, 
      //                                      newClusterIdToOriginalClusterId[key], 0);
      //   allResults.pushBack(result);
      // }

      // Check the well-connectedness of every cluster and/or connected component
      var allResults = new list((int,int), parSafe=true);
      forall key in newClusters.keysToArray() with (ref newClusters, ref allResults) {
        ref clusterToAdd = newClusters[key];
        var (src, dst, mapper) = getEdgeList(clusterToAdd);
        var result = wellconnectednessRecursiveChecker(clusterToAdd, src, dst, mapper, 
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
      
      outMsg = "%s found %i clusters to be well-connected".format(analysisType,numClusters);
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      return numClusters;
    } // end of wellConnectednessExecutor
    
    var numClusters = if ChplConfig.CHPL_COMM == "none" then wellConnectednessExecutor()
                      else wellConnectednessExecutor();
    return numClusters;
  }
}