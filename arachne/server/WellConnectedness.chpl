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

  // At compile-time pick distributed or shared-memory execution.
  private param oneLocale = if ChplConfig.CHPL_COMM == "none" then true else false;
  // private param oneLocale = true;
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

    // Distributed block domain for manually controlling replicated variables
    var newClusterId = makeDistArray(numLocales, chpl__processorAtomicType(int));
    forall id in newClusterId do id.write(0);
    var clustersMap = makeDistArray(numLocales, map(int, set(int), parSafe=true));
    // var clustersMap = makeDistArray(numLocales, map(int, set(int)));
    
    // Turn on the clustering part of well-connectedness (CM)
    var runClustering = if analysisType == "CM" then true else false;


    /* Reads in a tab-delimited file denoting vertices and the clusters they belong to. Returns a
       map with original cluster identifier to a set of vertices that make up that cluster. */
    proc readClustersFile(filename: string) throws {
      var (vertices, clusters, _) = if oneLocale then readTSVFileLocal(filename,false)
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
      var segments = makeDistArray(uniqueClusters.size + 1, int);
      segments[0] = 0;
      segments[1..] = clusterCumulativeCounts; // has comms in multilocale

      
      forall i in segments.domain {
        if i != 0 {
          var c = uniqueClusters[i-1];
          var vInC = keptInternalVertices[segments[i-1]..<segments[i]]; // has comms in multilocale
          var s = new set(int);
          for v in vInC do s.add(v);
          on Locales[i%numLocales] {
            clustersMap[i%numLocales].add(c, s);  // ✓ Now executing ON locale 1
          }
          // clustersMap[i%numLocales].add(c,s); // has comms in multilocale
        }
      }
    }

    // /*
    //   Process file that lists clusterID with one vertex on each line to a map where each cluster
    //   ID is mapped to all of the vertices with that cluster ID. 
    // */
    // proc readClustersFile(filename: string) throws {
    //   var file = open(filename, ioMode.r);
    //   var reader = file.reader(locking=false);

    //   for line in reader.lines() {
    //     var fields = line.split();
    //     if fields.size >= 2 {
    //       var originalNode = fields(0): int;
    //       var clusterID = fields(1): int;
    //       const (found, idx) = binarySearch(nodeMapGraphG, originalNode);

    //       if found {
    //         var mappedNode = idx;
    //         if clustersMap[clusterID%numLocales].contains(clusterID) {
    //           clustersMap[clusterID%numLocales][clusterID].add(mappedNode);
    //         } else {
    //           var s = new set(int);
    //           s.add(mappedNode);
    //           clustersMap[clusterID%numLocales][clusterID] = s;
    //         }
    //       }
    //     }
    //   }
    //   reader.close();
    //   file.close();
    // }

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

    /* Writes all clusters out to a file AFTER they are deemed well-connected. */
    proc writeClustersToFile(ref allResults: [] list((int,int), parSafe=true)) throws {
      coforall loc in Locales do on loc {
        ref localResult = allResults[loc.id];
        var vertices: [0..<localResult.size] int;
        var clusterIds: [0..<localResult.size] int;
        forall (v,c,tup) in zip(vertices,clusterIds,localResult) {
          v = tup[0];
          c = tup[1];
        }
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
        // Get current locale ID padded to 5 digits
        var localeStr = "%05i".format(loc.id);

        // Find the last period for file extension
        var dotIdx = outputPath.rfind("."):int;
        var newFilename: string;

        if dotIdx >= 0 {
          // Insert _LOCALE_XXXXX before the file extension
          newFilename = outputPath[0..<dotIdx] + "_LOCALE_" + localeStr + outputPath[dotIdx..];
        } else {
          // If no extension, just append
          newFilename = outputPath + "_LOCALE_" + localeStr;
        }

        // Open and write
        var outfile = open(newFilename, ioMode.cw);
        var writer = outfile.writer(locking=false);

        for (v, c) in zip(vertices, clusterIds) do writer.writeln(nodeMapGraphG[v], " ", c);

        writer.close();
        outfile.close();
      }
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
      both WCC and CM steps using the UIUC approach. */
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
      
      // STEP 1: If well-connected, return cluster as-is
      if cut > criterionValue {
        var cid = newClusterId[here.id].fetchAdd(1);
        var sid = "%i%i".format(here.id+1,cid);
        var id = sid:int;
        for v in vertices do result.pushBack((v, id));

        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " from parent " + pId:string + " with depth " +
                      depth:string + " and cutsize " + cut:string + " is well-connected with " +
                      vertices.size:string + " vertices";
          wcLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
        }

        return result;
      }
      // writeln("from parent: ", pId," vertices:", vertices.size, "is not well connected");

      // STEP 2: If NOT well-connected, ALWAYS do min-cut first to split into two parts
      var cluster1, cluster2 = new set(int);
      for (v, p) in zip(partitionArr.domain, partitionArr) {
        if p == 1 then cluster1.add(mapper[v]);
        else cluster2.add(mapper[v]);
      }

      // Map src and dst back to original vertex IDs for getEdgeList calls
      for (u, v, i) in zip(src, dst, src.domain) {
        src[i] = mapper[u];
        dst[i] = mapper[v];
      }

      // STEP 3: Process each part (cluster1 and cluster2)
      
      // Process cluster1
      if cluster1.size > postFilterMinSize {
        var (c1src, c1dst, c1mapper) = getEdgeList(cluster1, src, dst);
        if c1src.size > 0 {
          if runClustering {
            // CM mode: Apply Leiden clustering to cluster1, then check connectivity of each community
            var n1 = c1mapper.size;
            var m1 = c1src.size;
            var communities1: [0..<n1] int;
            var numCommunities1: int(64) = 0;
            c_computeLeiden(c1src, c1dst, m1, n1, 1, 0.5, communities1, numCommunities1);

            var communityMap1 = new map(int, set(int));
            for (vertex, community) in zip(communities1.domain, communities1) {
              if !communityMap1.contains(community) {
                communityMap1[community] = new set(int);
              }
              communityMap1[community].add(c1mapper[vertex]);
            }

            // Check each community for connectivity and split if needed
            if communityMap1.size > 1 {
              for community in communityMap1.keys() {
                ref communitySet = communityMap1[community];
                if communitySet.size > postFilterMinSize {
                  var (communitySrc, communityDst, communityMapper) = getEdgeList(communitySet, c1src, c1dst);
                  
                  if communitySrc.size > 0 {
                    // Check if this community is connected
                    var components = connectedComponents(communitySrc, communityDst, communityMapper.size);
                    var multipleComponents:bool = false;
                    for c in components do if c != 0 { multipleComponents = true; break; }
                    
                    if multipleComponents {
                      // Split disconnected community into connected components
                      var tempMap = new map(int, set(int));
                      for (c,v) in zip(components,components.domain) {
                        if tempMap.contains(c) then tempMap[c].add(communityMapper[v]);
                        else {
                          var s = new set(int);
                          s.add(communityMapper[v]);
                          tempMap[c] = s;
                        }
                      }
                      // Recurse on each connected component
                      for c in tempMap.keys() {
                        if tempMap[c].size > postFilterMinSize {
                          var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], communitySrc, communityDst);
                          var componentResult = wellconnectednessRecursiveChecker(tempMap[c], compSrc, 
                                                                                  compDst, compMapper, 
                                                                                  pId, depth+1);
                          result.pushBack(componentResult);
                        }
                      }
                    } else {
                      // Single connected component - recurse as normal
                      var communityResult = wellconnectednessRecursiveChecker(communitySet, communitySrc, 
                                                                              communityDst, communityMapper, 
                                                                              pId, depth+1);
                      result.pushBack(communityResult);
                    }
                  }
                }
              }
            } else {
              // If Leiden finds only 1 community, still check connectivity for maximum robustness
              if c1src.size > 0 {
                var components = connectedComponents(c1src, c1dst, c1mapper.size);
                var multipleComponents:bool = false;
                for c in components do if c != 0 { multipleComponents = true; break; }
                
                if multipleComponents {
                  // Split into connected components
                  var tempMap = new map(int, set(int));
                  for (c,v) in zip(components,components.domain) {
                    if tempMap.contains(c) then tempMap[c].add(c1mapper[v]);
                    else {
                      var s = new set(int);
                      s.add(c1mapper[v]);
                      tempMap[c] = s;
                    }
                  }
                  for c in tempMap.keys() {
                    if tempMap[c].size > postFilterMinSize {
                      var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], c1src, c1dst);
                      var componentResult = wellconnectednessRecursiveChecker(tempMap[c], compSrc, 
                                                                              compDst, compMapper, 
                                                                              pId, depth+1);
                      result.pushBack(componentResult);
                    }
                  }
                } else {
                  // Single connected component - recurse normally
                  var cluster1Result = wellconnectednessRecursiveChecker(cluster1, c1src, c1dst, c1mapper,
                                                                        pId, depth+1);
                  result.pushBack(cluster1Result);
                }
              }
            }
          } else {
            // WCC mode: Just recurse directly on cluster1
            var cluster1Result = wellconnectednessRecursiveChecker(cluster1, c1src, c1dst, c1mapper,
                                                                  pId, depth+1);
            result.pushBack(cluster1Result);
          }
        }
      }

      // Process cluster2
      if cluster2.size > postFilterMinSize {
        var (c2src, c2dst, c2mapper) = getEdgeList(cluster2, src, dst);
        if c2src.size > 0 {
          if runClustering {
            // CM mode: Apply Leiden clustering to cluster2, then check connectivity of each community
            var n2 = c2mapper.size;
            var m2 = c2src.size;
            var communities2: [0..<n2] int;
            var numCommunities2: int(64) = 0;
            c_computeLeiden(c2src, c2dst, m2, n2, 1, 0.5, communities2, numCommunities2);

            var communityMap2 = new map(int, set(int));
            for (vertex, community) in zip(communities2.domain, communities2) {
              if !communityMap2.contains(community) {
                communityMap2[community] = new set(int);
              }
              communityMap2[community].add(c2mapper[vertex]);
            }

            // Check each community for connectivity and split if needed
            if communityMap2.size > 1 {
              for community in communityMap2.keys() {
                ref communitySet = communityMap2[community];
                if communitySet.size > postFilterMinSize {
                  var (communitySrc, communityDst, communityMapper) = getEdgeList(communitySet, c2src, c2dst);
                  
                  if communitySrc.size > 0 {
                    // Check if this community is connected
                    var components = connectedComponents(communitySrc, communityDst, communityMapper.size);
                    var multipleComponents:bool = false;
                    for c in components do if c != 0 { multipleComponents = true; break; }
                    
                    if multipleComponents {
                      // Split disconnected community into connected components
                      var tempMap = new map(int, set(int));
                      for (c,v) in zip(components,components.domain) {
                        if tempMap.contains(c) then tempMap[c].add(communityMapper[v]);
                        else {
                          var s = new set(int);
                          s.add(communityMapper[v]);
                          tempMap[c] = s;
                        }
                      }
                      // Recurse on each connected component
                      for c in tempMap.keys() {
                        if tempMap[c].size > postFilterMinSize {
                          var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], communitySrc, communityDst);
                          var componentResult = wellconnectednessRecursiveChecker(tempMap[c], compSrc, 
                                                                                  compDst, compMapper, 
                                                                                  pId, depth+1);
                          result.pushBack(componentResult);
                        }
                      }
                    } else {
                      // Single connected component - recurse as normal
                      var communityResult = wellconnectednessRecursiveChecker(communitySet, communitySrc, 
                                                                              communityDst, communityMapper, 
                                                                              pId, depth+1);
                      result.pushBack(communityResult);
                    }
                  }
                }
              }
            } else {
              // If Leiden finds only 1 community, check its connectivity and recurse
              var (communitySrc, communityDst, communityMapper) = getEdgeList(cluster2, c2src, c2dst);
              
              if communitySrc.size > 0 {
                var components = connectedComponents(communitySrc, communityDst, communityMapper.size);
                var multipleComponents:bool = false;
                for c in components do if c != 0 { multipleComponents = true; break; }
                
                if multipleComponents {
                  // Split into connected components
                  var tempMap = new map(int, set(int));
                  for (c,v) in zip(components,components.domain) {
                    if tempMap.contains(c) then tempMap[c].add(communityMapper[v]);
                    else {
                      var s = new set(int);
                      s.add(communityMapper[v]);
                      tempMap[c] = s;
                    }
                  }
                  for c in tempMap.keys() {
                    if tempMap[c].size > postFilterMinSize {
                      var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], communitySrc, communityDst);
                      var componentResult = wellconnectednessRecursiveChecker(tempMap[c], compSrc, 
                                                                              compDst, compMapper, 
                                                                              pId, depth+1);
                      result.pushBack(componentResult);
                    }
                  }
                } else {
                  var cluster2Result = wellconnectednessRecursiveChecker(cluster2, c2src, c2dst, c2mapper,
                                                                        pId, depth+1);
                  result.pushBack(cluster2Result);
                }
              }
            }
          } else {
            // WCC mode: Just recurse directly on cluster2
            var cluster2Result = wellconnectednessRecursiveChecker(cluster2, c2src, c2dst, c2mapper,
                                                                  pId, depth+1);
            result.pushBack(cluster2Result);
          }
        }
      }

      return result;
    }

    /* Shared-memory executor for well-connected components and connectivity modifier. */
    proc wellConnectednessSharedMemoryExecutor() throws {
      var outMsg = "Processing graph with %i vertices and %i edges with %s".format(G.n_vertices,
                                                                                   G.n_edges,
                                                                                   analysisType);
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      var timer:stopwatch;

      timer.start();
      readClustersFile(inputClustersFilePath);
      var originalClusters = clustersMap[0];
      outMsg = "Reading clusters took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();

      var newId = 0;
      var newClusters = new map(int, set(int));
      var newClusterIdToOriginalClusterId = new map(int,int);
      // Process original clusters and split into connected components
      for (key,currCluster) in zip(originalClusters.keys(),originalClusters.values()) {
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
              newId += 1;
              if tempMap[c].size > preFilterMinSize {
                newClusters[newId] = tempMap[c];
                newClusterIdToOriginalClusterId[newId] = key;
              }
            }
          } else {
            if currCluster.size > preFilterMinSize {
              newId += 1;
              newClusters[newId] = currCluster;
              newClusterIdToOriginalClusterId[newId] = key;
            }
          }
        }
      }
      outMsg = "Splitting up clusters yielded %i new clusters".format(newClusters.size);
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      outMsg = "Splitting up clusters took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();

      // Check the well-connectedness of every cluster and/or connected component
      var allResults = new list((int,int), parSafe=true);
      forall key in newClusters.keysToArray() with (ref newClusters, ref allResults) {
        ref clusterToAdd = newClusters[key];
        var (src, dst, mapper) = getEdgeList(clusterToAdd);
        var result = wellconnectednessRecursiveChecker(clusterToAdd, src, dst, mapper, 
                                                       newClusterIdToOriginalClusterId[key], 0);
        allResults.pushBack(result);
      }
      outMsg = "%s took %r secs".format(analysisType, timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();
      
      // Convert final results lists to arrays
      var finalVertices = makeDistArray(allResults.size, int);
      var finalClusters = makeDistArray(allResults.size, int);
      forall (tup,i) in zip(allResults, finalVertices.domain) {
        finalVertices[i] = tup[0];
        finalClusters[i] = tup[1];
      }
      outMsg = "Converting final lists of tuples to arrays took %s secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();
      
      // Write clusters to file
      writeClustersToFile(finalVertices, finalClusters);
      outMsg = "Writing clusters to file took %s secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.stop();
    } // end of wellConnectednessSharedMemoryExecutor

    /* Distributed-memory executor for well-connected components and connectivity modifier. */
    proc wellConnectednessDistributedMemoryExecutor() throws {
      var outMsg = "Processing graph with %i vertices and %i edges with %s".format(G.n_vertices,
                                                                                   G.n_edges,
                                                                                   analysisType);
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      var timer:stopwatch;

      timer.start();
      readClustersFile(inputClustersFilePath);
      outMsg = "Reading clusters took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();

      var newClusters = makeDistArray(numLocales, map(int, set(int)));
      var newClusterIdToOriginalClusterId = makeDistArray(numLocales, map(int,int));
      var newClustersSize:int = 0;
      // Process original clusters and split into connected components
      coforall loc in Locales with (+ reduce newClustersSize) do on loc {
        ref originalClusters = clustersMap[loc.id];
        var newClusterId = 0;
        for (key,currCluster) in zip(originalClusters.keys(),originalClusters.values()) {
          var (src, dst, mapper) = getEdgeList(currCluster);
          if src.size > 0 { 
            var components = connectedComponentsLocal(src, dst, mapper.size);
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
                newClusterId += 1;
                var newIdString = "%i%i".format(loc.id+1,newClusterId);
                var newId = newIdString:int;
                if tempMap[c].size > preFilterMinSize {
                  newClusters[loc.id][newId] = tempMap[c];
                  newClusterIdToOriginalClusterId[loc.id][newId] = key;
                }
              }
            } else {
              if currCluster.size > preFilterMinSize {
                newClusterId += 1;
                var newIdString = "%i%i".format(loc.id+1,newClusterId);
                var newId = newIdString:int;
                newClusters[loc.id][newId] = currCluster;
                newClusterIdToOriginalClusterId[loc.id][newId] = key;
              }
            }
          }
        }
        newClustersSize += newClusterId;
      }
      outMsg = "Splitting up clusters yielded %i new clusters".format(newClustersSize);
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      outMsg = "Splitting up clusters took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();

      // Check the well-connectedness of every cluster and/or connected component
      var allResults = makeDistArray(numLocales, list((int,int), parSafe=true));
      var allResultsSize:int = 0;
      coforall loc in Locales with (+ reduce allResultsSize) do on loc {
        forall key in newClusters[loc.id].keysToArray() {
          ref clusterToAdd = newClusters[loc.id][key];
          var (src, dst, mapper) = getEdgeList(clusterToAdd);
          var result = wellconnectednessRecursiveChecker(clusterToAdd, src, dst, mapper, 
                                                         newClusterIdToOriginalClusterId[loc.id][key], 
                                                         0);
          allResults[loc.id].pushBack(result);
        }
        allResultsSize += allResults[loc.id].size;
      }
      outMsg = "%s took %r secs".format(analysisType, timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.stop();
      
      // // Convert final results lists to arrays
      // var finalVertices = makeDistArray(allResultsSize, int);
      // var finalClusters = makeDistArray(allResultsSize, int);
      // var finalArrayRanges = makeDistArray(numLocales, int);
      // finalArrayRanges[0] = allResults[0].size;
      // for i in 1..<numLocales do finalArrayRanges[i] = finalArrayRanges[i-1] + allResults[i].size;
      // coforall loc in Locales do on loc {
      //   var localResult = allResults[loc.id];
      //   var start = if loc.id == 0 then 0 else finalArrayRanges[loc.id-1]+1;
      //   var end = finalArrayRanges[loc.id];
      //   forall (tup,i) in zip(localResult, start..end) {
      //     finalVertices[i] = tup[0];
      //     finalClusters[i] = tup[1];
      //   }
      // }
      // outMsg = "Converting final lists of tuples to arrays took %s secs".format(timer.elapsed());
      // wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      // timer.restart();
      
      // Write clusters to file
      writeClustersToFile(allResults);
      outMsg = "Writing clusters to file took %s secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();
    } // end of wellConnectednessDistributedMemoryExecutor
    
    if oneLocale then wellConnectednessSharedMemoryExecutor();
    else wellConnectednessDistributedMemoryExecutor();

    var numClusters = 0;
    for n in newClusterId do numClusters += n.read();
    var outMsg = "%s found %i clusters to be well-connected".format(analysisType,numClusters);
    wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

    return numClusters;
  }
}