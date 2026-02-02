module WellConnectedness {
  // Chapel modules.
  use ReplicatedDist;
  use CopyAggregation;
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
                            analysisType: string, maxDepth: int): int throws {
    // Maximum allowed recursion depth to prevent unbounded recursion
    const MAX_RECURSION_DEPTH = maxDepth;

    // Extract graph structural data as distributed arrays
    var srcNodesG_dist = toSymEntry(G.getComp("SRC_SDI"), int).a;
    var dstNodesG_dist = toSymEntry(G.getComp("DST_SDI"), int).a;
    var segGraphG_dist = toSymEntry(G.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG_dist = toSymEntry(G.getComp("VERTEX_MAP_SDI"), int).a;

    // Gather global sizes of distributed graph components
    const srcCount     = srcNodesG_dist.size;
    const segCount     = segGraphG_dist.size;
    const nodeMapCount = nodeMapGraphG_dist.size;

    // Define replicated domains so each locale holds the full index space
    const repSrcDom     = {0..<srcCount}     dmapped new replicatedDist();
    const repSegDom     = {0..<segCount}     dmapped new replicatedDist();
    const repNodeMapDom = {0..<nodeMapCount} dmapped new replicatedDist();

    // Fully replicated graph arrays (local copy on every locale)
    var srcNodesG     : [repSrcDom]     int;
    var dstNodesG     : [repSrcDom]     int;
    var segGraphG     : [repSegDom]     int;
    var nodeMapGraphG : [repNodeMapDom] int;


    // STEP 1: Build full arrays on Locale 0 ONLY
    // Use SrcAggregator to batch remote GETs for indices not local to locale 0.
    on Locales[0] {
        forall i in repSrcDom
            with (var srcAgg = new SrcAggregator(int),
                  var dstAgg = new SrcAggregator(int)) {
            srcAgg.copy(srcNodesG[i], srcNodesG_dist[i]);
            dstAgg.copy(dstNodesG[i], dstNodesG_dist[i]);
        }
        forall i in repSegDom
            with (var agg = new SrcAggregator(int)) {
            agg.copy(segGraphG[i], segGraphG_dist[i]);
        }
        forall i in repNodeMapDom
            with (var agg = new SrcAggregator(int)) {
            agg.copy(nodeMapGraphG[i], nodeMapGraphG_dist[i]);
        }
    }

    // STEP 2: Broadcast locale 0 replicand to ALL locales
    coforall loc in Locales do on loc {
      if here.id != 0 {
        srcNodesG.replicand(here) = srcNodesG.replicand(Locales[0]);
        dstNodesG.replicand(here) = dstNodesG.replicand(Locales[0]);
        segGraphG.replicand(here) = segGraphG.replicand(Locales[0]);
        nodeMapGraphG.replicand(here) = nodeMapGraphG.replicand(Locales[0]);
      }
    }

    // Variables needed for WCC or CM regardless if they are distributed or not
    var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
                        else if connectednessCriterion == "log2" then log2Criterion
                        else if connectednessCriterion == "sqrt" then sqrtCriterion
                        else if connectednessCriterion == "mult" then multCriterion
                        else log10Criterion;

    // Distributed block domain for manually controlling replicated variables
    var newClusterId = makeDistArray(numLocales, chpl__processorAtomicType(int));
    forall id in newClusterId do id.write(0);
    var clustersMap = makeDistArray(numLocales, map(int, set(int)));
    // var clustersMap = makeDistArray(numLocales, map(int, set(int)));
    
    // Turn on the clustering part of well-connectedness (CM)
    var runClustering = if analysisType == "CM" then true else false;


    /* Reads in a tab-delimited file denoting vertices and the clusters they belong to.
       Each locale reads the file independently and only keeps clusters assigned to it
       via round-robin (clusterID % numLocales == here.id). Uses the local replica of
       nodeMapGraphG for binary search — no cross-locale communication needed. */
    proc readClustersFile(filename: string) throws {
      coforall loc in Locales do on loc {
        const myId = here.id;
        var localNodeMap: [{0..<nodeMapGraphG.size}] int;
        localNodeMap = nodeMapGraphG;

        var file = open(filename, ioMode.r);
        var reader = file.reader(locking=false);
        var originalNode, clusterID: int;

        while reader.read(originalNode, clusterID) {
          // Ownership check
          if (clusterID % numLocales) != myId then continue;
          
          const (found, idx) = binarySearch(localNodeMap, originalNode);
          if !found then
            continue;

          // Insert into local cluster map
          if clustersMap[myId].contains(clusterID) {
            ref s = clustersMap[myId][clusterID];
            s.add(idx);
          } else {
            var s = new set(int);
            s.add(idx);
            clustersMap[myId].add(clusterID, s);
          }
        }
        reader.close();
        file.close();
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

    /* Returns the edge list of the induced subgraph given a set of vertices. */
    proc getEdgeList(ref vertices: set(int), ref srcNodes: [] int, 
                    ref dstNodes: [] int, ref segGraph: [] int) throws {
      var srcList = new list(int);
      var dstList = new list(int);

      var v2idx = new map(int, int);
      var idx2v = vertices.toArray();
      sort(idx2v);

      for (v,idx) in zip(idx2v, idx2v.domain) do v2idx[v] = idx;

      // Gather the edges of the subgraph induced by the given vertices.
      // OPTIMIZED: Use explicit indices instead of range slicing
      for u in vertices {
        const startIdx = segGraph[u];
        const endIdx = segGraph[u+1];
        for i in startIdx..<endIdx {
          const v = dstNodes[i];
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
          var (src, dst, mapper) = getEdgeList(clusterVertices, srcNodesG, dstNodesG, segGraphG);
          
          if src.size > 0 {
            var components = connectedComponentsLocal(src, dst, mapper.size);
            
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
            var (src, dst, mapper) = getEdgeList(clusterVertices, srcNodesG, dstNodesG, segGraphG);
            
            if src.size > 0 {
              var components = connectedComponentsLocal(src, dst, mapper.size);
              
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
                                          pId: int, depth: int, ref srcNodes: [] int,
                                          ref dstNodes: [] int, ref segGraph: [] int): list((int,int)) throws {
      var result = new list((int,int));

      // Use the parameter instead of hardcoded value
      if depth >= MAX_RECURSION_DEPTH {
        writeln("[Locale ", here.id, "] Max recursion depth ", MAX_RECURSION_DEPTH, " reached.");
        var cid = newClusterId[here.id].fetchAdd(1);
        var sid = "%i%i".format(here.id+1,cid);
        var id = sid:int;
        for v in vertices do result.pushBack((v, id));
        return result;
      }
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
        var (c1src, c1dst, c1mapper) = getEdgeList(cluster1, srcNodes, dstNodes, segGraph);
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
                    var components = connectedComponentsLocal(communitySrc, communityDst, communityMapper.size);
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
                                                                                  pId, depth+1,
                                                                                  srcNodes, dstNodes, segGraph);
                          result.pushBack(componentResult);
                        }
                      }
                    } else {
                      // Single connected component - recurse as normal
                      var communityResult = wellconnectednessRecursiveChecker(communitySet, communitySrc, 
                                                                              communityDst, communityMapper, 
                                                                              pId, depth+1,
                                                                              srcNodes, dstNodes, segGraph);
                      result.pushBack(communityResult);
                    }
                  }
                }
              }
            } else {
              // If Leiden finds only 1 community, still check connectivity for maximum robustness
              if c1src.size > 0 {
                var components = connectedComponentsLocal(c1src, c1dst, c1mapper.size);
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
                                                                              pId, depth+1,
                                                                              srcNodes, dstNodes, segGraph); 
                      result.pushBack(componentResult);
                    }
                  }
                } else {
                  // Single connected component - recurse normally
                  var cluster1Result = wellconnectednessRecursiveChecker(cluster1, c1src, c1dst, c1mapper,
                                                                        pId, depth+1,
                                                                        srcNodes, dstNodes, segGraph);
                  result.pushBack(cluster1Result);
                }
              }
            }
          } else {
            // WCC mode: Just recurse directly on cluster1
            var cluster1Result = wellconnectednessRecursiveChecker(cluster1, c1src, c1dst, c1mapper,
                                                                  pId, depth+1,
                                                                  srcNodes, dstNodes, segGraph); 
            result.pushBack(cluster1Result);
          }
        }
      }

      // Process cluster2
      if cluster2.size > postFilterMinSize {
        var (c2src, c2dst, c2mapper) = getEdgeList(cluster2, srcNodes, dstNodes, segGraph);    
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
                    var components = connectedComponentsLocal(communitySrc, communityDst, communityMapper.size);
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
                                                                                  pId, depth+1,
                                                                                  srcNodes, dstNodes, segGraph);
                          result.pushBack(componentResult);
                        }
                      }
                    } else {
                      // Single connected component - recurse as normal
                      var communityResult = wellconnectednessRecursiveChecker(communitySet, communitySrc, 
                                                                              communityDst, communityMapper, 
                                                                              pId, depth+1,
                                                                              srcNodes, dstNodes, segGraph);
                      result.pushBack(communityResult);
                    }
                  }
                }
              }
            } else {
              // If Leiden finds only 1 community, check its connectivity and recurse
              var (communitySrc, communityDst, communityMapper) = getEdgeList(cluster2, c2src, c2dst);
              
              if communitySrc.size > 0 {
                var components = connectedComponentsLocal(communitySrc, communityDst, communityMapper.size);
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
                                                                              pId, depth+1,
                                                                              srcNodes, dstNodes, segGraph);
                      result.pushBack(componentResult);
                    }
                  }
                } else {
                  var cluster2Result = wellconnectednessRecursiveChecker(cluster2, c2src, c2dst, c2mapper,
                                                                        pId, depth+1,
                                                                        srcNodes, dstNodes, segGraph);
                  result.pushBack(cluster2Result);
                }
              }
            }
          } else {
            // WCC mode: Just recurse directly on cluster2
            var cluster2Result = wellconnectednessRecursiveChecker(cluster2, c2src, c2dst, c2mapper,
                                                                  pId, depth+1,
                                                                  srcNodes, dstNodes, segGraph);
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
        var (src, dst, mapper) = getEdgeList(currCluster, srcNodesG, dstNodesG, segGraphG);
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
        var (src, dst, mapper) = getEdgeList(clusterToAdd, srcNodesG, dstNodesG, segGraphG);
        var result = wellconnectednessRecursiveChecker(clusterToAdd, src, dst, mapper, 
                                                 newClusterIdToOriginalClusterId[key], 0,
                                                 srcNodesG, dstNodesG, segGraphG);
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

      var allResults = makeDistArray(numLocales, list((int,int), parSafe=true));

      // Process clusters independently on each locale
      coforall loc in Locales do on loc {
        ref originalClusters = clustersMap[loc.id];
        // Local references to graph data (replicated)
        ref localSrcNodes = srcNodesG;
        ref localDstNodes = dstNodesG;
        ref localSegGraph = segGraphG;

        var localNewId = 0;
        var newClusters = new map(int, set(int));
        var newClusterIdToOriginalClusterId = new map(int, int);
        // Process original clusters and split into connected components
        for (key,currCluster) in zip(originalClusters.keys(),originalClusters.values()) {
          var (src, dst, mapper) = getEdgeList(currCluster, localSrcNodes, localDstNodes, localSegGraph);
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
                localNewId += 1;
                if tempMap[c].size > preFilterMinSize {
                  newClusters[localNewId] = tempMap[c];
                  newClusterIdToOriginalClusterId[localNewId] = key;
                }
              }
            } else {
              if currCluster.size > preFilterMinSize {
                localNewId += 1;
                newClusters[localNewId] = currCluster;
                newClusterIdToOriginalClusterId[localNewId] = key;
              }
            }
          }
        }
        // Check the well-connectedness of every cluster and/or connected component
        forall key in newClusters.keysToArray() with (ref newClusters, ref allResults) {
          ref clusterToAdd = newClusters[key];
          var (src, dst, mapper) = getEdgeList(clusterToAdd, localSrcNodes, localDstNodes, localSegGraph);
          var result = wellconnectednessRecursiveChecker(clusterToAdd,
                                                        src, dst, mapper,
                                                        newClusterIdToOriginalClusterId[key], 0,
                                                        localSrcNodes, localDstNodes, localSegGraph);
          allResults[loc.id].pushBack(result);
        }
  
      }
      
      outMsg = "%s took %r secs".format(analysisType, timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();

      // Write clusters to file
      writeClustersToFile(allResults);
      outMsg = "Writing clusters to file took %s secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.stop();
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