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
  use FileSystem;
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
      // Sort the edges and remove any multiples if they exist.
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);
      return (uniqueSrc, uniqueDst, idx2v);
    }
    /* Filter src/dst to edges where both endpoints are in vertices. Re-indexes and deduplicates. */
    proc getEdgeList(ref vertices, ref src, ref dst) throws {
      var v2idx = new map(int, int);
      var idx2v = vertices.toArray();
      sort(idx2v);
      for (v, idx) in zip(idx2v, idx2v.domain) do v2idx[v] = idx;
      // First pass: count matching edges to pre-allocate exact-size arrays.
      var count = 0;
      for (u, v) in zip(src, dst) {
        if v2idx.contains(u) && v2idx.contains(v) then count += 1;
      }
      // Second pass: fill pre-allocated arrays.
      var newSrc: [0..<count] int;
      var newDst: [0..<count] int;
      var i = 0;
      for (u, v) in zip(src, dst) {
        if v2idx.contains(u) && v2idx.contains(v) {
          newSrc[i] = v2idx[u];
          newDst[i] = v2idx[v];
          i += 1;
        }
      }
      var (sSrc, sDst) = sortEdgeList(newSrc, newDst);
      var (uSrc, uDst) = removeMultipleEdges(sSrc, sDst);
      return (uSrc, uDst, idx2v);
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
    /* Returns the first degree-one vertex in src, or -1 if none found. */
    proc checkForDegreeOne(ref src, n: int) {
      if src.size == 0 then return -1;
      var degrees: [{0..<n}] int;
      for u in src do degrees[u] += 1;
      for (u, c) in zip(degrees.domain, degrees) {
        if c == 1 { return u; }
      }
      return -1;
    }
    /* Recursive well-connectedness checker for WCC and CM modes. */
    proc wellconnectednessRecursiveChecker(ref vertices, ref src, ref dst, ref mapper,
                                          pId: int, depth: int, ref srcNodes: [] int,
                                          ref dstNodes: [] int, ref segGraph: [] int): list((int,int)) throws {
      var result = new list((int,int));

      if depth >= MAX_RECURSION_DEPTH {
        writeln("[Locale ", here.id, "] Max recursion depth ", MAX_RECURSION_DEPTH, " reached.");
        var cid = newClusterId[here.id].fetchAdd(1);
        var id = ("%i%i".format(here.id+1, cid)):int;
        for v in vertices do result.pushBack((v, id));
        return result;
      }
      if src.size < 1 then return result;

      var n = mapper.size;
      var m = src.size;

      // Compute criterion first so we can short-circuit before the expensive C++ call.
      var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue): int;

      // Short-circuit for criterionValue == 0: cheap CC check instead of min-cut.
      if criterionValue == 0 {
        var comps = connectedComponentsLocal(src, dst, n);
        var multi = false;
        for c in comps do if c != 0 { multi = true; break; }
        if !multi {
          // Connected: passes criterion immediately.
          var cid = newClusterId[here.id].fetchAdd(1);
          var id = ("%i%i".format(here.id+1, cid)):int;
          for v in vertices do result.pushBack((v, id));
          return result;
        }
        // Disconnected: split into connected components and recurse.
        var tempMap = new map(int, set(int));
        for (c, v) in zip(comps, comps.domain) {
          if tempMap.contains(c) then tempMap[c].add(mapper[v]);
          else { var s = new set(int); s.add(mapper[v]); tempMap[c] = s; }
        }
        for c in tempMap.keys() {
          if tempMap[c].size > postFilterMinSize {
            var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], srcNodes, dstNodes, segGraph);
            result.pushBack(wellconnectednessRecursiveChecker(
                tempMap[c], compSrc, compDst, compMapper, pId, depth+1,
                srcNodes, dstNodes, segGraph));
          }
        }
        return result;
      }

      var partitionArr: [{0..<n}] int;
      var cut: int;
      var degreeOneVertex = checkForDegreeOne(src, n);

      if degreeOneVertex != -1 {
        cut = 1;
        for i in partitionArr.domain do
          partitionArr[i] = if i == degreeOneVertex then 1 else 0;
      } else {
        cut = c_computeMinCut(partitionArr, src, dst, n, m);
      }

      // Well-connected: return cluster as-is
      if cut > criterionValue {
        var cid = newClusterId[here.id].fetchAdd(1);
        var id = ("%i%i".format(here.id+1, cid)):int;
        for v in vertices do result.pushBack((v, id));
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " (parent " + pId:string +
                       ") depth=" + depth:string + " cut=" + cut:string +
                       " n=" + vertices.size:string + " well-connected";
          wcLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
        }
        return result;
      }

      // Not well-connected: split on min-cut boundary
      var cluster1, cluster2 = new set(int);
      for (v, p) in zip(partitionArr.domain, partitionArr) {
        if p == 1 then cluster1.add(mapper[v]);
        else            cluster2.add(mapper[v]);
      }

      // Process cluster1 and cluster2 IN PARALLEL.
      var result1 = new list((int,int));
      var result2 = new list((int,int));

      cobegin with (ref result1, ref result2, ref cluster1, ref cluster2) {

        { // ==================== cluster1 ====================
          if cluster1.size > postFilterMinSize {
            var (c1src, c1dst, c1mapper) = getEdgeList(cluster1, srcNodes, dstNodes, segGraph);
            if c1src.size > 0 {
              if runClustering {
                // CM mode: Leiden -> check connectivity of each community -> recurse
                var n1 = c1mapper.size;
                var m1 = c1src.size;
                var communities1: [0..<n1] int;
                var numCommunities1: int(64) = 0;
                c_computeLeiden(c1src, c1dst, m1, n1, 1, 0.5, communities1, numCommunities1);

                // Build community sets using GLOBAL IDs
                var communityMap1 = new map(int, set(int));
                for (vertex, community) in zip(communities1.domain, communities1) {
                  if !communityMap1.contains(community) then
                    communityMap1[community] = new set(int);
                  communityMap1[community].add(c1mapper[vertex]);
                }

                // Remap c1src/c1dst to global IDs for community-level getEdgeList calls
                var c1srcG = [i in c1src.domain] c1mapper[c1src[i]];
                var c1dstG = [i in c1dst.domain] c1mapper[c1dst[i]];

                if communityMap1.size > 1 {
                  // Snapshot keys so the forall has no map contention.
                  var commKeys1 = communityMap1.keysToArray();
                  var commSets1: [commKeys1.domain] set(int);
                  for (k, s) in zip(commKeys1, commSets1) do s = communityMap1[k];
                  // Each community is independent — process in parallel.
                  var commResults1 = new list((int,int), parSafe=true);
                  forall (community, commSet) in zip(commKeys1, commSets1)
                      with (ref commResults1) {
                    if commSet.size > postFilterMinSize {
                      var (cSrc, cDst, cMapper) = getEdgeList(commSet, c1srcG, c1dstG);
                      if cSrc.size > 0 {
                        var comps = connectedComponentsLocal(cSrc, cDst, cMapper.size);
                        var multi = false;
                        for c in comps do if c != 0 { multi = true; break; }
                        if multi {
                          var tempMap = new map(int, set(int));
                          for (c, v) in zip(comps, comps.domain) {
                            if tempMap.contains(c) then tempMap[c].add(cMapper[v]);
                            else { var s = new set(int); s.add(cMapper[v]); tempMap[c] = s; }
                          }
                          for c in tempMap.keys() {
                            if tempMap[c].size > postFilterMinSize {
                              var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], cSrc, cDst);
                              var subResult = wellconnectednessRecursiveChecker(
                                  tempMap[c], compSrc, compDst, compMapper, pId, depth+1,
                                  srcNodes, dstNodes, segGraph);
                              for tup in subResult do commResults1.pushBack(tup);
                            }
                          }
                        } else {
                          var subResult = wellconnectednessRecursiveChecker(
                              commSet, cSrc, cDst, cMapper, pId, depth+1,
                              srcNodes, dstNodes, segGraph);
                          for tup in subResult do commResults1.pushBack(tup);
                        }
                      }
                    }
                  }
                  for tup in commResults1 do result1.pushBack(tup);
                } else {
                  // Single community: connectivity check then recurse
                  var comps = connectedComponentsLocal(c1src, c1dst, c1mapper.size);
                  var multi = false;
                  for c in comps do if c != 0 { multi = true; break; }
                  if multi {
                    var tempMap = new map(int, set(int));
                    for (c, v) in zip(comps, comps.domain) {
                      if tempMap.contains(c) then tempMap[c].add(c1mapper[v]);
                      else { var s = new set(int); s.add(c1mapper[v]); tempMap[c] = s; }
                    }
                    for c in tempMap.keys() {
                      if tempMap[c].size > postFilterMinSize {
                        var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], c1srcG, c1dstG);
                        result1.pushBack(wellconnectednessRecursiveChecker(
                            tempMap[c], compSrc, compDst, compMapper, pId, depth+1,
                            srcNodes, dstNodes, segGraph));
                      }
                    }
                  } else {
                    result1.pushBack(wellconnectednessRecursiveChecker(
                        cluster1, c1src, c1dst, c1mapper, pId, depth+1,
                        srcNodes, dstNodes, segGraph));
                  }
                }
              } else {
                // WCC mode: recurse directly
                result1.pushBack(wellconnectednessRecursiveChecker(
                    cluster1, c1src, c1dst, c1mapper, pId, depth+1,
                    srcNodes, dstNodes, segGraph));
              }
            }
          }
        } // end cluster1

        { // ==================== cluster2 ====================
          if cluster2.size > postFilterMinSize {
            var (c2src, c2dst, c2mapper) = getEdgeList(cluster2, srcNodes, dstNodes, segGraph);
            if c2src.size > 0 {
              if runClustering {
                var n2 = c2mapper.size;
                var m2 = c2src.size;
                var communities2: [0..<n2] int;
                var numCommunities2: int(64) = 0;
                c_computeLeiden(c2src, c2dst, m2, n2, 1, 0.5, communities2, numCommunities2);

                var communityMap2 = new map(int, set(int));
                for (vertex, community) in zip(communities2.domain, communities2) {
                  if !communityMap2.contains(community) then
                    communityMap2[community] = new set(int);
                  communityMap2[community].add(c2mapper[vertex]);
                }

                var c2srcG = [i in c2src.domain] c2mapper[c2src[i]];
                var c2dstG = [i in c2dst.domain] c2mapper[c2dst[i]];

                if communityMap2.size > 1 {
                  var commKeys2 = communityMap2.keysToArray();
                  var commSets2: [commKeys2.domain] set(int);
                  for (k, s) in zip(commKeys2, commSets2) do s = communityMap2[k];
                  var commResults2 = new list((int,int), parSafe=true);
                  forall (community, commSet) in zip(commKeys2, commSets2)
                      with (ref commResults2) {
                    if commSet.size > postFilterMinSize {
                      var (cSrc, cDst, cMapper) = getEdgeList(commSet, c2srcG, c2dstG);
                      if cSrc.size > 0 {
                        var comps = connectedComponentsLocal(cSrc, cDst, cMapper.size);
                        var multi = false;
                        for c in comps do if c != 0 { multi = true; break; }
                        if multi {
                          var tempMap = new map(int, set(int));
                          for (c, v) in zip(comps, comps.domain) {
                            if tempMap.contains(c) then tempMap[c].add(cMapper[v]);
                            else { var s = new set(int); s.add(cMapper[v]); tempMap[c] = s; }
                          }
                          for c in tempMap.keys() {
                            if tempMap[c].size > postFilterMinSize {
                              var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], cSrc, cDst);
                              var subResult = wellconnectednessRecursiveChecker(
                                  tempMap[c], compSrc, compDst, compMapper, pId, depth+1,
                                  srcNodes, dstNodes, segGraph);
                              for tup in subResult do commResults2.pushBack(tup);
                            }
                          }
                        } else {
                          var subResult = wellconnectednessRecursiveChecker(
                              commSet, cSrc, cDst, cMapper, pId, depth+1,
                              srcNodes, dstNodes, segGraph);
                          for tup in subResult do commResults2.pushBack(tup);
                        }
                      }
                    }
                  }
                  for tup in commResults2 do result2.pushBack(tup);
                } else {
                  var comps = connectedComponentsLocal(c2src, c2dst, c2mapper.size);
                  var multi = false;
                  for c in comps do if c != 0 { multi = true; break; }
                  if multi {
                    var tempMap = new map(int, set(int));
                    for (c, v) in zip(comps, comps.domain) {
                      if tempMap.contains(c) then tempMap[c].add(c2mapper[v]);
                      else { var s = new set(int); s.add(c2mapper[v]); tempMap[c] = s; }
                    }
                    for c in tempMap.keys() {
                      if tempMap[c].size > postFilterMinSize {
                        var (compSrc, compDst, compMapper) = getEdgeList(tempMap[c], c2srcG, c2dstG);
                        result2.pushBack(wellconnectednessRecursiveChecker(
                            tempMap[c], compSrc, compDst, compMapper, pId, depth+1,
                            srcNodes, dstNodes, segGraph));
                      }
                    }
                  } else {
                    result2.pushBack(wellconnectednessRecursiveChecker(
                        cluster2, c2src, c2dst, c2mapper, pId, depth+1,
                        srcNodes, dstNodes, segGraph));
                  }
                }
              } else {
                result2.pushBack(wellconnectednessRecursiveChecker(
                    cluster2, c2src, c2dst, c2mapper, pId, depth+1,
                    srcNodes, dstNodes, segGraph));
              }
            }
          }
        } // end cluster2

      } // end cobegin

      for tup in result1 do result.pushBack(tup);
      for tup in result2 do result.pushBack(tup);
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
  /* Run WCC/CM on pre-extracted cluster TSV files (no SegGraph needed).
     CC pre-check is omitted — files are pre-extracted from connected subgraphs. */
  proc runWellConnectednessFromFiles(inputFolderPath: string, outputPath: string,
                                     connectednessCriterion: string,
                                     connectednessCriterionMultValue: real,
                                     postFilterMinSize: int,
                                     analysisType: string, maxDepth: int): int throws {

    const MAX_RECURSION_DEPTH = maxDepth;

    var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
                        else if connectednessCriterion == "log2"  then log2Criterion
                        else if connectednessCriterion == "sqrt"  then sqrtCriterion
                        else if connectednessCriterion == "mult"  then multCriterion
                        else log10Criterion;

    var newClusterId = makeDistArray(numLocales, chpl__processorAtomicType(int));
    forall id in newClusterId do id.write(0);

    var runClustering = analysisType == "CM";

    // -----------------------------------------------------------------------
    // Utility procs (mirror the ones in runWellConnectedness)
    // -----------------------------------------------------------------------

    proc sortEdgeListF(ref src: [] int, ref dst: [] int) {
      // Move elements of src and dst to an array of tuples
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

    proc removeMultipleEdgesF(ref src: [] int, ref dst: [] int) {
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
      
      return (uniqueSrc.toArray(), uniqueDst.toArray());
    }

    /* Filter src/dst to edges where both endpoints are in vertices. Re-indexes and deduplicates. */
    proc getEdgeListF(const ref vertices, ref src, ref dst) throws {
      var v2idx = new map(int, int);
      var idx2v = vertices.toArray();
      sort(idx2v);
      for (v, idx) in zip(idx2v, idx2v.domain) do v2idx[v] = idx;
      // First pass: count matching edges to pre-allocate exact-size arrays.
      var count = 0;
      for (u, v) in zip(src, dst) {
        if v2idx.contains(u) && v2idx.contains(v) then count += 1;
      }
      // Second pass: fill pre-allocated arrays.
      var newSrc: [0..<count] int;
      var newDst: [0..<count] int;
      var i = 0;
      for (u, v) in zip(src, dst) {
        if v2idx.contains(u) && v2idx.contains(v) {
          newSrc[i] = v2idx[u];
          newDst[i] = v2idx[v];
          i += 1;
        }
      }
      var (sSrc, sDst) = sortEdgeListF(newSrc, newDst);
      var (uSrc, uDst) = removeMultipleEdgesF(sSrc, sDst);
      return (uSrc, uDst, idx2v);
    }

    // Returns the first degree-one vertex in src (bridge → min-cut = 1), or -1.
    proc checkForDegreeOneF(ref src, n: int) {
      if src.size == 0 then return -1;
      var degrees: [{0..<n}] int;
      for u in src do degrees[u] += 1;
      for (u, c) in zip(degrees.domain, degrees) {
        if c == 1 { return u; }
      }
      return -1;
    }

    /* Load a cluster TSV file and return (localSrc, localDst, mapper, verticesGlobal). */
    proc loadClusterFile(filename: string) throws {
      var edgeList = new list((int, int));
      var file   = open(filename, ioMode.r);
      var reader = file.reader(locking=false);
      var u, v: int;
      while reader.read(u, v) do edgeList.pushBack((u, v));
      reader.close();
      file.close();

      var vertexSet = new set(int);
      for (u, v) in edgeList { vertexSet.add(u); vertexSet.add(v); }

      // mapper: localIdx -> globalId
      var mapper = vertexSet.toArray();
      sort(mapper);
      var v2idx = new map(int, int);
      for (idx, orig) in zip(mapper.domain, mapper) do v2idx[orig] = idx;

      // Canonicalize each edge as (min,max) then deduplicate.
      var rawSrc: [0..<edgeList.size] int;
      var rawDst: [0..<edgeList.size] int;
      for (i, tup) in zip(0..<edgeList.size, edgeList) {
        const u = v2idx[tup[0]];
        const v = v2idx[tup[1]];
        if u < v { rawSrc[i] = u; rawDst[i] = v; }
        else      { rawSrc[i] = v; rawDst[i] = u; }
      }
      var (sSrc, sDst) = sortEdgeListF(rawSrc, rawDst);
      var (uSrc, uDst) = removeMultipleEdgesF(sSrc, sDst);

      // Add both directions for each unique undirected edge (bidirectional semantics).
      var src: [0..<2*uSrc.size] int;
      var dst: [0..<2*uDst.size] int;
      for i in 0..<uSrc.size {
        src[2*i]   = uSrc[i]; dst[2*i]   = uDst[i];
        src[2*i+1] = uDst[i]; dst[2*i+1] = uSrc[i];
      }
      // No second sort+dedup needed — bidirectional pairs are distinct.
      return (src, dst, mapper, vertexSet);
    }

    /* Write results for this locale. Each tuple is (originalGlobalId, clusterId). */
    proc writeClustersToFileF(ref results: list((int,int), parSafe=true),
                              localeId: int) throws {
      var localeStr  = "%05i".format(localeId);
      var dotIdx     = outputPath.rfind("."):int;
      var newFilename: string;
      if dotIdx >= 0 {
        newFilename = outputPath[0..<dotIdx] + "_LOCALE_" + localeStr + outputPath[dotIdx..];
      } else {
        newFilename = outputPath + "_LOCALE_" + localeStr;
      }
      var outfile = open(newFilename, ioMode.cw);
      var writer  = outfile.writer(locking=false);
      for (v, c) in results do writer.writeln(v, " ", c);
      writer.close();
      outfile.close();
    }

    // Recursive well-connectedness checker (no segGraph — re-extracts from src/dst).
    proc wellconnectednessRecursiveCheckerF(const ref vertices, ref src, ref dst,
                                            ref mapper, pId: int,
                                            depth: int): list((int,int)) throws {
      var result = new list((int,int));

      if depth >= MAX_RECURSION_DEPTH {
        var cid = newClusterId[here.id].fetchAdd(1);
        var id  = ("%i%i".format(here.id+1, cid)):int;
        for v in vertices do result.pushBack((v, id));
        return result;
      }
      if src.size < 1 then return result;

      var n = mapper.size;
      var m = src.size;

      if m < 1 then return result;

      // Compute criterion first so we can short-circuit before the expensive C++ call.
      var criterionValue = criterionFunction(vertices.size,
                                             connectednessCriterionMultValue): int;

      // Short-circuit for criterionValue == 0: cheap CC check instead of min-cut.
      if criterionValue == 0 {
        var comps = connectedComponentsLocal(src, dst, n);
        var multi = false;
        for c in comps do if c != 0 { multi = true; break; }
        if !multi {
          // Connected: passes criterion immediately.
          var cid = newClusterId[here.id].fetchAdd(1);
          var id  = ("%i%i".format(here.id+1, cid)):int;
          for v in vertices do result.pushBack((v, id));
          return result;
        }
        // Disconnected: split into connected components and recurse.
        for (u, v, i) in zip(src, dst, src.domain) {
          src[i] = mapper[u];
          dst[i] = mapper[v];
        }
        var tempMap = new map(int, set(int));
        for (c, v) in zip(comps, comps.domain) {
          if tempMap.contains(c) then tempMap[c].add(mapper[v]);
          else { var s = new set(int); s.add(mapper[v]); tempMap[c] = s; }
        }
        for c in tempMap.keys() {
          if tempMap[c].size > postFilterMinSize {
            var (compSrc, compDst, compMapper) = getEdgeListF(tempMap[c], src, dst);
            result.pushBack(wellconnectednessRecursiveCheckerF(
                tempMap[c], compSrc, compDst, compMapper, pId, depth+1));
          }
        }
        return result;
      }

      var partitionArr: [{0..<n}] int;
      var cut: int;
      var degreeOneVertex = checkForDegreeOneF(src, n);

      if degreeOneVertex != -1 {
        cut = 1;
        for i in partitionArr.domain do
          partitionArr[i] = if i == degreeOneVertex then 1 else 0;
      } else {
        cut = c_computeMinCut(partitionArr, src, dst, n, m);
      }

      // Well-connected: return this cluster as-is
      if cut > criterionValue {
        var cid = newClusterId[here.id].fetchAdd(1);
        var id  = ("%i%i".format(here.id+1, cid)):int;
        for v in vertices do result.pushBack((v, id));
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " (parent " + pId:string +
                       ") depth=" + depth:string + " cut=" + cut:string +
                       " n=" + vertices.size:string + " well-connected";
          wcLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
        }
        return result;
      }

      // Not well-connected: split on min-cut boundary
      var cluster1, cluster2 = new set(int);
      for (v, p) in zip(partitionArr.domain, partitionArr) {
        if p == 1 then cluster1.add(mapper[v]);
        else            cluster2.add(mapper[v]);
      }

      // Remap src/dst to global IDs for getEdgeListF filtering.
      forall i in src.domain {
        src[i] = mapper[src[i]];
        dst[i] = mapper[dst[i]];
      }

      // Process cluster1 and cluster2 in parallel.
      var result1 = new list((int,int));
      var result2 = new list((int,int));

      cobegin with (ref result1, ref result2) {

        { // ==================== cluster1 ====================
          if cluster1.size > postFilterMinSize {
            var (c1src, c1dst, c1mapper) = getEdgeListF(cluster1, src, dst);
            if c1src.size > 0 {
              if runClustering {
                // CM mode: Leiden -> check connectivity of each community -> recurse
                var n1 = c1mapper.size;
                var m1 = c1src.size;
                var communities1: [0..<n1] int;
                var numCommunities1: int(64) = 0;
                c_computeLeiden(c1src, c1dst, m1, n1, 1, 0.5, communities1, numCommunities1);

                // Build community sets using GLOBAL IDs
                var communityMap1 = new map(int, set(int));
                for (vertex, community) in zip(communities1.domain, communities1) {
                  if !communityMap1.contains(community) then
                    communityMap1[community] = new set(int);
                  communityMap1[community].add(c1mapper[vertex]);
                }

                // Remap c1src/c1dst to global IDs for community-level getEdgeListF calls
                var c1srcG = [i in c1src.domain] c1mapper[c1src[i]];
                var c1dstG = [i in c1dst.domain] c1mapper[c1dst[i]];

                if communityMap1.size > 1 {
                  // Snapshot keys so the forall has no map contention.
                  var commKeys1 = communityMap1.keysToArray();
                  var commSets1: [commKeys1.domain] set(int);
                  for (k, s) in zip(commKeys1, commSets1) do s = communityMap1[k];
                  // Each community is independent — process in parallel.
                  var commResults1 = new list((int,int), parSafe=true);
                  forall (community, commSet) in zip(commKeys1, commSets1)
                      with (ref commResults1) {
                    if commSet.size > postFilterMinSize {
                      var (cSrc, cDst, cMapper) = getEdgeListF(commSet, c1srcG, c1dstG);
                      if cSrc.size > 0 {
                        var comps = connectedComponentsLocal(cSrc, cDst, cMapper.size);
                        var multi = false;
                        for c in comps do if c != 0 { multi = true; break; }
                        if multi {
                          var tempMap = new map(int, set(int));
                          for (c, v) in zip(comps, comps.domain) {
                            if tempMap.contains(c) then tempMap[c].add(cMapper[v]);
                            else { var s = new set(int); s.add(cMapper[v]); tempMap[c] = s; }
                          }
                          for c in tempMap.keys() {
                            if tempMap[c].size > postFilterMinSize {
                              var (compSrc, compDst, compMapper) = getEdgeListF(tempMap[c], cSrc, cDst);
                              var subResult = wellconnectednessRecursiveCheckerF(
                                  tempMap[c], compSrc, compDst, compMapper, pId, depth+1);
                              for tup in subResult do commResults1.pushBack(tup);
                            }
                          }
                        } else {
                          var subResult = wellconnectednessRecursiveCheckerF(
                              commSet, cSrc, cDst, cMapper, pId, depth+1);
                          for tup in subResult do commResults1.pushBack(tup);
                        }
                      }
                    }
                  }
                  for tup in commResults1 do result1.pushBack(tup);
                } else {
                  // Single community: connectivity check then recurse
                  var comps = connectedComponentsLocal(c1src, c1dst, c1mapper.size);
                  var multi = false;
                  for c in comps do if c != 0 { multi = true; break; }
                  if multi {
                    var tempMap = new map(int, set(int));
                    for (c, v) in zip(comps, comps.domain) {
                      if tempMap.contains(c) then tempMap[c].add(c1mapper[v]);
                      else { var s = new set(int); s.add(c1mapper[v]); tempMap[c] = s; }
                    }
                    for c in tempMap.keys() {
                      if tempMap[c].size > postFilterMinSize {
                        var (compSrc, compDst, compMapper) = getEdgeListF(tempMap[c], c1srcG, c1dstG);
                        result1.pushBack(wellconnectednessRecursiveCheckerF(
                            tempMap[c], compSrc, compDst, compMapper, pId, depth+1));
                      }
                    }
                  } else {
                    result1.pushBack(wellconnectednessRecursiveCheckerF(
                        cluster1, c1src, c1dst, c1mapper, pId, depth+1));
                  }
                }
              } else {
                // WCC mode: recurse directly
                result1.pushBack(wellconnectednessRecursiveCheckerF(
                    cluster1, c1src, c1dst, c1mapper, pId, depth+1));
              }
            }
          }
        } // end cluster1

        { // ==================== cluster2 ====================
          if cluster2.size > postFilterMinSize {
            var (c2src, c2dst, c2mapper) = getEdgeListF(cluster2, src, dst);
            if c2src.size > 0 {
              if runClustering {
                var n2 = c2mapper.size;
                var m2 = c2src.size;
                var communities2: [0..<n2] int;
                var numCommunities2: int(64) = 0;
                c_computeLeiden(c2src, c2dst, m2, n2, 1, 0.5, communities2, numCommunities2);

                var communityMap2 = new map(int, set(int));
                for (vertex, community) in zip(communities2.domain, communities2) {
                  if !communityMap2.contains(community) then
                    communityMap2[community] = new set(int);
                  communityMap2[community].add(c2mapper[vertex]);
                }

                var c2srcG = [i in c2src.domain] c2mapper[c2src[i]];
                var c2dstG = [i in c2dst.domain] c2mapper[c2dst[i]];

                if communityMap2.size > 1 {
                  // Snapshot keys so the forall has no map contention.
                  var commKeys2 = communityMap2.keysToArray();
                  var commSets2: [commKeys2.domain] set(int);
                  for (k, s) in zip(commKeys2, commSets2) do s = communityMap2[k];
                  // Each community is independent — process in parallel.
                  var commResults2 = new list((int,int), parSafe=true);
                  forall (community, commSet) in zip(commKeys2, commSets2)
                      with (ref commResults2) {
                    if commSet.size > postFilterMinSize {
                      var (cSrc, cDst, cMapper) = getEdgeListF(commSet, c2srcG, c2dstG);
                      if cSrc.size > 0 {
                        var comps = connectedComponentsLocal(cSrc, cDst, cMapper.size);
                        var multi = false;
                        for c in comps do if c != 0 { multi = true; break; }
                        if multi {
                          var tempMap = new map(int, set(int));
                          for (c, v) in zip(comps, comps.domain) {
                            if tempMap.contains(c) then tempMap[c].add(cMapper[v]);
                            else { var s = new set(int); s.add(cMapper[v]); tempMap[c] = s; }
                          }
                          for c in tempMap.keys() {
                            if tempMap[c].size > postFilterMinSize {
                              var (compSrc, compDst, compMapper) = getEdgeListF(tempMap[c], cSrc, cDst);
                              var subResult = wellconnectednessRecursiveCheckerF(
                                  tempMap[c], compSrc, compDst, compMapper, pId, depth+1);
                              for tup in subResult do commResults2.pushBack(tup);
                            }
                          }
                        } else {
                          var subResult = wellconnectednessRecursiveCheckerF(
                              commSet, cSrc, cDst, cMapper, pId, depth+1);
                          for tup in subResult do commResults2.pushBack(tup);
                        }
                      }
                    }
                  }
                  for tup in commResults2 do result2.pushBack(tup);
                } else {
                  var comps = connectedComponentsLocal(c2src, c2dst, c2mapper.size);
                  var multi = false;
                  for c in comps do if c != 0 { multi = true; break; }
                  if multi {
                    var tempMap = new map(int, set(int));
                    for (c, v) in zip(comps, comps.domain) {
                      if tempMap.contains(c) then tempMap[c].add(c2mapper[v]);
                      else { var s = new set(int); s.add(c2mapper[v]); tempMap[c] = s; }
                    }
                    for c in tempMap.keys() {
                      if tempMap[c].size > postFilterMinSize {
                        var (compSrc, compDst, compMapper) = getEdgeListF(tempMap[c], c2srcG, c2dstG);
                        result2.pushBack(wellconnectednessRecursiveCheckerF(
                            tempMap[c], compSrc, compDst, compMapper, pId, depth+1));
                      }
                    }
                  } else {
                    result2.pushBack(wellconnectednessRecursiveCheckerF(
                        cluster2, c2src, c2dst, c2mapper, pId, depth+1));
                  }
                }
              } else {
                result2.pushBack(wellconnectednessRecursiveCheckerF(
                    cluster2, c2src, c2dst, c2mapper, pId, depth+1));
              }
            }
          }
        } // end cluster2

      } // end cobegin

      for tup in result1 do result.pushBack(tup);
      for tup in result2 do result.pushBack(tup);
      return result;
    } // end wellconnectednessRecursiveCheckerF

    // Shared-memory executor: load files on locale 0, process with forall.
    proc fromFilesSharedMemoryExecutor() throws {
      var timer: stopwatch;
      timer.start();

      // Collect all cluster_*.tsv paths
      var fileList = new list(string);
      for f in glob(inputFolderPath + "/cluster_*.tsv") do fileList.pushBack(f);
      var clusterFiles = fileList.toArray();
      sort(clusterFiles);

      var outMsg = "Found %i cluster files in %s".format(clusterFiles.size, inputFolderPath);
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      outMsg = "Listing files took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.restart();

      var allResults = new list((int,int), parSafe=true);

      forall filepath in clusterFiles with (ref allResults) {
        var (src, dst, mapper, verticesGlobal) = loadClusterFile(filepath);

        if src.size < 1 || verticesGlobal.size <= postFilterMinSize then continue;

        // No CC pre-check needed — files are pre-extracted from connected subgraphs.
        var clusterNum = filepath.find("cluster_"):int;
        var result = wellconnectednessRecursiveCheckerF(
                        verticesGlobal, src, dst, mapper, clusterNum, 0);
        allResults.pushBack(result);
      }

      outMsg = "%s took %r secs".format(analysisType, timer.elapsed());
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.restart();

      // Write single output file from locale 0
      writeClustersToFileF(allResults, 0);
      outMsg = "Writing output took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.stop();
    } // end fromFilesSharedMemoryExecutor

    // Distributed executor: each locale owns a round-robin slice of files.
    proc fromFilesDistributedMemoryExecutor() throws {
      var timer: stopwatch;
      timer.start();

      // Collect file list on locale 0 then broadcast
      var fileList = new list(string);
      on Locales[0] {
        for f in glob(inputFolderPath + "/cluster_*.tsv") do fileList.pushBack(f);
      }
      var clusterFiles = fileList.toArray();
      sort(clusterFiles);

      var outMsg = "Found %i cluster files in %s".format(clusterFiles.size, inputFolderPath);
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      outMsg = "Listing files took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.restart();

      coforall loc in Locales do on loc {
        const myId = here.id;
        var myFileList = new list(string);
        for fileIdx in myId..<clusterFiles.size by numLocales {
          myFileList.pushBack(clusterFiles[fileIdx]);
        }
        var localFiles = myFileList.toArray();
        var localResults = new list((int,int), parSafe=true);

        forall i in 0..<localFiles.size with (ref localResults) {
          var filepath = localFiles[i];
          var startIdx = filepath.find("cluster_");
          if startIdx < 0 then continue;
          startIdx += "cluster_".size;
          var dotIdx = filepath.rfind(".tsv");
          if dotIdx < 0 then continue;
          const clusterNum = filepath[startIdx..<dotIdx]:int;
          var (src, dst, mapper, verticesGlobal) = loadClusterFile(filepath);

          if src.size < 1 || verticesGlobal.size <= postFilterMinSize then continue;

          // No CC pre-check needed — files are pre-extracted from connected subgraphs.
          var result = wellconnectednessRecursiveCheckerF(
                          verticesGlobal, src, dst, mapper, clusterNum, 0);
          localResults.pushBack(result);
        }

        // Each locale writes its own output shard
        writeClustersToFileF(localResults, myId);
      }

      outMsg = "%s took %r secs".format(analysisType, timer.elapsed());
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.restart();

      outMsg = "Writing output took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.stop();
    } // end fromFilesDistributedMemoryExecutor

    if oneLocale then fromFilesSharedMemoryExecutor();
    else fromFilesDistributedMemoryExecutor();

    var numClusters = 0;
    for n in newClusterId do numClusters += n.read();
    var outMsg = "%s (from files) found %i well-connected clusters".format(analysisType, numClusters);
    wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
    return numClusters;
  } // end runWellConnectednessFromFiles
} // end module WellConnectedness