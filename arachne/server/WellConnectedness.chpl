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
  proc log2Criterion(n:int, m:real) { return floor(log2(n:real)); }
  proc sqrtCriterion(n:int, m:real) { return floor(sqrt(n:real)/5); }
  proc multCriterion(n:int, m:real) { return floor(m*n:real); }

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
    const MAX_RECURSION_DEPTH = maxDepth;

    // Extract graph structural data as distributed arrays.
    var srcNodesG_dist = toSymEntry(G.getComp("SRC_SDI"), int).a;
    var dstNodesG_dist = toSymEntry(G.getComp("DST_SDI"), int).a;
    var segGraphG_dist = toSymEntry(G.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG_dist = toSymEntry(G.getComp("VERTEX_MAP_SDI"), int).a;

    const srcCount = srcNodesG_dist.size;
    const segCount = segGraphG_dist.size;
    const nodeMapCount = nodeMapGraphG_dist.size;

    // Define replicated domains so each locale holds the full index space.
    const repSrcDom = {0..<srcCount} dmapped new replicatedDist();
    const repSegDom = {0..<segCount} dmapped new replicatedDist();
    const repNodeMapDom = {0..<nodeMapCount} dmapped new replicatedDist();

    // Fully replicated graph arrays (local copy on every locale).
    var srcNodesG : [repSrcDom] int;
    var dstNodesG : [repSrcDom] int;
    var segGraphG : [repSegDom] int;
    var nodeMapGraphG : [repNodeMapDom] int;

    // STEP 1: Build full arrays on Locale 0, then broadcast to all locales.
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

    // STEP 2: Broadcast locale 0 replicand to all other locales.
    coforall loc in Locales do on loc {
      if here.id != 0 {
        srcNodesG.replicand(here) = srcNodesG.replicand(Locales[0]);
        dstNodesG.replicand(here) = dstNodesG.replicand(Locales[0]);
        segGraphG.replicand(here) = segGraphG.replicand(Locales[0]);
        nodeMapGraphG.replicand(here) = nodeMapGraphG.replicand(Locales[0]);
      }
    }

    var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
                        else if connectednessCriterion == "log2" then log2Criterion
                        else if connectednessCriterion == "sqrt" then sqrtCriterion
                        else if connectednessCriterion == "mult" then multCriterion
                        else log10Criterion;

    var newClusterId = makeDistArray(numLocales, chpl__processorAtomicType(int));
    forall id in newClusterId do id.write(0);
    var clustersMap = makeDistArray(numLocales, map(int, set(int)));
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
    proc sortEdgeList(ref src: [] int, ref dst: [] int, n: int) {
      const m = src.size;
      if m == 0 then return (src, dst);
      var keys: [0..<m] int;
      for i in 0..<m do keys[i] = src[i] * n + dst[i];
      sort(keys);
      var sortedSrc: [0..<m] int;
      var sortedDst: [0..<m] int;
      for i in 0..<m { sortedSrc[i] = keys[i] / n; sortedDst[i] = keys[i] % n; }
      return (sortedSrc, sortedDst);
    }
    /* Function to remove duplicate edges from sorted edge lists. */
    proc removeMultipleEdges(ref src: [] int, ref dst: [] int) {
      if src.size == 0 then return (src, dst);
      var count = 1;
      for i in 1..<src.size do if src[i] != src[i-1] || dst[i] != dst[i-1] then count += 1;
      var uniqueSrc: [0..<count] int;
      var uniqueDst: [0..<count] int;
      uniqueSrc[0] = src[0]; uniqueDst[0] = dst[0];
      var j = 1;
      for i in 1..<src.size {
        if src[i] != src[i-1] || dst[i] != dst[i-1] {
          uniqueSrc[j] = src[i]; uniqueDst[j] = dst[i]; j += 1;
        }
      }
      return (uniqueSrc, uniqueDst);
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
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst, idx2v.size);
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);
      return (uniqueSrc, uniqueDst, idx2v);
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
    /* Returns true if no bridge found; fills partitionArr and returns false if bridge found. */
    proc findBridgePartition(const ref src: [] int, const ref dst: [] int,
                             n: int, ref partitionArr: [] int): bool {
      if n <= 1 || src.size == 0 then return true;

      var deg: [0..<n] int;
      for u in src do deg[u] += 1;
      var adjStart: [0..<n+1] int;
      for i in 0..<n do adjStart[i+1] = adjStart[i] + deg[i];
      var adjList: [0..<src.size] int;
      var pos: [0..<n] int;
      for i in 0..<n do pos[i] = adjStart[i];
      for (u, v) in zip(src, dst) { adjList[pos[u]] = v; pos[u] += 1; }

      var disc: [0..<n] int = -1;
      var low: [0..<n] int = 0;
      var par: [0..<n] int = -1;
      var timer = 0;
      var stackV: [0..<n] int;
      var stackI: [0..<n] int;
      disc[0] = 0; low[0] = 0; timer = 1;
      stackV[0] = 0; stackI[0] = adjStart[0];
      var top = 1;

      while top > 0 {
        const u = stackV[top-1];
        if stackI[top-1] < adjStart[u+1] {
          const v = adjList[stackI[top-1]]; stackI[top-1] += 1;
          if disc[v] == -1 {
            disc[v] = timer; low[v] = timer; timer += 1;
            par[v] = u;
            stackV[top] = v; stackI[top] = adjStart[v]; top += 1;
          } else if v != par[u] {
            if disc[v] < low[u] then low[u] = disc[v];
          }
        } else {
          top -= 1;
          if par[u] != -1 {
            const p = par[u];
            if low[u] < low[p] then low[p] = low[u];
            if low[u] > disc[p] {
              // Bridge (p, u) found. BFS from u to identify u's component.
              var visited: [0..<n] bool;
              var queue:   [0..<n] int;
              var head = 0; var tail = 0;
              visited[u] = true;
              queue[tail] = u; tail += 1;
              while head < tail {
                const cur = queue[head]; head += 1;
                for wi in adjStart[cur]..<adjStart[cur+1] {
                  const w = adjList[wi];
                  if cur == u && w == p then continue; // skip bridge edge u→p
                  if !visited[w] { visited[w] = true; queue[tail] = w; tail += 1; }
                }
              }
              for i in 0..<n do partitionArr[i] = if visited[i] then 1 else 0;
              return false;
            }
          }
        }
      }
      return true;
    }
    /* Recursive well-connectedness checker for WCC and CM modes.
       Works entirely in local indices (mapper[localIdx] = graphVertexIdx).
       Partitions edges in a single pass after each split — no getEdgeList calls. */
    proc wellconnectednessRecursiveChecker(ref src: [] int, ref dst: [] int,
                                           ref mapper: [] int,
                                           pId: int, depth: int): list((int,int)) throws {
      var result = new list((int,int));
      const n = mapper.size;
      const m = src.size;
      if depth >= MAX_RECURSION_DEPTH {
        writeln("[Locale ", here.id, "] Max recursion depth ", MAX_RECURSION_DEPTH, " reached.");
        var cid = newClusterId[here.id].fetchAdd(1);
        var id = ("%i%i".format(here.id+1, cid)):int;
        for gid in mapper do result.pushBack((gid, id));
        return result;
      }
      if m < 1 then return result;

      const criterionValue = criterionFunction(n, connectednessCriterionMultValue):int;

      // criterionValue == 0: CC check is sufficient.
      if criterionValue == 0 {
        var comps = connectedComponentsLocal(src, dst, n);
        var multi = false;
        for c in comps do if c != 0 { multi = true; break; }
        if !multi {
          var cid = newClusterId[here.id].fetchAdd(1);
          var id = ("%i%i".format(here.id+1, cid)):int;
          for gid in mapper do result.pushBack((gid, id));
          return result;
        }

        // Multiple components: split using local indices.
        var compCount: [0..<n] int;
        for v in 0..<n do compCount[comps[v]] += 1;
        var compStart: [0..<n+1] int;
        for i in 0..<n do compStart[i+1] = compStart[i] + compCount[i];
        var compVertArr: [0..<n] int;
        var compPos: [0..<n] int;
        for i in 0..<n do compPos[i] = compStart[i];
        for v in 0..<n { compVertArr[compPos[comps[v]]] = v; compPos[comps[v]] += 1; }
        var remap: [0..<n] int = -1;
        for c in 0..<n {
          if compCount[c] == 0 then continue;
          const compSize = compCount[c];
          if compSize <= postFilterMinSize then continue;
          const startPos = compStart[c];
          var ni = 0;
          for si in startPos..<startPos+compSize { remap[compVertArr[si]] = ni; ni += 1; }
          var subMapper: [0..<compSize] int;
          for si in 0..<compSize do subMapper[si] = mapper[compVertArr[startPos+si]];
          var ec = 0;
          for (u, v) in zip(src, dst) do if remap[u] != -1 && remap[v] != -1 then ec += 1;
          var subSrc: [0..<ec] int; var subDst: [0..<ec] int; var ei = 0;
          for (u, v) in zip(src, dst) {
            if remap[u] != -1 && remap[v] != -1 {
              subSrc[ei] = remap[u]; subDst[ei] = remap[v]; ei += 1;
            }
          }
          for si in startPos..<startPos+compSize do remap[compVertArr[si]] = -1;
          result.pushBack(wellconnectednessRecursiveChecker(subSrc, subDst, subMapper, pId, depth+1));
        }
        return result;
      }
      // cv > 0: degree-one fast path, then bridge or mincut.
      var deg: [0..<n] int;
      var minDeg = max(int);
      for u in src do deg[u] += 1;
      for i in 0..<n do if deg[i] < minDeg then minDeg = deg[i];

      var degOneVertex = -1;
      for i in 0..<n do if deg[i] == 1 { degOneVertex = i; break; }

      var partitionArr: [0..<n] int;
      var cut: int;

      if degOneVertex != -1 {
        cut = 1;
        for i in 0..<n do partitionArr[i] = if i == degOneVertex then 1 else 0;
      } else if minDeg <= criterionValue {
        // branchA: sparse, bridge first — rare bridge gives better recursion tree than mincut
        if findBridgePartition(src, dst, n, partitionArr) {
          cut = c_computeMinCut(partitionArr, src, dst, n, m);
        } else {
          cut = 1;
        }
      } else if criterionValue == 1 {
        // branchB: cv==1, bridge check suffices
        if findBridgePartition(src, dst, n, partitionArr) {
          cut = 2;
        } else {
          cut = 1;
        }
      } else {
        // branchC: dense (minDeg>cv>=2), mincut directly
        cut = c_computeMinCut(partitionArr, src, dst, n, m);
      }

      if cut > criterionValue {
        var cid = newClusterId[here.id].fetchAdd(1);
        var id = ("%i%i".format(here.id+1, cid)):int;
        for gid in mapper do result.pushBack((gid, id));
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " (parent " + pId:string +
                       ") depth=" + depth:string + " cut=" + cut:string +
                       " n=" + n:string + " well-connected";
          wcLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
        }
        return result;
      }

      // Not well-connected: split on partition boundary.
      var cnt1 = 0; var cnt2 = 0;
      for p in partitionArr do if p == 1 then cnt1 += 1; else cnt2 += 1;
      var remap1: [0..<n] int = -1;
      var remap2: [0..<n] int = -1;
      var ni1 = 0; var ni2 = 0;
      for i in 0..<n {
        if partitionArr[i] == 1 { remap1[i] = ni1; ni1 += 1; }
        else                    { remap2[i] = ni2; ni2 += 1; }
      }

      var mapper1: [0..<cnt1] int;
      var mapper2: [0..<cnt2] int;
      for i in 0..<n {
        if partitionArr[i] == 1 then mapper1[remap1[i]] = mapper[i];
        else                         mapper2[remap2[i]] = mapper[i];
      }

      var ec1 = 0; var ec2 = 0;
      for (u, v) in zip(src, dst) {
        if partitionArr[u] == 1 && partitionArr[v] == 1 then ec1 += 1;
        else if partitionArr[u] == 0 && partitionArr[v] == 0 then ec2 += 1;
      }

      var src1: [0..<ec1] int; var dst1: [0..<ec1] int;
      var src2: [0..<ec2] int; var dst2: [0..<ec2] int;
      var i1 = 0; var i2 = 0;
      for (u, v) in zip(src, dst) {
        if partitionArr[u] == 1 && partitionArr[v] == 1 {
          src1[i1] = remap1[u]; dst1[i1] = remap1[v]; i1 += 1;
        } else if partitionArr[u] == 0 && partitionArr[v] == 0 {
          src2[i2] = remap2[u]; dst2[i2] = remap2[v]; i2 += 1;
        }
      }

      // Recurse on each half. WCC: recurse directly. CM: run Leiden, recurse per community.
      if cnt1 > postFilterMinSize && ec1 > 0 {
        if runClustering {
          var communities1: [0..<cnt1] int;
          var numComm1: int(64) = 0;
          numComm1 = c_computeLeiden(src1, dst1, ec1, cnt1, 1, 0.5, communities1, numComm1);
          var commCount1: [0..<numComm1] int;
          for v in 0..<cnt1 do commCount1[communities1[v]] += 1;
          var commStart1: [0..<numComm1+1] int;
          for i in 0..<numComm1 do commStart1[i+1] = commStart1[i] + commCount1[i];
          var commVertArr1: [0..<cnt1] int;
          var commPos1: [0..<numComm1] int;
          for i in 0..<numComm1 do commPos1[i] = commStart1[i];
          for v in 0..<cnt1 { commVertArr1[commPos1[communities1[v]]] = v; commPos1[communities1[v]] += 1; }
          var cr1: [0..<cnt1] int = -1;
          for c in 0..<numComm1 {
            if commCount1[c] == 0 then continue;
            const commSize1 = commCount1[c];
            if commSize1 <= postFilterMinSize then continue;
            const startPos1 = commStart1[c];
            var ri = 0;
            for si in startPos1..<startPos1+commSize1 { cr1[commVertArr1[si]] = ri; ri += 1; }
            var subMapper1: [0..<commSize1] int;
            for si in 0..<commSize1 do subMapper1[si] = mapper1[commVertArr1[startPos1+si]];
            var ec = 0;
            for (u, v) in zip(src1, dst1) do if cr1[u] != -1 && cr1[v] != -1 then ec += 1;
            if ec == 0 {
              for si in startPos1..<startPos1+commSize1 do cr1[commVertArr1[si]] = -1;
              continue;
            }
            var cS1: [0..<ec] int; var cD1: [0..<ec] int; var ei = 0;
            for (u, v) in zip(src1, dst1) {
              if cr1[u] != -1 && cr1[v] != -1 { cS1[ei] = cr1[u]; cD1[ei] = cr1[v]; ei += 1; }
            }
            for si in startPos1..<startPos1+commSize1 do cr1[commVertArr1[si]] = -1;
            result.pushBack(wellconnectednessRecursiveChecker(cS1, cD1, subMapper1, pId, depth+1));
          }
        } else {
          result.pushBack(wellconnectednessRecursiveChecker(src1, dst1, mapper1, pId, depth+1));
        }
      }
      if cnt2 > postFilterMinSize && ec2 > 0 {
        if runClustering {
          var communities2: [0..<cnt2] int;
          var numComm2: int(64) = 0;
          numComm2 = c_computeLeiden(src2, dst2, ec2, cnt2, 1, 0.5, communities2, numComm2);
          var commCount2: [0..<numComm2] int;
          for v in 0..<cnt2 do commCount2[communities2[v]] += 1;
          var commStart2: [0..<numComm2+1] int;
          for i in 0..<numComm2 do commStart2[i+1] = commStart2[i] + commCount2[i];
          var commVertArr2: [0..<cnt2] int;
          var commPos2: [0..<numComm2] int;
          for i in 0..<numComm2 do commPos2[i] = commStart2[i];
          for v in 0..<cnt2 { commVertArr2[commPos2[communities2[v]]] = v; commPos2[communities2[v]] += 1; }
          var cr2: [0..<cnt2] int = -1;
          for c in 0..<numComm2 {
            if commCount2[c] == 0 then continue;
            const commSize2 = commCount2[c];
            if commSize2 <= postFilterMinSize then continue;
            const startPos2 = commStart2[c];
            var ri = 0;
            for si in startPos2..<startPos2+commSize2 { cr2[commVertArr2[si]] = ri; ri += 1; }
            var subMapper2: [0..<commSize2] int;
            for si in 0..<commSize2 do subMapper2[si] = mapper2[commVertArr2[startPos2+si]];
            var ec = 0;
            for (u, v) in zip(src2, dst2) do if cr2[u] != -1 && cr2[v] != -1 then ec += 1;
            if ec == 0 {
              for si in startPos2..<startPos2+commSize2 do cr2[commVertArr2[si]] = -1;
              continue;
            }
            var cS2: [0..<ec] int; var cD2: [0..<ec] int; var ei = 0;
            for (u, v) in zip(src2, dst2) {
              if cr2[u] != -1 && cr2[v] != -1 { cS2[ei] = cr2[u]; cD2[ei] = cr2[v]; ei += 1; }
            }
            for si in startPos2..<startPos2+commSize2 do cr2[commVertArr2[si]] = -1;
            result.pushBack(wellconnectednessRecursiveChecker(cS2, cD2, subMapper2, pId, depth+1));
          }
        } else {
          result.pushBack(wellconnectednessRecursiveChecker(src2, dst2, mapper2, pId, depth+1));
        }
      }
      return result;
    } // end wellconnectednessRecursiveChecker

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

      // Process original clusters and split into connected components.
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

      // Check well-connectedness of every cluster/connected component.
      var allResults = new list((int,int), parSafe=true);
      forall key in newClusters.keysToArray() with (ref newClusters, ref allResults) {
        ref clusterToAdd = newClusters[key];
        var (src, dst, mapper) = getEdgeList(clusterToAdd, srcNodesG, dstNodesG, segGraphG);
        var result = wellconnectednessRecursiveChecker(src, dst, mapper,
                                                 newClusterIdToOriginalClusterId[key], 0);
        allResults.pushBack(result);
      }
      outMsg = "%s took %r secs".format(analysisType, timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();

      // Convert final results lists to arrays.
      var finalVertices = makeDistArray(allResults.size, int);
      var finalClusters = makeDistArray(allResults.size, int);
      forall (tup,i) in zip(allResults, finalVertices.domain) {
        finalVertices[i] = tup[0];
        finalClusters[i] = tup[1];
      }
      outMsg = "Converting final lists of tuples to arrays took %s secs".format(timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();

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

      // Process clusters independently on each locale.
      coforall loc in Locales do on loc {
        ref originalClusters = clustersMap[loc.id];
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
        // Check well-connectedness of every cluster/connected component.
        forall key in newClusters.keysToArray() with (ref newClusters, ref allResults) {
          ref clusterToAdd = newClusters[key];
          var (src, dst, mapper) = getEdgeList(clusterToAdd, localSrcNodes, localDstNodes, localSegGraph);
          var result = wellconnectednessRecursiveChecker(src, dst, mapper,
                                                        newClusterIdToOriginalClusterId[key], 0);
          allResults[loc.id].pushBack(result);
        }
      }
      outMsg = "%s took %r secs".format(analysisType, timer.elapsed());
      wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.restart();

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

    /* Load a cluster TSV file and return (src, dst, mapper).
       mapper[localIdx] = globalId. Both directions included for undirected graphs. */
    proc loadClusterFile(filename: string) throws {
      var srcList = new list(int);
      var dstList = new list(int);
      var vertMap = new map(int, int);
      var vertCount = 0;

      var file = open(filename, ioMode.r);
      var reader = file.reader(locking=false);
      var u, v: int;
      while reader.read(u, v) {
        if !vertMap.contains(u) { vertMap[u] = vertCount; vertCount += 1; }
        if !vertMap.contains(v) { vertMap[v] = vertCount; vertCount += 1; }
        const lu = vertMap[u], lv = vertMap[v];
        if lu < lv { srcList.pushBack(lu); dstList.pushBack(lv); }
        else        { srcList.pushBack(lv); dstList.pushBack(lu); }
      }
      reader.close();
      file.close();

      // Sort mapper by globalId and rebuild vertMap with sorted local indices.
      var mapper: [0..<vertCount] int;
      for (gid, li) in vertMap.items() do mapper[li] = gid;
      sort(mapper);
      var remap: [0..<vertCount] int;
      for (newLi, gid) in zip(0..<vertCount, mapper) {
        remap[vertMap[gid]] = newLi;
        vertMap[gid] = newLi;
      }

      // Re-normalise edge endpoints with sorted IDs.
      const edgeCount = srcList.size;
      var rawSrc: [0..<edgeCount] int;
      var rawDst: [0..<edgeCount] int;
      for i in 0..<edgeCount {
        const lu = remap[srcList[i]], lv = remap[dstList[i]];
        if lu < lv { 
          rawSrc[i] = lu; 
          rawDst[i] = lv; 
        }
        else { 
          rawSrc[i] = lv; 
          rawDst[i] = lu; 
        }
      }

      // Add both directions for undirected semantics.
      // sort+dedup skipped — input already normalised, no duplicates in practice.
      var src: [0..<2*edgeCount] int;
      var dst: [0..<2*edgeCount] int;
      for i in 0..<edgeCount {
        src[2*i]   = rawSrc[i]; dst[2*i]   = rawDst[i];
        src[2*i+1] = rawDst[i]; dst[2*i+1] = rawSrc[i];
      }
      return (src, dst, mapper);
    }
    /* Write results for this locale. Each tuple is (originalGlobalId, clusterId). */
    proc writeClustersToFileF(ref results: list((int,int), parSafe=true),
                              localeId: int) throws {
      var localeStr = "%05i".format(localeId);
      var dotIdx = outputPath.rfind("."):int;
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
   
    /* Returns true if no bridge found; fills partitionArr and returns false if bridge found. */
    proc findBridgePartitionF(const ref src: [] int, const ref dst: [] int,
                              n: int, ref partitionArr: [] int): bool {
      if n <= 1 || src.size == 0 then return true;

      var deg: [0..<n] int;
      for u in src do deg[u] += 1;
      var adjStart: [0..<n+1] int;
      for i in 0..<n do adjStart[i+1] = adjStart[i] + deg[i];
      var adjList: [0..<src.size] int;
      var pos: [0..<n] int;
      for i in 0..<n do pos[i] = adjStart[i];
      for (u, v) in zip(src, dst) { adjList[pos[u]] = v; pos[u] += 1; }

      var disc: [0..<n] int = -1;
      var low: [0..<n] int = 0;
      var par: [0..<n] int = -1;
      var timer = 0;
      var stackV: [0..<n] int;
      var stackI: [0..<n] int;
      disc[0] = 0; low[0] = 0; timer = 1;
      stackV[0] = 0; stackI[0] = adjStart[0];
      var top = 1;

      while top > 0 {
        const u = stackV[top-1];
        if stackI[top-1] < adjStart[u+1] {
          const v = adjList[stackI[top-1]]; stackI[top-1] += 1;
          if disc[v] == -1 {
            disc[v] = timer; low[v] = timer; timer += 1;
            par[v] = u;
            stackV[top] = v; stackI[top] = adjStart[v]; top += 1;
          } else if v != par[u] {
            if disc[v] < low[u] then low[u] = disc[v];
          }
        } else {
          top -= 1;
          if par[u] != -1 {
            const p = par[u];
            if low[u] < low[p] then low[p] = low[u];
            if low[u] > disc[p] {
              // Bridge (p, u) found. BFS from u (skipping the bridge edge) to
              // identify u's component: those vertices get partition=1.
              var visited: [0..<n] bool;
              var queue:   [0..<n] int;
              var head = 0; var tail = 0;
              visited[u] = true;
              queue[tail] = u; tail += 1;
              while head < tail {
                const cur = queue[head]; head += 1;
                for wi in adjStart[cur]..<adjStart[cur+1] {
                  const w = adjList[wi];
                  if cur == u && w == p then continue; // skip bridge edge u→p
                  if !visited[w] { visited[w] = true; queue[tail] = w; tail += 1; }
                }
              }
              for i in 0..<n do partitionArr[i] = if visited[i] then 1 else 0;
              return false;
            }
          }
        }
      }
      return true;
    }
    /* Recursive well-connectedness checker (from-files path). Local indices; edges partitioned in one pass after each split. CM mode recurses per Leiden community. */
    proc wellconnectednessRecursiveCheckerF(ref src: [] int, ref dst: [] int,
                                            ref mapper: [] int,
                                            pId: int, depth: int): list((int,int)) throws {
      var result = new list((int,int));
      const n = mapper.size;
      const m = src.size;
      if depth >= MAX_RECURSION_DEPTH {
        var cid = newClusterId[here.id].fetchAdd(1);
        var id  = ("%i%i".format(here.id+1, cid)):int;
        for gid in mapper do result.pushBack((gid, id));
        return result;
      }
      if m < 1 then return result;

      const criterionValue = criterionFunction(n, connectednessCriterionMultValue):int;

      // criterionValue == 0: CC check is sufficient. "As in previous version"
      if criterionValue == 0 {
        var comps = connectedComponentsLocal(src, dst, n);
        var multi = false;
        for c in comps do if c != 0 { multi = true; break; }
        if !multi {
          var cid = newClusterId[here.id].fetchAdd(1);
          var id  = ("%i%i".format(here.id+1, cid)):int;
          for gid in mapper do result.pushBack((gid, id));
          return result;
        }

        // Multiple components: split using local indices.
        var compCount: [0..<n] int;
        for v in 0..<n do compCount[comps[v]] += 1;
        var compStart: [0..<n+1] int;
        for i in 0..<n do compStart[i+1] = compStart[i] + compCount[i];
        var compVertArr: [0..<n] int;
        var compPos: [0..<n] int;
        for i in 0..<n do compPos[i] = compStart[i];
        for v in 0..<n { compVertArr[compPos[comps[v]]] = v; compPos[comps[v]] += 1; }
        var remap: [0..<n] int = -1;
        for c in 0..<n {
          if compCount[c] == 0 then continue;
          const compSize = compCount[c];
          if compSize <= postFilterMinSize then continue;
          const startPos = compStart[c];
          var ni = 0;
          for si in startPos..<startPos+compSize { remap[compVertArr[si]] = ni; ni += 1; }
          var subMapper: [0..<compSize] int;
          for si in 0..<compSize do subMapper[si] = mapper[compVertArr[startPos+si]];
          var ec = 0;
          for (u, v) in zip(src, dst) do if remap[u] != -1 && remap[v] != -1 then ec += 1;
          var subSrc: [0..<ec] int; var subDst: [0..<ec] int; var ei = 0;
          for (u, v) in zip(src, dst) {
            if remap[u] != -1 && remap[v] != -1 {
              subSrc[ei] = remap[u]; subDst[ei] = remap[v]; ei += 1;
            }
          }
          for si in startPos..<startPos+compSize do remap[compVertArr[si]] = -1;
          var childRes = wellconnectednessRecursiveCheckerF(subSrc, subDst, subMapper, pId, depth+1);
          result.pushBack(childRes);
        }
        return result;
      }
      // criterionValue > 0: degree-one fast path, then bridge check or min-cut.
      var partitionArr: [0..<n] int;
      var cut: int;

      var deg: [0..<n] int;
      var minDeg = max(int);
      for u in src do deg[u] += 1;
      for i in 0..<n do if deg[i] < minDeg then minDeg = deg[i];

      var degOneVertex = -1;
      for i in 0..<n do if deg[i] == 1 { degOneVertex = i; break; }

      if degOneVertex != -1 {
        // Case 1: leaf node exists so min-cut = 1 (fast split)
        cut = 1;
        for i in 0..<n do partitionArr[i] = if i == degOneVertex then 1 else 0;
      } else if criterionValue == 1 {
        // Case 2: we only care if min-cut > 1
        // bridge check is enough (no need for full mincut)
        if findBridgePartitionF(src, dst, n, partitionArr) {
          cut = 2; 
        } else {
          cut = 1;  
        }
      } else {
        // Case 3: general case (criterionValue >= 2)
        // Try cheap split first (bridge detection)
        if findBridgePartitionF(src, dst, n, partitionArr) {
          // no bridge -> need exact mincut
          cut = c_computeMinCut(partitionArr, src, dst, n, m);
        } else {
          cut = 1;  // bridge found, partition already valid so skip cactus
        }
      }

      if cut > criterionValue {
        var cid = newClusterId[here.id].fetchAdd(1);
        var id  = ("%i%i".format(here.id+1, cid)):int;
        for gid in mapper do result.pushBack((gid, id));
        return result;
      }

      // Not well-connected: split on partition boundary.
      var cnt1 = 0; var cnt2 = 0;
      for p in partitionArr do if p == 1 then cnt1 += 1; else cnt2 += 1;
      var remap1: [0..<n] int = -1;
      var remap2: [0..<n] int = -1;
      var ni1 = 0; var ni2 = 0;
      for i in 0..<n {
        if partitionArr[i] == 1 { remap1[i] = ni1; ni1 += 1; }
        else                    { remap2[i] = ni2; ni2 += 1; }
      }

      var mapper1: [0..<cnt1] int;
      var mapper2: [0..<cnt2] int;
      for i in 0..<n {
        if partitionArr[i] == 1 then mapper1[remap1[i]] = mapper[i];
        else                         mapper2[remap2[i]] = mapper[i];
      }

      var ec1 = 0; var ec2 = 0;
      for (u, v) in zip(src, dst) {
        if partitionArr[u] == 1 && partitionArr[v] == 1 then ec1 += 1;
        else if partitionArr[u] == 0 && partitionArr[v] == 0 then ec2 += 1;
      }

      var src1: [0..<ec1] int; var dst1: [0..<ec1] int;
      var src2: [0..<ec2] int; var dst2: [0..<ec2] int;
      var i1 = 0; var i2 = 0;
      for (u, v) in zip(src, dst) {
        if partitionArr[u] == 1 && partitionArr[v] == 1 {
          src1[i1] = remap1[u]; dst1[i1] = remap1[v]; i1 += 1;
        } else if partitionArr[u] == 0 && partitionArr[v] == 0 {
          src2[i2] = remap2[u]; dst2[i2] = remap2[v]; i2 += 1;
        }
      }

      // Recurse on each half. WCC: recurse directly.
      // CM: run Leiden, group by community (local indices), recurse per community.
      if cnt1 > postFilterMinSize && ec1 > 0 {
        if runClustering {
          var communities1: [0..<cnt1] int;
          var numComm1: int(64) = 0;
          numComm1 = c_computeLeiden(src1, dst1, ec1, cnt1, 1, 0.5, communities1, numComm1);
          var commCount1: [0..<numComm1] int;
          for v in 0..<cnt1 do commCount1[communities1[v]] += 1;
          var commStart1: [0..<numComm1+1] int;
          for i in 0..<numComm1 do commStart1[i+1] = commStart1[i] + commCount1[i];
          var commVertArr1: [0..<cnt1] int;
          var commPos1: [0..<numComm1] int;
          for i in 0..<numComm1 do commPos1[i] = commStart1[i];
          for v in 0..<cnt1 { commVertArr1[commPos1[communities1[v]]] = v; commPos1[communities1[v]] += 1; }
          var cr1: [0..<cnt1] int = -1;
          for c in 0..<numComm1 {
            if commCount1[c] == 0 then continue;
            const commSize1 = commCount1[c];
            if commSize1 <= postFilterMinSize then continue;
            const startPos1 = commStart1[c];
            var ri = 0;
            for si in startPos1..<startPos1+commSize1 { cr1[commVertArr1[si]] = ri; ri += 1; }
            var subMapper1: [0..<commSize1] int;
            for si in 0..<commSize1 do subMapper1[si] = mapper1[commVertArr1[startPos1+si]];
            var ec = 0;
            for (u, v) in zip(src1, dst1) do if cr1[u] != -1 && cr1[v] != -1 then ec += 1;
            if ec == 0 {
              for si in startPos1..<startPos1+commSize1 do cr1[commVertArr1[si]] = -1;
              continue;
            }
            var cS1: [0..<ec] int; var cD1: [0..<ec] int; var ei = 0;
            for (u, v) in zip(src1, dst1) {
              if cr1[u] != -1 && cr1[v] != -1 { cS1[ei] = cr1[u]; cD1[ei] = cr1[v]; ei += 1; }
            }
            for si in startPos1..<startPos1+commSize1 do cr1[commVertArr1[si]] = -1;
            var childRes = wellconnectednessRecursiveCheckerF(cS1, cD1, subMapper1, pId, depth+1);
            result.pushBack(childRes);
          }
        } else {
          var childRes1 = wellconnectednessRecursiveCheckerF(src1, dst1, mapper1, pId, depth+1);
          result.pushBack(childRes1);
        }
      }
      if cnt2 > postFilterMinSize && ec2 > 0 {
        if runClustering {
          var communities2: [0..<cnt2] int;
          var numComm2: int(64) = 0;
          numComm2 = c_computeLeiden(src2, dst2, ec2, cnt2, 1, 0.5, communities2, numComm2);
          var commCount2: [0..<numComm2] int;
          for v in 0..<cnt2 do commCount2[communities2[v]] += 1;
          var commStart2: [0..<numComm2+1] int;
          for i in 0..<numComm2 do commStart2[i+1] = commStart2[i] + commCount2[i];
          var commVertArr2: [0..<cnt2] int;
          var commPos2: [0..<numComm2] int;
          for i in 0..<numComm2 do commPos2[i] = commStart2[i];
          for v in 0..<cnt2 { commVertArr2[commPos2[communities2[v]]] = v; commPos2[communities2[v]] += 1; }
          var cr2: [0..<cnt2] int = -1;
          for c in 0..<numComm2 {
            if commCount2[c] == 0 then continue;
            const commSize2 = commCount2[c];
            if commSize2 <= postFilterMinSize then continue;
            const startPos2 = commStart2[c];
            var ri = 0;
            for si in startPos2..<startPos2+commSize2 { cr2[commVertArr2[si]] = ri; ri += 1; }
            var subMapper2: [0..<commSize2] int;
            for si in 0..<commSize2 do subMapper2[si] = mapper2[commVertArr2[startPos2+si]];
            var ec = 0;
            for (u, v) in zip(src2, dst2) do if cr2[u] != -1 && cr2[v] != -1 then ec += 1;
            if ec == 0 {
              for si in startPos2..<startPos2+commSize2 do cr2[commVertArr2[si]] = -1;
              continue;
            }
            var cS2: [0..<ec] int; var cD2: [0..<ec] int; var ei = 0;
            for (u, v) in zip(src2, dst2) {
              if cr2[u] != -1 && cr2[v] != -1 { cS2[ei] = cr2[u]; cD2[ei] = cr2[v]; ei += 1; }
            }
            for si in startPos2..<startPos2+commSize2 do cr2[commVertArr2[si]] = -1;
            var childRes = wellconnectednessRecursiveCheckerF(cS2, cD2, subMapper2, pId, depth+1);
            result.pushBack(childRes);
          }
        } else {
          var childRes2 = wellconnectednessRecursiveCheckerF(src2, dst2, mapper2, pId, depth+1);
          result.pushBack(childRes2);
        }
      }
      return result;
    } // end wellconnectednessRecursiveCheckerF

    // Shared-memory executor: load files on locale 0, process with forall.
    proc fromFilesSharedMemoryExecutor() throws {
      var timer: stopwatch;
      timer.start();

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
        var clusterNum = filepath.find("cluster_"):int;
        var (src, dst, mapper) = loadClusterFile(filepath);
        if src.size < 1 || mapper.size <= postFilterMinSize then continue;
        var result = wellconnectednessRecursiveCheckerF(src, dst, mapper, clusterNum, 0);
        allResults.pushBack(result);
      }
      outMsg = "%s took %r secs".format(analysisType, timer.elapsed());
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.restart();

      writeClustersToFileF(allResults, 0);
      outMsg = "Writing output took %r secs".format(timer.elapsed());
      wcLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.stop();
    } // end fromFilesSharedMemoryExecutor

    // Distributed executor: each locale owns a round-robin slice of files.
    proc fromFilesDistributedMemoryExecutor() throws {
      var timer: stopwatch;
      timer.start();

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
          var (src, dst, mapper) = loadClusterFile(filepath);
          if src.size < 1 || mapper.size <= postFilterMinSize then continue;
          var result = wellconnectednessRecursiveCheckerF(src, dst, mapper, clusterNum, 0);
          localResults.pushBack(result);
        }
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