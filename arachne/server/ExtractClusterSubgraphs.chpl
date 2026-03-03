module ExtractClusterSubgraphs {
  // Chapel modules.
  use ReplicatedDist;
  use CopyAggregation;
  use Reflection;
  use Map;
  use List;
  use Set;
  use IO;
  use Time;
  use Sort;
  use Search;
  import ChplConfig;
 
  // Arachne modules.
  import ExtractClusterSubgraphsMsg.ecsLogger;
  use BuildGraph;
  use GraphArray;
 
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerConfig;
  use Logging;
 
  // At compile-time pick distributed or shared-memory execution.
  private param oneLocale = if ChplConfig.CHPL_COMM == "none" then true else false;
 
  /* Define a custom tuple comparator. */
  record TupleComparator {
    proc compare(a: (int, int), b: (int, int)) {
      if a(0) != b(0) then return a(0)-b(0);
      else return a(1)-b(1);
    }
  }
 
  /* Extracts induced subgraph edge lists per cluster and writes each to its own file. */
  proc runExtractClusterSubgraphs(G: SegGraph, st: borrowed SymTab,
                                   inputClustersFilePath: string,
                                   outputFolder: string): int throws {
    // Extract graph structural data as distributed arrays.
    var srcNodesG_dist     = toSymEntry(G.getComp("SRC_SDI"),        int).a;
    var dstNodesG_dist     = toSymEntry(G.getComp("DST_SDI"),        int).a;
    var segGraphG_dist     = toSymEntry(G.getComp("SEGMENTS_SDI"),   int).a;
    var nodeMapGraphG_dist = toSymEntry(G.getComp("VERTEX_MAP_SDI"), int).a;
 
    // Gather global sizes of distributed graph components.
    const srcCount     = srcNodesG_dist.size;
    const segCount     = segGraphG_dist.size;
    const nodeMapCount = nodeMapGraphG_dist.size;
 
    // Define replicated domains so each locale holds the full index space.
    const repSrcDom     = {0..<srcCount}     dmapped new replicatedDist();
    const repSegDom     = {0..<segCount}     dmapped new replicatedDist();
    const repNodeMapDom = {0..<nodeMapCount} dmapped new replicatedDist();
 
    // Fully replicated graph arrays (local copy on every locale).
    var srcNodesG     : [repSrcDom]     int;
    var dstNodesG     : [repSrcDom]     int;
    var segGraphG     : [repSegDom]     int;
    var nodeMapGraphG : [repNodeMapDom] int;
 
    // STEP 1: Build full arrays on Locale 0 ONLY.
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
 
    // STEP 2: Broadcast locale 0 replicand to ALL locales.
    coforall loc in Locales do on loc {
      if here.id != 0 {
        srcNodesG.replicand(here) = srcNodesG.replicand(Locales[0]);
        dstNodesG.replicand(here) = dstNodesG.replicand(Locales[0]);
        segGraphG.replicand(here) = segGraphG.replicand(Locales[0]);
        nodeMapGraphG.replicand(here) = nodeMapGraphG.replicand(Locales[0]);
      }
    }
 
    // Distributed array: each element is a locale-local cluster map.
    var clustersMap = makeDistArray(numLocales, map(int, set(int)));
 
    /* Reads tab-delimited "originalNode clusterID" file. Each locale reads
       independently and keeps only clusters where clusterID % numLocales == here.id.
       Uses the local replica of nodeMapGraphG for binary search. */
    proc readClustersFile(filename: string) throws {
      coforall loc in Locales do on loc {
        const myId = here.id;
        var localNodeMap: [{0..<nodeMapGraphG.size}] int;
        localNodeMap = nodeMapGraphG;
 
        var file   = open(filename, ioMode.r);
        var reader = file.reader(locking=false);
        var originalNode, clusterID: int;
 
        while reader.read(originalNode, clusterID) {
          if (clusterID % numLocales) != myId then continue;
 
          const (found, idx) = binarySearch(localNodeMap, originalNode);
          if !found then continue;
 
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
 
    /* Sort an edge list by (src, dst). */
    proc sortEdgeList(ref src: [] int, ref dst: [] int) {
      var edges: [0..<src.size] (int, int);
      for i in 0..<src.size do edges[i] = (src[i], dst[i]);
      var TupleComp: TupleComparator;
      sort(edges, comparator=TupleComp);
      var sortedSrc: [0..<src.size] int;
      var sortedDst: [0..<dst.size] int;
      for i in 0..<src.size {
        sortedSrc[i] = edges[i][0];
        sortedDst[i] = edges[i][1];
      }
      return (sortedSrc, sortedDst);
    }
 
    /* Remove duplicate (src, dst) pairs from a sorted edge list. */
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
      return (uniqueSrc.toArray(), uniqueDst.toArray());
    }
 
    /* Returns the induced subgraph edge list for a set of internal vertex IDs.
       segGraph[u]..segGraph[u+1]-1 indexes the neighbors of u in dstNodes.
       Returns (uniqueSrc, uniqueDst, idx2v) where idx2v[localIdx] = internalIdx. */
    proc getEdgeList(ref vertices: set(int), ref srcNodes: [] int,
                     ref dstNodes: [] int, ref segGraph: [] int) throws {
      var srcList = new list(int);
      var dstList = new list(int);
      var v2idx   = new map(int, int);
      var idx2v   = vertices.toArray();
      sort(idx2v);
      for (v, idx) in zip(idx2v, idx2v.domain) do v2idx[v] = idx;
 
      for u in vertices {
        const startIdx = segGraph[u];
        const endIdx   = segGraph[u + 1];
        for i in startIdx..<endIdx {
          const v = dstNodes[i];
          if v2idx.contains(v) {
            srcList.pushBack(v2idx[u]);
            dstList.pushBack(v2idx[v]);
          }
        }
      }
 
      var src = srcList.toArray();
      var dst = dstList.toArray();
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);
      return (uniqueSrc, uniqueDst, idx2v);
    }
 
    /* Writes the induced subgraph of each cluster in myMap to its own
       <outputFolder>cluster_<id>.tsv file using original node IDs. */
    proc writeClusterFiles(ref myMap: map(int, set(int)),
                           ref srcNodes: [] int, ref dstNodes: [] int,
                           ref segGraph: [] int, ref nodeMap: [] int): int throws {
                          
      var clusterIds = myMap.keysToArray();
      forall clusterID in clusterIds with (ref myMap) {
        ref vertices = myMap[clusterID];
        if vertices.size < 2 then continue;
        var (subSrc, subDst, mapper) = getEdgeList(vertices, srcNodes, dstNodes, segGraph);
 
        const filename = outputFolder + "cluster_" + clusterID:string + ".tsv";
        var outfile = open(filename, ioMode.cw);
        var writer  = outfile.writer(locking=false);
 
        // mapper[localIdx] = internalIdx; nodeMap[internalIdx] = originalID
        for (u, v) in zip(subSrc, subDst) do
          writer.writeln(nodeMap[mapper[u]], "\t", nodeMap[mapper[v]]);
 
        writer.close();
        outfile.close();
 
        if logLevel == LogLevel.DEBUG {
          var outMsg = "cluster_%i.tsv: %i vertices, %i edges"
                       .format(clusterID, vertices.size, subSrc.size);
          ecsLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
        }
      }
      return clusterIds.size;
    }
 
    /* Shared-memory executor: all clusters live on locale 0. */
    proc extractSharedMemoryExecutor(): int throws {
      var outMsg = "Extracting cluster subgraphs: graph has %i vertices and %i edges"
                   .format(G.n_vertices, G.n_edges);
      ecsLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      var timer: stopwatch;
 
      timer.start();
      readClustersFile(inputClustersFilePath);
      var localMap = clustersMap[0];
      outMsg = "Reading %i clusters took %r secs".format(localMap.size, timer.elapsed());
      ecsLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.restart();
 
      var numWritten = writeClusterFiles(localMap, srcNodesG, dstNodesG, segGraphG, nodeMapGraphG);
      outMsg = "Writing %i cluster files took %r secs".format(numWritten, timer.elapsed());
      ecsLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.stop();
 
      return numWritten;
    }
 
    /* Distributed-memory executor: each locale owns clusters where
       clusterID % numLocales == here.id, matching readClustersFile ownership. */
    proc extractDistributedMemoryExecutor(): int throws {
      var outMsg = "Extracting cluster subgraphs: graph has %i vertices and %i edges"
                   .format(G.n_vertices, G.n_edges);
      ecsLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      var timer: stopwatch;
 
      timer.start();
      readClustersFile(inputClustersFilePath);
      outMsg = "Reading clusters took %r secs".format(timer.elapsed());
      ecsLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.restart();
 
      var perLocaleCount = makeDistArray(numLocales, int);
 
      coforall loc in Locales do on loc {
        ref localMap = clustersMap[loc.id];
        ref localSrc = srcNodesG;
        ref localDst = dstNodesG;
        ref localSeg = segGraphG;
        ref localNodeMap = nodeMapGraphG;
 
        perLocaleCount[loc.id] = writeClusterFiles(localMap, localSrc, localDst,
                                                   localSeg, localNodeMap);
      }
 
      var numWritten = 0;
      for c in perLocaleCount do numWritten += c;
 
      outMsg = "Writing %i cluster files took %r secs".format(numWritten, timer.elapsed());
      ecsLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
      timer.stop();
 
      return numWritten;
    }
 
    var numClusters: int;
    if oneLocale then numClusters = extractSharedMemoryExecutor();
    else              numClusters = extractDistributedMemoryExecutor();
 
    var outMsg = "extractClusterSubgraphs wrote %i cluster files to %s"
                 .format(numClusters, outputFolder);
    ecsLogger.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
 
    return numClusters;
  }
}