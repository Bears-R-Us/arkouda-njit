module WellConnectedComponentsDistributed {
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

  // Arachne modules.
  import WellConnectedComponentsMsg.wccLogger;
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

  /* Define a custom tuple comparator. */
  record TupleComparator {
    proc compare(a: (int, int), b: (int, int)) {
      if a(0) != b(0) then return a(0)-b(0);
      else return a(1)-b(1);
    }
  }

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

  proc runWCCDistributed(g1: SegGraph, st: borrowed SymTab, 
                         inputcluster_filePath: string, outputPath: string,
                         connectednessCriterion: string, connectednessCriterionMultValue: real, 
                         preFilterMinSize: int, postFilterMinSize: int): int throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG1 = toSymEntry(g1.getComp("NEIGHBORS_SET_SDI"), set(int)).a;

    // Make block-distributed domain where each locale will own an index of the distributed array.
    var localeDom = blockDist.createDomain(0..<numLocales);
    var finalVerticesDistributed: [localeDom][{0..<1}] list(int, parSafe=true);
    var finalClustersDistributed: [localeDom][{0..<1}] list(int, parSafe=true);
    var globalIdDistributed: [localeDom][{0..<1}] chpl__processorAtomicType(int);
    coforall loc in Locales do on loc { globalIdDistributed[loc.id][0].write(1); }

    // Make locale 0 versions of finalVertices and finalClusters for output.
    var finalDom = {0..1};
    var finalVertices: [finalDom] int;
    var finalClusters: [finalDom] int;
    
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
      var srcList = new list(int, parSafe=true);
      var dstList = new list(int, parSafe=true);

      var v2idx = new map(int, int);
      var idx2v = vertices.toArray();
      sort(idx2v);

      for (v,idx) in zip(idx2v, idx2v.domain) do v2idx[v] = idx;

      // Gather the edges of the subgraph induced by the given vertices.
      for u in vertices {
        var start = segGraphG1[u];
        var end = segGraphG1[u+1];
        var neighbors: [0..<end-start] int;
        forall (i,s) in zip(neighbors.domain, start..<end) with (var agg = new SrcAggregator(int)) {
          agg.copy(neighbors[i], dstNodesG1[s]);
        }
        forall v in neighbors with (ref srcList, ref dstList, ref v2idx) {
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

    /* Similar to above, but we can assume src and dst already contain a subset of vertices. */
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

      // Sort the redges and remove any multiples if they exist.
      // TODO: Do we actually need to sort and remove multiple edges? If the input graph is simple, 
      //       wouldn't any induced subgraphs also be simple?
      var (sortedSrc, sortedDst) = sortEdgeList(newSrc, newDst);
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
    proc writeClustersToFile() throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(finalVertices, finalClusters) do writer.writeln(nodeMapGraphG1[v], " ", c);

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

    /* Recursive method that processes a given set of vertices (partition), denotes if it is 
       well-connected or not, and if not calls itself on the new generated partitions. */
    proc wccRecursiveChecker(ref vertices, ref src, ref dst, ref mapper, id: int, depth: int) throws {
      // If the generated edge list is empty, then return.
      if src.size < 1 then return;

      var n = mapper.size;
      var m = src.size;

      var partitionArr: [{0..<n}] int;
      var cut = c_computeMinCut(partitionArr, src, dst, n, m);

      var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue):int;
      if cut > criterionValue { // Cluster is well-connected.
        var localeId = here.id;
        var nextId = globalIdDistributed[localeId][0].fetchAdd(1);
        var tempId = nextId:string + localeId:string;
        var currentId = tempId:int;
        for v in vertices {
          finalVerticesDistributed[localeId][0].pushBack(v);
          finalClustersDistributed[localeId][0].pushBack(currentId);
        }
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " with depth " + depth:string + " and cutsize " 
                    + cut:string + " is well-connected with " + vertices.size:string + " vertices.";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        return;
      }
      else { // Cluster is not well-connected.
        var cluster1, cluster2 = new set(int);
        
        // Separate vertices into two partitions.
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.add(mapper[v]);
          else cluster2.add(mapper[v]);
        }

        // Convert src and dst to original vertex names.
        for (u,v,i) in zip(src,dst,src.domain) {
          src[i] = mapper[u];
          dst[i] = mapper[v];
        }
        
        // Make sure the partitions meet the minimum size denoted by postFilterMinSize.
        if cluster1.size > postFilterMinSize {
          var (cluster1Src, cluster1Dst, cluster1Mapper) = getEdgeList(cluster1, src, dst);
          wccRecursiveChecker(cluster1, cluster1Src, cluster1Dst, cluster1Mapper, id, depth+1);
        }
        if cluster2.size > postFilterMinSize {
          var (cluster2Src, cluster2Dst, cluster2Mapper) = getEdgeList(cluster2, src, dst);
          wccRecursiveChecker(cluster2, cluster2Src, cluster2Dst, cluster2Mapper, id, depth+1);
        }
      }
      return;
    }

    /* Main executing function for well-connected components. */
    proc wcc(g1: SegGraph): int throws {
      var outMsg = "Graph loaded with " + g1.n_vertices:string + " vertices and " 
                 + g1.n_edges:string + " edges.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      var originalClusters = readClustersFile(inputcluster_filePath);
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),
                     "Reading clusters file finished.");

      // Make block-distributed arrays to store clusters across locales.
      var originalClustersDistributed: [localeDom][{0..<1}] map(int, set(int));
      var newClustersDistributed: [localeDom][{0..<1}] map(int, set(int));
      var newClusterIdToOriginalClusterIdDistributed: [localeDom][{0..<1}] map(int, int);

      // Transfer the data from locale 0 to the distributed cluster map.
      if logLevel == LogLevel.DEBUG then startCommDiagnostics();
      for (clusterId,clusterVertices) in zip(originalClusters.keys(),originalClusters.values()) {
        const targetLocale = clusterId % numLocales;
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Moving cluster " + clusterId:string + " to locale " + targetLocale:string + 
                       ".";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        on Locales[targetLocale] {
          originalClustersDistributed[targetLocale][0].add(clusterId,clusterVertices);
        }
      }
      if logLevel == LogLevel.DEBUG {
        var outMsg = "Communication statistics transfering components for locale 0 to all others.";
        wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        printCommDiagnosticsTable();
        resetCommDiagnostics();
      }
      
      // NOTE: The parallelization is across locales, but work within the locales is sequential.
      //
      // NOTE: Sequential for now since connected components is highly parallel. We need to discuss
      //       the tradeoff if it is more important to run connected components on the original
      //       clusters in parallel or run connected components in parallel.
      //
      // NOTE: This is probably not even needed here. We could add a pre-filtering step to run this
      //       during graph construction or as a totally separate process instead of here.
      if logLevel == LogLevel.DEBUG then startCommDiagnostics();
      coforall loc in Locales do on loc {
        var originalClusters = originalClustersDistributed[loc.id][0];
        var newClusterIds: atomic int = 1;
        for key in originalClusters.keysToArray() {
          var (src, dst, mapper) = getEdgeList(originalClusters[key]);
          if src.size > 0 { // If no edges were generated, then do not process this component.
            // Call connected components and decide if multiple connected components exist or not.
            var components = connectedComponentsLocal(src, dst, mapper.size);
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
                var nextId = newClusterIds.fetchAdd(1);
                var tempId = nextId:string + loc.id:string;
                var newId = tempId:int;
                if tempMap[c].size > preFilterMinSize {
                  newClustersDistributed[loc.id][0][newId] = tempMap[c];
                  newClusterIdToOriginalClusterIdDistributed[loc.id][0].add(newId,key);
                }
              }
              if logLevel == LogLevel.DEBUG {
                var outMsg = "Original cluster " + key:string + " processed on locale " + 
                             loc.id:string + " was split up into " + tempMap.size:string + 
                             " clusters.";
                wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
              }
            } else {
                if logLevel == LogLevel.DEBUG {
                  var outMsg = "Cluster " + key:string + " processed on locale " + loc.id:string + 
                               " was NOT split up into multiple clusters.";
                  wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                }
              if originalClusters[key].size > preFilterMinSize {
                var nextId = newClusterIds.fetchAdd(1);
                var tempId = nextId:string + loc.id:string;
                var newId = tempId:int;
                newClustersDistributed[loc.id][0][newId] = originalClusters[key];
                newClusterIdToOriginalClusterIdDistributed[loc.id][0].add(newId,key);
              }
            }
          }
        }
      }
      if logLevel == LogLevel.DEBUG {
        var outMsg = "Communication statistics for initial CC run on all clusters.";
        wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        printCommDiagnosticsTable();
        resetCommDiagnostics();
      }

      // Reduce all distributed new cluster amounts. 
      var newClusterAmount:atomic int = 0;
      coforall loc in Locales with (ref newClusterAmount) do on loc {
        newClusterAmount.add(newClustersDistributed[loc.id][0].size);
      }
      if logLevel == LogLevel.DEBUG {
        var outMsg = "Communication statistics for reducing distributed new cluster amounts.";
        wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        printCommDiagnosticsTable();
        resetCommDiagnostics();
      }

      // Reduce from distributed arrays new cluster ID to original cluster ID to array on locale 0.
      if logLevel == LogLevel.DEBUG {
        for m in newClusterIdToOriginalClusterIdDistributed {
          newClusterIdToOriginalClusterId.extend(m[0]);
        }
        var outMsg = "Communication statistics for reducing new to old cluster ID maps.";
        wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        printCommDiagnosticsTable();
        resetCommDiagnostics();
      }

      outMsg = "Splitting up clusters yielded " + newClusterAmount.read():string + " new clusters.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      // Process the new clusters on the locales they live in.
      coforall loc in Locales do on loc {
        var newClusters = newClustersDistributed[loc.id][0];
        forall key in newClusters.keysToArray() with (ref newClusters) {
          ref clusterToAdd = newClusters[key];
          if logLevel == LogLevel.DEBUG {
            var outMsg = "Processing cluster " + key:string + " which is a subcluster of " 
                      + newClusterIdToOriginalClusterIdDistributed[loc.id][0][key]:string + 
                      " on locale " + loc.id:string + ".";
            wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          }
          var (src, dst, mapper) = getEdgeList(clusterToAdd);
          wccRecursiveChecker(clusterToAdd, src, dst, mapper, key, 0);
        }
      }
      if logLevel == LogLevel.DEBUG {
        var outMsg = "Communication statistics for wccRecursiveChecker.";
        wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        printCommDiagnosticsTable();
        resetCommDiagnostics();
      }

      // Get how many vertices were finally kept after running WCC.
      var finalNumVertices: [{0..<numLocales}] int = 0;
      coforall loc in Locales do on loc { 
        finalNumVertices[loc.id] = finalVerticesDistributed[loc.id][0].size;
      }
      var finalNumVerticesScan = + scan finalNumVertices;
      var finalOffsets: [{0..finalNumVerticesScan.size}] int;
      finalOffsets[0] = 0;
      finalOffsets[1..] = finalNumVerticesScan;

      // Resize our locale 0 array that will write out based on the above information.
      var finalTotalVertices = + reduce finalNumVertices;
      finalDom = {0..<finalTotalVertices};
      coforall loc in Locales do on loc { // Transfer data from locales to locale 0 array.
        var localRange = 0..<finalVerticesDistributed[loc.id][0].size;
        var toRange = finalOffsets[loc.id]..<finalOffsets[loc.id+1];
        forall (l,t) in zip(localRange, toRange) with (var agg = new DstAggregator(int)) {
          agg.copy(finalVertices[t], finalVerticesDistributed[loc.id][0][l]);
          agg.copy(finalClusters[t], finalClustersDistributed[loc.id][0][l]);
        }
      }

      // Modify the cluster labels to start from 0.
      var tempSet = new set(int, parSafe=true);
      forall c in finalClusters with (ref tempSet) do tempSet.add(c);
      var idx2c = tempSet.toArray();
      var c2idx = new map(int, int, parSafe=true);
      sort(idx2c);
      forall (c,idx) in zip(idx2c, idx2c.domain) with (ref c2idx) do c2idx.add(c,idx);
      forall (c,idx) in zip(finalClusters, 0..<finalClusters.size) with (ref finalClusters) do
        finalClusters[idx] = c2idx[c];
      if logLevel == LogLevel.DEBUG {
        var outMsg = "Communication statistics for reducing final vertices and clusters.";
        wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        printCommDiagnosticsTable();
        resetCommDiagnostics();
      }

      writeClustersToFile();
      if logLevel == LogLevel.DEBUG {
        var outMsg = "Communication statistics for writing out file with post.";
        wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        printCommDiagnosticsTable();
        resetCommDiagnostics();
      }
      
      outMsg = "WCC found " + tempSet.size:string + " clusters to be well-connected.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      if logLevel == LogLevel.DEBUG then stopCommDiagnostics();
      if logLevel == LogLevel.DEBUG then resetCommDiagnostics();
      return tempSet.size;
    } // end of wcc
    
    var numClusters = wcc(g1);
    return numClusters;
  } // end of runWCCDistributed
} // end of WellConnectedComponentsDistributed module