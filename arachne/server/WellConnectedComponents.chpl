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
  use DistributedDeque;
  use CTypes;

  // Arachne modules.
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

  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string, outputType: string) throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG1 = toSymEntry(g1.getComp("NEIGHBORS_SET_SDI"), set(int)).a;
    
    var finalVertices = new list(int, parSafe=true);
    var finalClusters = new list(int, parSafe=true);
    var globalId:atomic int = 0;

    var clusterArrtemp = wcc(g1);
    writeln("**********************************************************we reached here");

    const ref  clusterArr = clusterArrtemp; //cluster id
    
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
          else writeln("originalNode which is not in graph: ", originalNode);
        }
      }
      reader.close();
      file.close();
      writeln("Number of clusters found: ", clusters.size);
      
      return clusters;
    }


 

    /* Returns the sorted and deduplicated edge list for a given set of vertices. */
    proc getEdgeList(ref vertices: set(int)) throws {
      // Initialize lists to collect edges
      var srcList = new list(int, parSafe=true);
      var dstList = new list(int, parSafe=true);

      // Map to assign new indices to vertices (mapper)
      var mapper = new map(int, int);
      var reverseMapper = new map(int, int); // For reverse mapping
      var idx = 0;
      for v in vertices {
        mapper[v] = idx;
        reverseMapper[idx] = v;
        idx += 1;
      }

      // Collect edges within the cluster
      for u in vertices {
        const ref neighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u + 1]];
        for v in neighbors {
          if mapper.contains(v) {
            srcList.pushBack(mapper[u]);
            dstList.pushBack(mapper[v]);
          }
        }
      }      

      // Convert lists to arrays
      var src = srcList.toArray();
      var dst = dstList.toArray();

      // Sort the edges
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);

      // Remove duplicate edges
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);

      // Create mapper array (original vertex IDs)
      var n = mapper.size;
      var mapperArray:[{0..<n}] int;

      for i in reverseMapper.keysToArray() {
        var originalV = reverseMapper[i];
        mapperArray[i] = originalV;
      }

      return (uniqueSrc, uniqueDst, mapperArray);
    }


   // Define a custom comparator record
    record TupleComparator {
        proc compare(a: (int, int), b: (int, int)) {
            if a(0) != b(0) then
                return a(0)-b(0);
            else
                return a(1)-b(1);
        }
    }
    /* Function to sort edge lists based on src and dst nodes */
    proc sortEdgeList(ref src: [] int, ref dst: [] int) {
      // Combine src and dst into a tuple array
      var edges: [0..<src.size] (int, int);
      for i in 0..<src.size do
        edges[i] = (src[i], dst[i]);

      var TupleComp: TupleComparator;

        // Sort the edges using the comparator
      sort(edges, comparator=TupleComp);
      // Extract sorted src and dst arrays
      var sortedSrc: [0..< src.size] int;
      var sortedDst: [0..< dst.size] int;
      for i in 0..<src.size {
        sortedSrc[i]= edges[i][0];
        sortedDst[i]= edges[i][1];
      }

      return (sortedSrc, sortedDst);
    }

        
    /* Function to remove duplicate edges from sorted edge lists */
    proc removeMultipleEdges(ref src: [] int, ref dst: [] int) {
      var uniqueSrc = new list(int);
      var uniqueDst = new list(int);

      if src.size == 0 then return (src, dst);

      uniqueSrc.pushBack(src[0]);
      uniqueDst.pushBack(dst[0]);

      for i in 1..<src.size {
        if src[i] != src[i - 1] || dst[i] != dst[i - 1] {
          uniqueSrc.pushBack(src[i]);
          uniqueDst.pushBack(dst[i]);
        }
      }

      // Convert lists to arrays
      var noDupsSrc = uniqueSrc.toArray();
      var noDupsDst = uniqueDst.toArray();

      return (noDupsSrc, noDupsDst);
    }




    /* Function to calculate the degree of a vertex within a component/cluster/community. */
    proc calculateClusterDegree(ref members: set(int), vertex: int) throws {
      const ref neighbors1 = neighborsSetGraphG1[vertex];
      var newWay = setIntersectionSize(neighbors1,members);

      return newWay;
    }
    /* Write out the clusters to a file. */
    //proc writeClustersToFile(ref membersA:set(int), id: int, depth: int, cut: int, ref mapper:[] int) throws {
    proc writeClustersToFile(ref membersA:set(int), id: int, depth: int, cut: int) throws {
        var filename = outputPath + "_" + id:string + "_" + depth:string + "_" + membersA.size:string + "_" + cut:string + ".txt";
        var file = open(filename, ioMode.cw);
        var fileWriter = file.writer(locking=false);
        var mappedArr = nodeMapGraphG1[membersA.toArray()];

        fileWriter.writeln("# cluster ID: " + id: string); 
        fileWriter.writeln("# cluster Depth: " + depth: string); 
        fileWriter.writeln("# number of members: " + membersA.size: string);
        fileWriter.writeln("# cutsize: " + cut: string);
        fileWriter.writeln("# members: " + mappedArr: string);
        
        try fileWriter.close();
        try file.close();
    }
    /* If given two lists with all vertices and cluster information, writes them out to file. */
    proc writeClustersToFile() throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(finalVertices, finalClusters) do writer.writeln(nodeMapGraphG1[v], " ", c);

      writer.close();
      outfile.close();
    }

    /* If given only vertices belonging to one cluster, writes them out to file. */
    proc writeClustersToFile(ref vertices: set(int), cluster:int) throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=true);

      for v in vertices do writer.writeln(nodeMapGraphG1[v], " ", cluster);

      writer.close();
      outfile.close();
    }

    proc removeDegOne(ref partition:set(int)): set(int) throws{
      if partition.size <= 1{
        var zeroset = new set(int);
        return zeroset;
      }
      //var keepedVertices:set(int, parSafe = true);
      var partitionToPass = partition;
      for v in partition {
        var memberDegree = calculateClusterDegree(partition, v);
        //writeln("Degree ",v," = ", memberDegree);
        if memberDegree < 2 {
          partitionToPass.remove(v);
        }
      }
      //writeln("removeDegOne called for: ",partition.size, " and it returned: ",partitionToPass.size );
      //writeln("partitionToPass: ",partitionToPass );
      return(partitionToPass);
    }
    /* Helper method to run the recursion. */
    /* Calls out to an external procedure that runs VieCut. */
    proc callMinCut(ref vertices: set(int), id: int, depth: int): list(int) throws {
      //writeln("///////////////////////callMinCut, received: ",vertices.size," vertices to CUT");
      var allWCC: list(int, parSafe=true);
      
      // If the vertices array is empty, do nothing and return an empty list
      if vertices.size < 2 {
        return allWCC;
      }

      var (src, dst, mapper) = getEdgeList(vertices);
      var n = mapper.size;
      var m = src.size;

      var partitionArr: [{0..<n}] int;
      var newSrc: [{0..<m}] int = src;
      var newDst: [{0..<m}] int = dst;
      var cut = c_computeMinCut(partitionArr, newSrc, newDst, n, m);

      var logN = floor(log10(vertices.size: real));
      var floorLog10N: int = logN:int;
      
      if cut > floorLog10N {// Check Well Connectedness
        allWCC.pushBack(id); //allWCC.pushBack(depth); allWCC.pushBack(vertices.size); allWCC.pushBack(cut);
        var currentId = globalId.fetchAdd(1);
        if outputType == "debug" then writeClustersToFile(vertices, id, depth, cut);
        else if outputType == "during" then writeClustersToFile(vertices, currentId);
        for v in vertices {
          finalVertices.pushBack(v);
          finalClusters.pushBack(currentId);
        }
        writeln("for cluster: ",id," in depth: ",depth," with cutsize: ", cut, " we found wcc. it has ",vertices.size," memebr!");
        return allWCC;
      }
      else{// Cluster is not WellConnected
        
        // Separate vertices into two partitions
        var cluster1, cluster2 = new set(int);
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.add(mapper[v]);
          else cluster2.add(mapper[v]);
        }


        var newSubClusters: list(int, parSafe=true);
        
        // The partition size must be greater than 1, to be meaningful passing it to VieCut.
        if cluster1.size >1 {
          var inPartition = removeDegOne(cluster1);
          newSubClusters = callMinCut(inPartition, id, depth+1);
        }
        if cluster2.size >1 {
          var outPartition = removeDegOne(cluster2);
          newSubClusters = callMinCut(outPartition, id, depth+1);
        }
        
        for findings in newSubClusters do allWCC.pushBack(findings);
      }
      return allWCC;
    }
    // TO OLIVER:
    /* Core 2 Decomposition. For some reasons that you know we didn't use it!*/
    proc clusterC2D(ref clusterNodes: set(int)): set(int) throws{
      // Create a copy of the input set to work with. Oliver is it a ref or copy?
      var coreMembers = clusterNodes;
      var coreDomain: domain(int, parSafe=true);
      
      for elem in coreMembers {
        coreDomain.add(elem);
      }

      // Map from vertex id to its degree within the cluster
      var degrees: [coreDomain] atomic int;

      // List of nodes with degree less than 2 to be removed
      var nodesToRemove = new list(int);

      // Initialize degrees and nodesToRemove
      forall vertex in coreMembers with (ref degrees, ref nodesToRemove, ref coreMembers) {
        degrees[vertex].write(calculateClusterDegree(coreMembers, vertex));
        if degrees[vertex].read() < 2 {
          nodesToRemove.pushBack(vertex);
        }
      }
      writeln("degrees: ", degrees);
      writeln("degrees.domain: ", degrees.domain);
      writeln("before while nodesToRemove: ", nodesToRemove);
      // Iteratively remove nodes with degree less than 2
      while !nodesToRemove.isEmpty() {
        // Collect node to be processed in this iteration
        var currentNodesToRemove = nodesToRemove.popBack();
        const ref neighbors = dstNodesG1[segGraphG1[currentNodesToRemove]..<segGraphG1[currentNodesToRemove+1]];
        writeln("currentNodesToRemove: ", currentNodesToRemove);
        writeln("it's neighbours: ", neighbors);

        for u in clusterNodes {
          if neighbors.find(u) != -1 && degrees[u].read() >= 2 {
            // update degrees
            degrees[u].sub(1);
            if degrees[u].read() < 2 then nodesToRemove.pushBack(u);
          }
        }
        // Mark currentNodesToRemove as removed.
        writeln("currentNodesToRemove checked: ", currentNodesToRemove);
        degrees[currentNodesToRemove].write(-1);
      }

      // Step 4: Collect nodes with degrees >= 2 and update cluster
      var newMembers = new set(int);
      for v in degrees.domain {
        if degrees[v].read() >= 2 {
          newMembers.add(v);
        }
      }
      writeln("core2Decomposition returned cluster with size:",newMembers.size);
      writeln("core2Decomposition returned cluster with size:",newMembers);
      return newMembers;
    }


    /* Kick off well-connected components. */
    proc wcc(g1: SegGraph): [] int throws {
      writeln("Graph loaded. It has: ", g1.n_vertices," vertices and ", g1.n_edges, " edges.");
      
      var results: list(int, parSafe=true);
      var originalClusters = readClustersFile(inputcluster_filePath);
      writeln("reading Clusters' File finished.");



      var newClusterIds: chpl__processorAtomicType(int) = 0;
      var newClusters = new map(int, set(int));
      
      // Sequential for now since connected components is highly parallel.
      for key in originalClusters.keysToArray() {
        var (src, dst, mapper) = getEdgeList(originalClusters[key]);
        // writeln("Checking original cluster ", key, " for multiple connected components.");
        if src.size > 0 { // if no edges were generated, then do not process this component.
          // Generate edges with 0-based vertex indices for connected components.
          var (arachneSrc, arachneDst, arachneMapper) = oneUpper(src, dst);

          // Generate the segments for the newly generated cluster graph.
          var (srcUnique, srcCounts) = uniqueFromSorted(arachneSrc);
          var srcCumulativeCounts = + scan srcCounts;
          var segments = makeDistArray(srcCounts.size + 1, int);
          segments[0] = 0;
          segments[1..] = srcCumulativeCounts;

          // Call connected components and decide if multiple connected components exist or not.
          var components = connectedComponents(arachneSrc, arachneDst, srcCounts.size);
          var multipleComponents:bool = false;
          for c in components do if c != 0 { multipleComponents = true; break; }
          
          // Add each vertex in each connected component to its own cluster, or just add the whole
          // cluster if it is composed of only one connected component.
          // writeln("multipleComponents = ", multipleComponents);
          if multipleComponents {
            var tempMap = new map(int, set(int));
            for (c,v) in zip(components,components.domain) {
              if tempMap.contains(c) then tempMap[c].add(arachneMapper[v]);
              else {
                var s = new set(int);
                s.add(arachneMapper[v]);
                tempMap[c] = s;
              }
            }
            for c in tempMap.keys() do newClusters[newClusterIds.fetchAdd(1)] = tempMap[c];
            writeln("Original cluster ", key, " was split up into ", tempMap.size, " clusters.");
          } else newClusters[newClusterIds.fetchAdd(1)] = originalClusters[key];
        }
      }
      writeln("New number of clusters is ", newClusters.size);
      writeln();
      writeln();
      writeln();

      for key in newClusters.keysToArray() {
      // forall key in newClusters.keysToArray() with (ref results, ref newClusters) {
        ref clusterToAdd = newClusters[key];
        writeln("Cluster ", key, ": ", clusterToAdd.size," vertices.");
        if clusterToAdd.size > 1 { // The cluster is not a singleton.
          var newResults:list(int, parSafe=true);
          newResults = callMinCut(clusterToAdd, key, 0); 
          for mapping in newResults do results.pushBack(mapping);
        }
        writeln();
      }
      var subClusterArrToReturn: [0..#results.size] int;
      subClusterArrToReturn = results.toArray();

      if outputType == "post" then writeClustersToFile();

      return subClusterArrToReturn;
    } // end of wcc
    
    return clusterArr;
  } // end of runWCC
} // end of WellConnectedComponents module