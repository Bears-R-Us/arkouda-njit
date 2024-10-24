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
    //writeln("size.read(): ", size.read());
    return size.read();
  }

  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string, outputType: string, functionType: string) throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG1 = toSymEntry(g1.getComp("NEIGHBORS_SET_SDI"), set(int)).a;
    
    var finalVertices = new list(int, parSafe=true);
    var finalClusters = new list(int, parSafe=true);
    var globalId:atomic int = 0;
    var functionTypePassed = if functionType != "none" then functionType:int else 10;
    
    var clusterArrtemp = wcc(g1);
    //writeln("**********************************************************we reached here");
    //writeln("functionTypePassed:", functionTypePassed);
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
          // if clusterID == 557{
          //   // writeln("originalNode(",originalNode,")", "mapped to:",idx );
          // }
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
      // writeln("Number of clusters found: ", clusters.size);
      
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
      // // Collect edges within the cluster
      // forall u in vertices with (ref srcList, ref dstList) {
      //   const ref neighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u + 1]];
      //   forall v in neighbors with (ref srcList, ref dstList){
      //     if mapper.contains(v) {
      //       srcList.pushBack(mapper[u]);
      //       dstList.pushBack(mapper[v]);
      //     }
      //   }
      // }
      // Convert lists to arrays
      var src = srcList.toArray();
      var dst = dstList.toArray();

      // Sort the edges
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);

      // Remove duplicate edges
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);

      // Create mapper array (original vertex IDs)
      var n = mapper.size;
      var mapperArray:[0..n - 1] int;

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
        var filename = outputPath + "/cluster_" + id:string + "_" + depth:string + "_" + membersA.size:string + "_" + cut:string + ".debugging";
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
      var filename = outputPath + "/cluster_"+".post";
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(finalVertices, finalClusters) do writer.writeln(nodeMapGraphG1[v], " ", c);

      writer.close();
      outfile.close();
    }

    /* If given only vertices belonging to one cluster, writes them out to file. */
    proc writeClustersToFile(ref vertices: set(int), cluster:int) throws {
      var filename = outputPath + "/cluster_"+".during";
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
      var partitionToPass = partition;
      for v in partition {
        var memberDegree = calculateClusterDegree(partition, v);
        if memberDegree < 2 {
          partitionToPass.remove(v);
        }
      }
      return(partitionToPass);
    }
    /* Helper method to run the recursion. */
    /* Calls out to an external procedure that runs VieCut. */
    proc callMinCut(ref vertices: set(int), id: int, depth: int): list(int) throws {
      //writeln("///////////////////////callMinCut, received: ",vertices.size," vertices to CUT");
      var allWCC: list(int, parSafe=true);
      
      // If the vertices array is empty, do nothing and return an empty list
      //TO OLIVER: I think it should be changed to 11 too
      //if vertices.size < 2 {
      if vertices.size < 1 {
        return allWCC;
      }
      //Viecut intializing
      var (src, dst, mapper) = getEdgeList(vertices);
      var n = mapper.size;
      var m = src.size;
      var partitionArr: [{0..<n}] int;

      // Call the external min-cut function
      var cut = c_computeMinCut(partitionArr, src, dst, n, m);

      var functionCriteria: int = 0;
      
      if functionTypePassed == 1 {
        var funcret = floor(0.01 * (vertices.size));
        functionCriteria = funcret:int;
      } 

      if functionTypePassed == 5 {
        var funcret = floor(sqrt(vertices.size:real)/5);
        functionCriteria = funcret:int;
      } 

      if functionTypePassed == 10 {
        var logN = floor(log10(vertices.size: real));
        functionCriteria = logN:int;
      }      
      
      if functionTypePassed == 2 {
        var logN = floor(log2(vertices.size: real));
        functionCriteria = logN:int;
      }

      if cut > functionCriteria {// Check Well Connectedness
        allWCC.pushBack(id); //allWCC.pushBack(depth); allWCC.pushBack(vertices.size); allWCC.pushBack(cut);
        var currentId = globalId.fetchAdd(1);
        if outputType == "debug" then writeClustersToFile(vertices, id, depth, cut);
        else if outputType == "during" then writeClustersToFile(vertices, currentId);
        for v in vertices {
          finalVertices.pushBack(v);
          finalClusters.pushBack(currentId);
        }
        return allWCC;
      }
      else{// Cluster is not WellConnected
        
        var cluster1, cluster2 = new set(int);
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.add(mapper[v]);
          else cluster2.add(mapper[v]);
        }

        var newSubClusters: list(int, parSafe=true);
        
        // The partition size must be greater than 1, to be meaningful passing it to VieCut.
        //--------> TO OLIVER: The partition size must be greater than 11, George SAID ON SLACK.
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
 
    /* Kick off well-connected components. */
    proc wcc(g1: SegGraph): [] int throws {
      
      writeln("Graph loaded. It has: ",g1.n_vertices," vertices and ",g1.n_edges, ".");
      
      var results: list(int, parSafe=true);
      var clusters = readClustersFile(inputcluster_filePath);
      writeln("reading Clusters' File finished.");
      forall key in clusters.keysToArray() with (ref results, ref clusters) {
        ref clusterToAdd = clusters[key];
        /*
        TO OLIVER: I changed my mind and commented this because there is a chance that at the first step we find
        a well connected cluster. PLEASE check the Min's code and MY STATEMENT on slack.
        //var clusterSetInit1 = removeDegOne(clusterToAdd);
        */
          //based on George
        if clusterToAdd.size > 1{ // The cluster is not a singleton.
          
          writeln("*-*-*-*-*-*-*-*-*-*-*-*-*-*");
          writeln("selected Cluster is:", key, " members are:",clusterToAdd );
          //To Oliver: I did it because of the warnings!
          var newResults:list(int, parSafe=true);
          newResults = callMinCut(clusterToAdd, key, 0); 
          for mapping in newResults do results.pushBack(mapping);
        }
      }
        var subClusterArrToReturn: [0..#results.size] int;
        subClusterArrToReturn = results.toArray();
        
        //To Oliver: I know it is expensive but I did it for my tests. We don't need it. Do we?
        sort(subClusterArrToReturn);
        if outputType == "post" then writeClustersToFile();

        return subClusterArrToReturn;
      } // end of wcc
    
    return clusterArr;
  } // end of runWCC
} // end of WellConnectedComponents module