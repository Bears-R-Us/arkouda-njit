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

  class Cluster {
    var id: int;                  // Cluster identifier.
    var n_members: int;           // Cluster size.       
    var isWcc: bool;              // Is it a well-connected cluster?
    var isSingleton: bool;        // Is it a singleton cluster?
    var depth: int;               // Cluster depth;
    var averageDegree: real;      // Cluster averageDegree;
    var membersD: domain(1);      // Members domain.
    var membersA: [membersD] int; // Members array.

    /* Cluster initializer from array. */
    proc init(members: [?D] int, id:int) {
      this.id = id;
      this.n_members = members.size;
      this.isWcc = false;
      if this.n_members <= 1 then this.isSingleton = true;
      this.depth = 0;
      //this.averageDegree = 0.0;
      this.membersD = D;
      this.membersA = members;
      sort(this.membersA);
    }

    /* Given a cluster and a cut size, determine if it is well-connected or not. */
    proc isWellConnected(edgeCutSize: int): bool throws {
      var logN = floor(log10(this.n_members: real));
      var floorLog10N: int = logN:int;
      
      if edgeCutSize > floorLog10N {
        this.isWcc = true;
        return true;
      }

      return false;
    }



 
    /* Method to print all details of the Cluster object. */
    proc printClusterInfo() {
      writeln("///////////////////////////////////////");
      writeln("Cluster ID: ", this.id);
      writeln("Number of Members: ", this.n_members);
      writeln("Members: ", membersA);
      writeln("Is Well-Connected Cluster (WCC)?: ", this.isWcc);
      writeln("Is Singleton?: ", this.isSingleton);
      writeln("Cluster Depth: ", this.depth);
      writeln("Cluster membersA size: ", this.membersA.size);
      writeln("///////////////////////////////////////");
    }
    proc createSubgraphFromCluster(ref seg: [] int, ref dst: [] int) throws {


    }
  }

  
  

  /* Define a record to encapsulate an array with its own domain. */
  record clustListArray {
    var d: domain(1);
    var a: [d] int;

    proc init(data: [] int) {
      this.d = data.domain;
      this.a = data;
    }
  }

  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string):[] int throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var clusterArrtemp = wcc(g1);
    writeln("**********************************************************we reached here");

    var clusterArr = clusterArrtemp; //cluster id
    
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
    proc getEdgeList(ref vertices: [] int) throws {
      //writeln("///////////////////////getEdgeList called for: ", vertices.size);

      // Initialize lists to collect edges
      var srcList = new list(int);
      var dstList = new list(int);

      // Map to assign new indices to vertices (mapper)
      var mapper = new map(int, int);
      var reverseMapper = new map(int, int); // For reverse mapping
      var idx = 0;
      for v in vertices {
        mapper[v] = idx;
        reverseMapper[idx] = v;
        idx += 1;
      }
      //writeln("getEdgeList-1");
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
      //writeln("getEdgeList-2");

      // Convert lists to arrays
      var src = srcList.toArray();
      var dst = dstList.toArray();
      //writeln("getEdgeList-2-1");

      // Sort the edges
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
      //writeln("getEdgeList-2-2");

      // Remove duplicate edges
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);

      //writeln("getEdgeList-3");

  // Create mapper array (original vertex IDs)
  var n = mapper.size;
  var mapperArray:[0..n - 1] int;

for i in reverseMapper.keysToArray() {
  var originalV = reverseMapper[i];
  mapperArray[i] = originalV;
}
      //writeln("getEdgeList-4");

      return (uniqueSrc, uniqueDst, mapperArray);
      //return (src, dst, mapperArray);
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
      //writeln("////////////////sortEdgeList");
      //writeln("src.size: ", src.size);
      //writeln("dst.size: ", dst.size);
      // Combine src and dst into a tuple array
      var edges: [0..<src.size] (int, int);
      for i in 0..<src.size do
        edges[i] = (src[i], dst[i]);

      var TupleComp: TupleComparator;

        // Sort the edges using the comparator
      sort(edges, comparator=TupleComp);
//writeln("edges.size: ", edges.size);
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



    /* Write out the clusters to a file. */
    proc writeClusterToFile(ref membersA:[] int, id: int, depth: int, cut: int, ref mapper:[] int) throws {
        var filename = outputPath + "_" + id:string + "_" + depth:string + "_" + membersA.size:string + "_" + cut:string + ".txt";
        var file = open(filename, ioMode.cw);
        var fileWriter = file.writer(locking=false);
        var backedToArachne = mapper[membersA];
        var backedToOriginal = nodeMapGraphG1[backedToArachne];
        writeln("memberA: ",membersA);
        writeln("backedToArachne: ",backedToArachne);
        writeln("backedToOriginal: ",backedToOriginal);
        
        fileWriter.writeln("# cluster ID: " + id: string); 
        fileWriter.writeln("# cluster Depth: " + depth: string); 
        fileWriter.writeln("# number of members: " + membersA.size: string);
        fileWriter.writeln("# cutsize: " + cut: string);
        //fileWriter.writeln("# mapper: " + mapper: string);
        fileWriter.writeln("# members: " + backedToOriginal: string);
        
        try fileWriter.close();
        try file.close();
    }
    /* Function to calculate the degree of a vertex within a component/cluster/community. */
    proc calculateClusterDegree(ref membersA:[] int, vertex: int): int throws {
      //writeln("///////////////////////calculateClusterDegree called for vertex: ",vertex);
      //this.printClusterInfo();
      const ref neighbors = dstNodesG1[segGraphG1[vertex]..<segGraphG1[vertex+1]];
      var degree = 0;
      for u in neighbors do if binarySearch(membersA, u)[0] then degree += 1;
      //writeln("///////////////////////calculateClusterDegree ended -> ",degree);

      return degree;
    }

 /* Function to perform 2-core decomposition on a given cluster. */
    proc core2Decomposition(cluster: borrowed Cluster) throws{
      // Initialize degrees within the cluster.
        //writeln("///////////////////////core2Decomposition");

      var toBeRemovedVertices:int = 0;
      //var totalDegree:int = 0;

      var degrees: [cluster.membersD] int = -1;
      //writeln("degrees: ", degrees);

      // Step 1: Calculate initial degrees for each vertex in the cluster
      forall v in cluster.membersA with (ref degrees){
        degrees[v] = calculateClusterDegree(cluster.membersA, v);
      }
      //writeln("degrees: ", degrees);

      // Step 2: Initialize a queue for nodes with degree < 2
      var removeQueue = new list(int, parSafe=true);
      forall v in cluster.membersA with (ref removeQueue){
        if degrees[v] < 2 {
          removeQueue.pushBack(v);
        }
      }
      // While the queue is not empty.
      while removeQueue.size != 0 {
        var v = removeQueue.popBack();
        const ref neighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

        //for u in neighbors {
        for u in cluster.membersA {
          if binarySearch(neighbors, u)[0] &&  degrees[u] >= 2 {
            degrees[u] -= 1;
            if degrees[u] < 2 then removeQueue.pushBack(u);
          }
        }
      //
      
      //writeln("core2Decomposition 2-1");

        // Mark v as removed.
        degrees[v] = -1;
      }
      // Step 4: Collect nodes with degrees >= 2 and update cluster
      var newMembersList = new list(int);
      var totalDegree = 0;
      for v in cluster.membersA {
        if degrees[v] >= 2 {
          newMembersList.pushBack(v);
          totalDegree += degrees[v];
        }
      }

      // Step 5: Update cluster properties
      var newVertices = newMembersList.size;
      var newMembersD = {0..<newVertices};
      var newMembersA: [newMembersD] int = newMembersList.toArray();

      cluster.membersD = newMembersD;
      cluster.membersA = newMembersA;
      cluster.n_members = newVertices;


      if cluster.n_members < 2 then cluster.isSingleton = true;

      //writeln("2-core decomposition completed for cluster: ", cluster.id);
      //writeln("Remaining members: ", cluster.n_members);
    }


    /* From a passed cluster, remove all vertices with degree one. */
    proc removeDegreeOneVertices(cluster: borrowed Cluster) throws {
      var totalDegree:int = 0;
      var removedVertices:int = 0;
      for v in cluster.membersA {
        var memberDegree = calculateClusterDegree(cluster.membersA, v);
        if memberDegree <= 1 { v = -1; removedVertices += 1; }
        else totalDegree += memberDegree;
      }
      var newVertices = cluster.n_members - removedVertices;
      var newMembersD = {0..<newVertices};
      var newMembersA: [newMembersD] int;
      var idx:int = 0;
      for v in cluster.membersA {
        if v != -1 then { newMembersA[idx] = v; idx += 1; }
      }
      cluster.membersD = newMembersD;
      cluster.membersA = newMembersA;
      sort(cluster.membersA);
      cluster.n_members = newVertices;
      //if cluster.n_members > 0 then cluster.averageDegree = totalDegree / cluster.n_members;
      if cluster.n_members < 2 then cluster.isSingleton = true;
      //writeln("removeDegreeOneVertices returned cluster with size:", cluster.n_members);
    }

 
/////////////////////////////////////////////////////// new idea
proc removeVertices(src: [] int, dst: [] int, mapper: [] int, removedVertices: [] int) throws{
  const n = src.size;
  var toRemove: set(int,parSafe=true);



  var degrees: [removedVertices.domain] int = -1;
      
  forall v in removedVertices with (ref degrees){
    degrees[v] = calculateClusterDegree(removedVertices, v);
    }
  
  var removedEdgesCount: int = + reduce degrees;
  var newDomain: domain(1) = 0..< n - (removedEdgesCount * 2);
  var newSrc, newDst: [newDomain] int;
  
  var nweMapperDomain = 0..(mapper.size - removedVertices.size);
  var newMapper:[nweMapperDomain] int;

  var idex: int = 0;
  for elem in mapper{
    if removedVertices.find(elem) != -1{
      newMapper[idex] = elem;
      idex += 1;
    }
  }

  idex = 0;
  // Removing edges connected to the nodes in 'vertices'
  for i in src.domain {
    if newMapper.find(src[i]) != -1 && newMapper.find(dst[i]) != -1 {
      newSrc[idex] = src[i];
      newDst[idex] = dst[i];
      idex += 1;
    }
  }
  //writeln("newSrc",newSrc );
  //writeln("newDst",newDst );
  //writeln("newMapper",newMapper );
  //return (newSrc, newDst, newMapper);
}

/////////////////////////////////////////////////////// end of new idea

    proc removeDegreeOneFromPartition(ref partition:[] int) throws{
      //var totalDegree:int = 0;
      if partition.size <= 1{
        var zeroArray:[1..0] int;
        return zeroArray;
      }
      var removedVertices:int = 0;
      for v in partition {
            var memberDegree = calculateClusterDegree(partition, v);
            if memberDegree < 2 {
              v = -1; 
              removedVertices += 1; 
            }
            //else totalDegree += memberDegree;
          }
          var newVertices = partition.size - removedVertices;
          var newMembersA: [0..<newVertices] int;
          var idx:int = 0;
          for v in partition {
            if v != -1 then { 
              newMembersA[idx] = v; 
              idx += 1; 
            }
          }
        return(newMembersA);
    }
    /* Helper method to run the recursion. */
    /* Calls out to an external procedure that runs VieCut. */
    proc callMinCut(ref vertices: [] int, id: int, depth: int): list(int) throws {
      writeln("///////////////////////callMinCut, received: ",vertices.size," vertices to CUT");
      var allWCC: list(int, parSafe=true);
      
      // If the vertices array is empty, do nothing and return an empty list
      if vertices.size == 0 {
        //writeln("We reached to exception point for cluster: ",id, " with size: ",vertices.size," at depth: ", depth  );
        return allWCC;
      }

      var (src, dst, mapper) = getEdgeList(vertices);
      //writeln("src: ", src.size, "\ndst: ", dst.size, "\nmapper: ", mapper.size);
      var n = mapper.size;
      var m = src.size;

      var partitionArr: [{0..<n}] int;
      var newSrc: [{0..<m}] int = src;
      var newDst: [{0..<m}] int = dst;
      //writeln("We are here 100");
      // Call the external min-cut function
      var cut = c_computeMinCut(partitionArr, newSrc, newDst, n, m);

      var logN = floor(log10(vertices.size: real));
      var floorLog10N: int = logN:int;
      
      if cut > floorLog10N {// Check Well Connectedness
        allWCC.pushBack(id); //allWCC.pushBack(depth); allWCC.pushBack(vertices.size); allWCC.pushBack(cut);
        writeClusterToFile(vertices, id, depth, cut, mapper);
        writeln("for cluster: ",id," in depth: ",depth," with cutsize: ", cut, " we found wcc. it has ",vertices.size," memebr!");
        return allWCC;
      }
      else{// Cluster is not WellConnected
        
        // Separate vertices into two partitions
        var cluster1, cluster2 = new list(int);
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.pushBack(mapper[v]);
          else cluster2.pushBack(mapper[v]);
        }


        var newSubClusters: list(int, parSafe=true);
        
        // The partition size must be greater than 2 for it to be meaningful before passing it to VieCut.
        if cluster1.size >1 {
          var inPartitionTemp = cluster1.toArray();
          var inPartition = removeDegreeOneFromPartition(inPartitionTemp);
          //writeln("inPartition before removing has: ", cluster1.size," after removing: ", inPartition.size);
          //writeln("recursion happened for inPartition");
          newSubClusters = callMinCut(inPartition, id, depth+1);
        }
        if cluster2.size >1 {
          var outPartitionTemp = cluster2.toArray();        
          var outPartition = removeDegreeOneFromPartition(outPartitionTemp);
          //writeln("outPartition before removing has: ", cluster2.size," after removing: ", outPartition.size);
          //writeln("recursion happened for outPartition");
          newSubClusters = callMinCut(outPartition, id, depth+1);
        }
        for findings in newSubClusters do allWCC.pushBack(findings);

        //}
      }
      return allWCC;
    }
    /* Kick off well-connected components. */
    proc wcc(g1: SegGraph): [] int throws {
      //writeln("grah load with: ", g1.n_vertices," and: ", g1.n_edges," edges");
      var results: list(int, parSafe=true);
      var clusters = readClustersFile(inputcluster_filePath);
      //writeln("/// readClustersFile finished");
      forall key in clusters.keysToArray() with (ref results, ref clusters) {
      //for key in clusters.keysToArray() {
        ref clusterToAdd = clusters[key].toArray();;
        if clusterToAdd.size > 1 && key == 580{ // The cluster is not a singleton.
          var clusterInit = new owned Cluster(clusterToAdd, key);

          clusterInit.id = key;
          clusterInit.printClusterInfo();
          removeDegreeOneVertices(clusterInit);
          //clusterInit.printClusterInfo();

          var newResults = callMinCut(clusterInit.membersA, clusterInit.id, 0); 
          //var newResults:list(int, parSafe=true);
          for mapping in newResults do results.pushBack(mapping);
        }
      }
        var subClusterArrToReturn: [0..#results.size] int;
        subClusterArrToReturn = results.toArray();
        //var subClusterArrToReturn: [0..3] int;
        return subClusterArrToReturn;
      } // end of wcc
    
    return clusterArr;
  } // end of runWCC
} // end of WellConnectedComponents module