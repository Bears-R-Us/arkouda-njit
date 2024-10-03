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
      this.averageDegree = 0.0;
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

    /* Function to calculate the degree of a vertex within a component/cluster/community. */
    proc calculateClusterDegree(vertex: int, ref seg, ref dst): int throws {
      const ref neighbors = dst[seg[vertex]..<seg[vertex+1]];
      var degree = 0;
      for u in neighbors do if binarySearch(this.membersA, u)[0] then degree += 1;
      return degree;
    }

    /* From a passed cluster, remove all vertices with degree one. */
    proc removeDegreeOneVertices(ref seg, ref dst) throws {
      var totalDegree:int = 0;
      var removedVertices:int = 0;
      for v in this.membersA {
        var memberDegree = calculateClusterDegree(v, seg, dst);
        if memberDegree == 1 { v = -1; removedVertices += 1; }
        else totalDegree += memberDegree;
      }
      var newVertices = this.n_members - removedVertices;
      var newMembersD = {0..<newVertices};
      var newMembersA: [newMembersD] int;
      var idx:int = 0;
      for v in this.membersA {
        if v != -1 then { newMembersA[idx] = v; idx += 1; }
      }
      this.membersD = newMembersD;
      this.membersA = newMembersA;
      this.n_members = newVertices;
      if this.n_members > 0 then this.averageDegree = totalDegree / this.n_members;
      if this.n_members < 2 then this.isSingleton = true;
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
      writeln("///////////////////////////////////////");
    }
  }

  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string):[] int throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    
    var workQueue = new list(shared Cluster, parSafe=true);
    var clusterArrtemp = wcc(g1);
    
    var clusterArr = clusterArrtemp; //cluster id, depth, number of elements
    
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
      
      return clusters;
    }

    // /* Function to perform 2-core decomposition on a given cluster. */
    // proc core2Decomposition(cluster: shared Cluster) throws {
    //   // Initialize degrees within the cluster.
    //   var clusterMembers = cluster.members;
    //   var clusterDomain:domain(int, parSafe=true);
    //   clusterDomain += clusterMembers.toArray();;
    //   var degrees: [clusterDomain] int = -1;
    //   for v in clusterMembers do degrees[v] = calculateClusterDegree(clusterMembers, v);

    //   // Initialize queue of nodes with degree less than 2.
    //   var removeQueue = new list(int);
    //   for v in clusterMembers do if degrees[v] < 2 then removeQueue.pushBack(v);

    //   // While the queue is not empty.
    //   while !removeQueue.isEmpty() {
    //     var v = removeQueue.popBack();
    //     const ref neighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

    //     for u in neighbors {
    //       if cluster.members.contains(u) && degrees[u] >= 2 {
    //         degrees[u] -= 1;
    //         if degrees[u] < 2 then removeQueue.pushBack(u);
    //       }
    //     }

    //     // Mark v as removed.
    //     degrees[v] = -1;
    //   }

    //   // Collect nodes with degrees >= 2.
    //   var core2Members = new set(int);
    //   for v in cluster.members do if degrees[v] >= 2 then core2Members.add(v);
    //   cluster.members = core2Members;
    //   cluster.n_members = cluster.members.size;
    //   if cluster.n_members < 2 then cluster.isSingleton = true;
    // }

    /* Returns the sorted edge list for a given set of vertices. */
    proc getEdgeList(vertices: [] int) throws {
      var srcList, dstList = new list(int);

      for u in vertices {
        const ref neighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];
        for v in vertices {
          const (found, idx) = binarySearch(neighbors, v);
          if found {
            srcList.pushBack(u);
            dstList.pushBack(v);
          }
        }
      }
      var src = srcList.toArray();
      var dst = dstList.toArray();

      // if src.size > 0 && dst.size > 0 {
        var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
        var (deduppedSrc, deduppedDst) = removeMultipleEdges(sortedSrc, sortedDst);
        var (remappedSrc, remappedDst, mapper) = oneUpper(deduppedSrc, deduppedDst);

        var mapper1 = makeDistArray(1, int);
        var remappedSrc1 = makeDistArray(1, int);
        var remappedDst1 = makeDistArray(1, int);

        // NOTE: THIS DOES NOT WORK BECAUSE makeDistArray returns a default Chapel array instead
        //       of a block-distributed array when CHPL_COMM is turned off.

        writeln("remappedSrc.type = ", remappedSrc.type:string);
        writeln("remappedDst.type = ", remappedDst.type:string);
        writeln("mapper.type = ", mapper.type:string);

        writeln("remappedSrc1.type = ", remappedSrc1.type:string);
        writeln("remappedDst1.type = ", remappedDst1.type:string);
        writeln("mapper1.type = ", mapper1.type:string);

        return (mapper, mapper.size, remappedSrc, remappedDst, remappedSrc.size);
      // } else {
      //   var mapper = makeDistArray(1, int);
      //   var remappedSrc = makeDistArray(1, int);
      //   var remappedDst = makeDistArray(1, int);
      //   return (mapper, mapper.size-1, remappedSrc, remappedDst, remappedSrc.size-1);
      // }
    }

    /* Calls out to an external procedure that runs VieCut. */
    proc callMinCut(vertices: [] int) throws {
      var (mapper, n, src, dst, m) = getEdgeList(vertices);
      var partitionArr: [{0..<n}] int;
      var newSrc: [{0..<m}] int = src;
      var newDst: [{0..<m}] int = dst;
      var cut = c_computeMinCut(partitionArr, newSrc, newDst, n, m);

      var cluster1, cluster2 = new list(int);
      for (v,p) in zip(partitionArr.domain, partitionArr) {
        if p == 1 then cluster1.pushBack(mapper[v]);
        else cluster2.pushBack(mapper[v]);
      }
      var inPartition = cluster1.toArray();
      var outPartition = cluster2.toArray();
      
      return(cut, inPartition, outPartition);
    }


    /* Write out the clusters to a file. */
    proc writeClusterToFile(cluster: shared Cluster) throws {
      var filename = outputPath + "_" + cluster.id:string + ".txt";
      var file = open(filename, ioMode.cw);
      var fileWriter = file.writer(locking=false);

      fileWriter.writeln("# cluster ID: " + cluster.id: string); 
      fileWriter.writeln("# cluster Depth: " + cluster.depth: string); 
      fileWriter.writeln("# number of members: " + cluster.n_members: string);
      for member in cluster.membersA do fileWriter.writeln(member:string);
      
      try fileWriter.close();
      try file.close();
    }

    // /* Helper method to run the recursion. */
    // proc wccHelper(cluster: shared Cluster): list(int) throws {
    //   var allWCC: list(int, parSafe=true);
      
    //   core2Decomposition(cluster);
    //   // NOTE: Per our experimentations, getting the 2-core decomposition of the graph is faster
    //   //       than removing degree-one vertices multiple times. Therefore, we use that instead of
    //   //       what is originally outlined in the WCC paper. 
    //   // removeDegreeOneVertices(cluster);

    //   if !cluster.isSingleton {
    //     var currentID = cluster.id;
    //     var currentDepth = cluster.depth;
    //     var (cutSize, clusterList) = callMinCut(cluster.members);
    //     writeln("The size of clusterList is ", clusterList.size);
        
    //     if !cluster.isWellConnected(cutSize) {
    //       for minCutReturnedArr in clusterList {
    //         var subCluster = new shared Cluster(minCutReturnedArr.a);
    //         subCluster.id = currentID;
    //         subCluster.depth = currentDepth + 1;
    //         var newSubClusters: list(int);
    //         newSubClusters = wccHelper(subCluster);
    //         for findings in newSubClusters do allWCC.pushBack(findings);
    //       }
    //     } else {
    //       allWCC.pushBack(cluster.id);
    //       allWCC.pushBack(cluster.depth);
    //       allWCC.pushBack(cluster.n_members);
    //       writeClusterToFile(cluster);

    //       return allWCC;
    //     }
    //   }
    //   return allWCC;
    // }

    /* Kick off well-connected components. */
    proc wcc(g1: SegGraph): [] int throws {
      var results: list(int, parSafe=true);
      var clusters = readClustersFile(inputcluster_filePath);

      forall key in clusters.keysToArray() with (ref workQueue) {
        var cluster = clusters[key].toArray();
        workQueue.pushBack(new shared Cluster(cluster, key));
      }
      writeln("workQueue size = ", workQueue.size);
      writeln("here.maxTaskPar = ", here.maxTaskPar);

      while workQueue.size > 0 {
        coforall i in 0..<here.maxTaskPar with (ref workQueue, ref results) {
          var cluster = workQueue.popBack();
          writeln("Working on cluster ", cluster.id, ": ");
          cluster.removeDegreeOneVertices(segGraphG1, dstNodesG1);
          if !cluster.isSingleton {
            var (cutSize, inPartition, outPartition) = callMinCut(cluster.membersA);
            if !cluster.isWellConnected(cutSize) {
              workQueue.pushBack(new shared Cluster(inPartition, cluster.id));
              workQueue.pushBack(new shared Cluster(outPartition, cluster.id));
            } else {
              writeClusterToFile(cluster);
              results.pushBack(cluster.id);
            }
          }
        }
      }

      // forall key in clusters.keysToArray() with (ref results, ref clusters) {
      //   ref clusterToAdd = clusters[key];
      //   if clusterToAdd.size > 1 { // The cluster is not a singleton.
      //     var clusterInit = new shared Cluster(clusterToAdd);
      //     clusterInit.id = key;
      //     var newResults = wccHelper(clusterInit);
      //     for mapping in newResults do results.pushBack(mapping);
      //   }
      //   // writeln("Inits from array called so far: ", initFromArray.read());
      //   // writeln("Inits from set called so far: ", initFromSet.read());
      // }
        var subClusterArrToReturn: [0..<results.size] int;
        for i in 0..<results.size do subClusterArrToReturn[i] = results(i);
        return subClusterArrToReturn;
      } // end of wcc
    
    return clusterArr;
  } // end of runWCC
} // end of WellConnectedComponents module