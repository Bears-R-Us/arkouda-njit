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
    var id: int;            // Cluster identifier.
    var n_members: int;     // Cluster size.
    var members: set(int);  // Members set.       
    var isWcc: bool;        // Is it a well-connected cluster?
    var isSingleton: bool;  // Is it a singleton cluster?
    var depth: int;         // Cluster depth;
    var averageDegree: real; // Cluster averageDegree;

    /* Cluster initializer from array. */
    proc init(members: [] int) {
      this.id = -1;
      this.n_members = members.size;
      this.members = new set(int);
      for m in members do this.members.add(m);
      this.isWcc = false;
      if this.n_members <= 1 then this.isSingleton = true;
      this.depth = 0;
      this.averageDegree = 0.0;
    }        
    
    /* Cluster initializer from list. */
    proc init(members: set(int)) {
      this.id = -1;
      this.n_members = members.size;
      this.members = new set(int);
      this.members += members;
      this.isWcc = false;
      if this.n_members <= 1 then this.isSingleton = true;
      this.depth = 0;
      this.averageDegree = 0.0;
    }
    /* Method to print all details of the Cluster object. */
    proc printClusterInfo() {
      writeln("///////////////////////////////////////");
      writeln("Cluster ID: ", this.id);
      writeln("Number of Members: ", this.n_members);
      writeln("Members: ", members);
      writeln("Is Well-Connected Cluster (WCC)?: ", this.isWcc);
      writeln("Is Singleton?: ", this.isSingleton);
      writeln("Cluster Depth: ", this.depth);
      writeln("///////////////////////////////////////");
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

    /* Function to calculate the degree of a vertex within a component/cluster/community. */
    proc calculateClusterDegree(clusterMembers: set(int), vertex: int): int throws {
      const ref neighbors = dstNodesG1[segGraphG1[vertex]..<segGraphG1[vertex+1]];
      var degree = 0;
      for u in neighbors {
        if clusterMembers.contains(u) then degree += 1;
      }
      return degree;
    }

    /* From a passed cluster, remove all vertices with degree one. */
    proc removeDegreeOneVertices(cluster: borrowed Cluster) throws {
      var totalDegree:int = 0;
      var newMemberSet: set(int);
      for v in cluster.members {
        var memberDegree = calculateClusterDegree(cluster.members, v);
        if  memberDegree >= 2 {
          newMemberSet.add(v);
          totalDegree += memberDegree;
        }
      }
      cluster.members = newMemberSet;
      cluster.n_members = cluster.members.size;
      if cluster.n_members > 0 then cluster.averageDegree = totalDegree / cluster.n_members;

      if cluster.n_members < 2 then cluster.isSingleton = true;
    }

    /* Function to perform 2-core decomposition on a given cluster. */
    proc core2Decomposition(cluster: borrowed Cluster) throws{
      // Initialize degrees within the cluster.
      var clusterMembers = cluster.members;
      var clusterDomain:domain(int, parSafe=true);
      clusterDomain += clusterMembers.toArray();;
      var degrees: [clusterDomain] int = -1;
      for v in clusterMembers do degrees[v] = calculateClusterDegree(clusterMembers, v);

      // Initialize queue of nodes with degree less than 2.
      var removeQueue = new list(int);
      for v in clusterMembers do if degrees[v] < 2 then removeQueue.pushBack(v);

      // While the queue is not empty.
      while !removeQueue.isEmpty() {
        var v = removeQueue.popBack();
        const ref neighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

        for u in neighbors {
          if cluster.members.contains(u) && degrees[u] >= 2 {
            degrees[u] -= 1;
            if degrees[u] < 2 then removeQueue.pushBack(u);
          }
        }

        // Mark v as removed.
        degrees[v] = -1;
      }

      // Collect nodes with degrees >= 2.
      var core2Members = new set(int);
      for v in cluster.members do if degrees[v] >= 2 then core2Members.add(v);
      cluster.members = core2Members;
      cluster.n_members = cluster.members.size;
      if cluster.n_members < 2 then cluster.isSingleton = true;
    }

    /* Given a cluster and a cut size, determine if it is well-connected or not. */
    proc isWellConnected(cluster: borrowed Cluster, edgeCutSize: int): bool throws {
      var logN = floor(log10(cluster.members.size: real));
      var floorLog10N: int = logN:int;
      
      if edgeCutSize > floorLog10N {
        cluster.isWcc = true;
        return true;
      }

      return false;
    }

    /* Returns the sorted edge list for a given set of vertices. */
    proc getEdgeList(vertices: set(int)){
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

      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
      var (deduppedSrc, deduppedDst) = removeMultipleEdges(sortedSrc, sortedDst);
      var (remappedSrc, remappedDst, mapper) = oneUpper(deduppedSrc, deduppedDst);

      return (mapper, mapper.size, remappedSrc, remappedDst, remappedSrc.size);
    }

    /* Calls out to an external procedure that runs VieCut. */
    proc callMinCut(vertices: set(int)): (int, list(clustListArray)) {
      var (mapper, n, src, dst, m) = getEdgeList(vertices);
      var partitionArr: [{0..<n}] int;
      var cut = c_computeMinCut(partitionArr, src, dst, n, m);

      var cluster1, cluster2 = new list(int);
      for (v,p) in zip(partitionArr.domain, partitionArr) {
        if p == 1 then cluster1.pushBack(mapper[v]);
        else cluster2.pushBack(mapper[v]);
      }

      var inPartition = new clustListArray(cluster1.toArray());
      var outPartition = new clustListArray(cluster2.toArray());

      var cluslist: list(clustListArray);
      cluslist.pushBack(inPartition);
      cluslist.pushBack(outPartition);
      
      return(cut, cluslist);
    }


    /* Write out the clusters to a file. */
    proc writeClusterToFile(cluster: borrowed Cluster) throws {
      var filename = outputPath + "_" + cluster.id:string + ".txt";
      var file = open(filename, ioMode.cw);
      var fileWriter = file.writer(locking=false);

      fileWriter.writeln("# cluster ID: " + cluster.id: string); 
      fileWriter.writeln("# cluster Depth: " + cluster.depth: string); 
      fileWriter.writeln("# number of members: " + cluster.n_members: string);
      for member in cluster.members do fileWriter.writeln(member:string);
      
      try fileWriter.close();
      try file.close();
    }

    /* Helper method to run the recursion. */
    proc wccHelper(cluster: borrowed Cluster): list(int) throws {
      var allWCC: list(int);
      
      core2Decomposition(cluster);
      // NOTE: Per our experimentations, getting the 2-core decomposition of the graph is faster
      //       than removing degree one vertices multiple times. Therefore, we use that instead of
      //       what is originally outlined in the WCC paper. 
      // removeDegreeOneVertices(cluster);

      if !cluster.isSingleton {
        var currentID = cluster.id;
        var currentDepth = cluster.depth;
        var (cutSize, clusterList) = callMinCut(cluster.members); 
        
        if !isWellConnected(cluster, cutSize) {
          for minCutReturnedArr in clusterList {
            var subCluster = new owned Cluster(minCutReturnedArr.a);
            subCluster.id = currentID;
            subCluster.depth = currentDepth + 1;
            var newSubClusters: list(int);
            newSubClusters = wccHelper(subCluster);
            for findings in newSubClusters do allWCC.pushBack(findings);
          }
        } else {
          allWCC.pushBack(cluster.id);
          allWCC.pushBack(cluster.depth);
          allWCC.pushBack(cluster.n_members);
          writeClusterToFile(cluster);

          return allWCC;
        }
      }
      return allWCC;
    }

    /* Kick off well-connected components. */
    proc wcc(g1: SegGraph): [] int throws {
      var results: list(int);
      var clusters = readClustersFile(inputcluster_filePath);

      for key in clusters.keys() {
        ref clusterToAdd = clusters[key];
        var clusterInit = new owned Cluster(clusterToAdd);
        clusterInit.id = key;

        if !clusterInit.isSingleton && !clusterInit.isWcc {
          var newResults = wccHelper(clusterInit);
          for mapping in newResults do results.pushBack(mapping);
        }
      }

      var subClusterArrToReturn: [0..#results.size] int;
      for i in 0..#results.size do subClusterArrToReturn[i] = results(i);
      return(subClusterArrToReturn);
    } // end of wcc
    
    return clusterArr;
  } // end of runWCC
} // end of WellConnectedComponents module