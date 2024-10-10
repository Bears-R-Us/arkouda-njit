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

    /* Default initializer. */
    proc init() {
      this.id = -1;
      this.n_members = 0;
      this.isWcc = false;
      this.isSingleton = true;
      this.depth = 0;
      this.averageDegree = 0.0;
    }
    
    /* Cluster initializer from array. */
    proc init(members: [?D] int, id:int, depth:int=0) {
      this.id = id;
      this.n_members = members.size;
      this.isWcc = false;
      if this.n_members <= 1 then this.isSingleton = true;
      this.depth = depth;
      this.averageDegree = 0.0;
      this.membersD = D;
      this.membersA = members;
      // sort(this.membersA);
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
      for v in this.membersA do if v != -1 then { newMembersA[idx] = v; idx += 1; }
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

    /* Given a mincut value and cluster size, returns if the cluster is well-connected or not. */
  proc isWellConnected(cut: int, n:int): bool throws {
    var logN = floor(log10(n:real));
    var floorLog10N:int = logN:int;
    
    if cut > floorLog10N then return true;
    return false;
  }


  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string):[] int throws {
    ref srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    ref dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    ref segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    
    var workStack = new list(shared Cluster, parSafe=true);
    var results: list(shared Cluster, parSafe=true);
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

    /* Returns the sorted edge list for a given set of vertices. */
    proc getEdgeList(ref vertices: [] int) throws {
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

      if src.size != 0 && dst.size != 0 {
        var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
        var (deduppedSrc, deduppedDst) = removeMultipleEdges(sortedSrc, sortedDst);
        var (remappedSrc, remappedDst, mapper) = oneUpper(deduppedSrc, deduppedDst);
        return (mapper, mapper.size, remappedSrc, remappedDst, remappedSrc.size);
      } else {
        var mapper = makeDistArray(0, int);
        var remappedSrc = makeDistArray(0, int);
        var remappedDst = makeDistArray(0, int);
        return (mapper, mapper.size, remappedSrc, remappedDst, remappedSrc.size);
      }
    }

    /* Calls out to an external procedure that runs VieCut. */
    proc callMinCut(cluster: shared Cluster) throws {       
      var (mapper, n, src, dst, m) = getEdgeList(cluster.membersA);                    
      if m > 0 {
        var partitionArr: [{0..<n}] int;
        var newSrc: [{0..<m}] int = src;
        var newDst: [{0..<m}] int = dst;
        var cut = c_computeMinCut(partitionArr, newSrc, newDst, n, m);

        if isWellConnected(cut, n) {
          cluster.isWcc = true;
          results.pushBack(cluster);
        }
        else {
          var cluster1, cluster2 = new list(int);
          for (v,p) in zip(partitionArr.domain, partitionArr) {
            if p == 1 then cluster1.pushBack(mapper[v]);
            else cluster2.pushBack(mapper[v]);
          }
          var inPartition = cluster1.toArray();
          var outPartition = cluster2.toArray();

          if inPartition.size > 1 then 
            workStack.pushBack(new shared Cluster(inPartition, cluster.id, cluster.depth+1));
          if outPartition.size > 1 then 
            workStack.pushBack(new shared Cluster(outPartition, cluster.id, cluster.depth+1));
        }
      }
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

    proc popIfNotEmpty(ref l) {
      l._enter();
      var cluster = new shared Cluster();
      if l._size != 0 then cluster = l._popAtIndex(l._size - 1);
      l._leave();
      return cluster;
    }

    /* Kick off well-connected components. */
    proc wcc(g1: SegGraph): [] int throws {
      var clusters = readClustersFile(inputcluster_filePath);

      forall key in clusters.keysToArray() with (ref workStack) {
        var cluster = clusters[key].toArray();
        sort(cluster);
        workStack.pushBack(new shared Cluster(cluster, key));
      }
      writeln("workStack size = ", workStack.size);
      writeln("here.maxTaskPar = ", here.maxTaskPar);
      writeln();

      var iteration:int = 0;
      while workStack.size > 0 {
        coforall i in 0..<here.maxTaskPar with (ref workStack, ref results) {
          var cluster = popIfNotEmpty(workStack);
          if cluster.id != -1 {
            cluster.removeDegreeOneVertices(segGraphG1, dstNodesG1);
            if !cluster.isSingleton then callMinCut(cluster);
          }
        }
        iteration += 1;
      }
      writeln("Number of iterations = ", iteration);
      // for r in results {
      //   writeln("Cluster ID: ", r.id, ", Depth: ", r.depth, ", Members: ", r.membersA.size);
      // }

      var subClusterArrToReturn: [0..<results.size] int;
      for i in 0..<results.size do subClusterArrToReturn[i] = results[i].id;
      return subClusterArrToReturn;
    } // end of wcc
    
    return clusterArr;
  } // end of runWCC
} // end of WellConnectedComponents module