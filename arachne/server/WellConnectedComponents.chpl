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

      /* Cluster initializer from array. */
      proc init(members: [] int) {
        this.id = -1;
        this.n_members = members.size;
        this.members = new set(int);
        for m in members do this.members.add(m);
        this.isWcc = false;
        if this.n_members <= 1 then this.isSingleton = true;
      }        
      
      /* Cluster initializer from list. */
      proc init(members: set(int)) {
        this.id = -1;
        this.n_members = members.size;
        this.members = new set(int);
        this.members += members;
        this.isWcc = false;
        if this.n_members <= 1 then this.isSingleton = true;
      }

      /* Method to remove nodes with degree 1 (to be implemented). */
      proc removeDegreeOne() {}
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

    proc runWCC (g1: SegGraph, st: borrowed SymTab, inputcluster_filePath: string):[] int throws {
      var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
      var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
      var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
      var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
      var clusterArrtemp = wcc(g1);
      writeln("clusterArrtemp = ", clusterArrtemp);
      var clusterArr = nodeMapGraphG1[clusterArrtemp]; // Map vertices back to original values.

      /*
        Process file that lists clusterID with one vertex on each line to a map where each cluster
        ID is mapped to all of the vertices with that cluster ID. 
      */
      proc readClustersFile(filename: string) throws {
        var clusters = new map(int, set(int));
        var file = open(filename, ioMode.r);
        var reader = file.reader();

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
          }
        }
        reader.close();
        file.close();
        return clusters;
      }

      /* Function to calculate the degree of a vertex. */
      proc calculateDegree(clusterMembers, elem: int): int throws {
        const ref neighbors = dstNodesG1[segGraphG1[elem]..<segGraphG1[elem+1]];
        
        // TODO: Wasting space by using to.Array(). Maybe just make our own intersection procedure?
        var intersection = neighbors & clusterMembers.toArray();
        return intersection.size;
      }

      proc removeDegreeOne(cluster: borrowed Cluster) throws {
          // Iterate over the members and collect elements that need to be removed
          for elem in cluster.members {
            //writeln("$$$$$ ENTER calculateDegree");
              if calculateDegree(cluster.members, elem) < 2 {
                  //writeln("$$$$$ EXIT calculateDegree");
                  cluster.members.remove(elem);

                  //TODO: TO CONTINUE WE HAVE TO CHANGE members TO BE A SET.

                  //writeln("Marked for removal: ", elem);
              }
          }
          cluster.n_members = cluster.members.size;
          if cluster.n_members <2 then cluster.isSingleton = true;
          //writeln("cluster after removeing degree one nodes: ", cluster);
          //return cluster;  // Return the modified cluster
      }
      
      // function is wrong I should call it by edgeCutSize
      proc isWellConnected(cluster: borrowed Cluster, edgeCutSize: int): bool throws {
          //writeln("////////////////************isWellConnected begin");

          // Compute the base-10 logarithm of 'numEdges' and take the floor
          var logN = floor(log10(cluster.members.size: real));
          // Convert the result to an integer if needed
          var floorLog10N: int = logN:int;
          
          //Well Connected Function
          if edgeCutSize > floorLog10N {
            writeln("the cluster = ",cluster," is well connected");
            cluster.isWcc = true;
            writeln("the cluster.isWcc updated = ",cluster.isWcc," is well connected");
            return true;
          }

          return false;
      }
      // The created edges is not sorted. should be? 
      proc createVieCutGraph(nodes: set(int)){
        var edgeSet = new set((int, int));
        for elem in nodes {
          const ref neighbors = dstNodesG1[segGraphG1[elem]..<segGraphG1[elem + 1]];
          for neigh in neighbors do edgeSet.add((elem, neigh));
        }
        var src, dst: [{0..edgeSet.size-1}] int;
        var src_index = 0;

        for edge in edgeSet {
          src[src_index] = edge(0);
          dst[src_index] = edge(1);
          src_index += 1;
        }
        var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
        var (remappedSrc, remappedDst, mapper) = oneUpper(sortedSrc, sortedDst);
        return(remappedSrc,remappedDst,remappedSrc.size,mapper.size,mapper);
      }

      proc callMinCut(nodes: set(int)): (int, list(clustListArray)) {
          var (src, dst, m, n, mapper) = createVieCutGraph(nodes);
          var partitionArr: [{0..<n}] int;
          var cut = c_computeMinCut(partitionArr, src, dst, n, m);
          writeln("m   = ", m);
          writeln("n   = ", n);
          writeln("cut = ", cut);
          writeln();

          var cluster1, cluster2 = new list(int);
          for (v,p) in zip(partitionArr.domain, partitionArr) {
            if p == 1 then cluster1.pushBack(mapper[v]);
            else cluster2.pushBack(mapper[v]);
          }

          // Create clustListArray instances
          var domVarryArray1 = new clustListArray(cluster1.toArray());
          var domVarryArray2 = new clustListArray(cluster2.toArray());

          var cluslist : list(clustListArray);
          // Push the instances into the list
          cluslist.pushBack(domVarryArray1);
          cluslist.pushBack(domVarryArray2);
          //writeln("cluslist = ", cluslist);
          return(cut, cluslist);
      }


      // Function to write cluster members to a file
      proc writeClusterToFile(cluster: borrowed Cluster) throws {
          //writeln("////////////////************writeClusterToFile begin");

          // cluster ID to ve distinguished
          var filename = "/scratch/users/md724/DataSets/wcc/WCC_Output/cluster_" + cluster.id:string + ".txt";
  
          
          var file = open(filename, ioMode.cw); // 'cw' stands for Create and Write

          // This fileWriter will not be used in parallel, so does not need to use
          // locking)
          var fileWriter = file.writer(locking=false);

          fileWriter.writeln("# cluster ID: " + cluster.id: string); 
          fileWriter.writeln("# number of members: " + cluster.n_members: string);
          // Write each member to the file, one per line. I am not sure!!!!!
          for member in cluster.members {
              //writeln("member :", member:string);
              fileWriter.writeln(member:string);
          }
          
          // Close the file to ensure data is flushed. 
          try fileWriter.close();
          try file.close();
          
          //writeln("WCC written to ", filename);
      }



      proc wccHelper(cluster: borrowed Cluster): list(int) throws{
          //writeln("////////////////************wccHelper begin");

          // Initialize an empty list to collect well-connected clusters
          var allWCC: list(int);

          //Preprocessing: remove degree-one 
          removeDegreeOne(cluster);

          // Check if the cluster is not a singleton and has more than 10 members
          if !cluster.isSingleton && cluster.n_members > 10 {

              // Update sub-cluster properties
              var currentID = cluster.id;

              // Perform min-cut to get cutSize and sub-clusters
              var (cutSize, clusterList) = callMinCut(cluster.members);
              
              if !isWellConnected(cluster, cutSize) {
                  // Iterate over each sub-cluster
                  //forall minCutReturnedArr in clusterList{

                  for minCutReturnedArr in clusterList{

                      //writeln("minCutReturnedArr = ", minCutReturnedArr);
                      var subCluster = new owned Cluster(minCutReturnedArr.a);
                      subCluster.id = currentID;

                      //writeln("subCluster created = ", subCluster);

                      var newSubClusters: list(int);

                      // Collect clusters from recursive call
                      newSubClusters = wccHelper(subCluster);

                      
                      // Use a loop to add elements from newMappings to allmappings
                      for findings in newSubClusters do allWCC.pushBack(findings);
                      writeln("newSubClusters found :", allWCC);
                  }
              } else {
                writeln("!!!!!!!!!!! WC Cluster found = ", cluster.members);
                // Add the well-connected cluster to the list
                allWCC.pushBack(cluster.id);
                allWCC.pushBack(cluster.n_members);
                
                // Attempt to write the well-connected cluster to a file
                writeClusterToFile(cluster);

                return allWCC;
              }
          }
          writeln("allWCC = ", allWCC);
          return allWCC;
      }

      proc wcc(g1: SegGraph): [] int throws {
        var results: list(int);
        var clusters = readClustersFile(inputcluster_filePath);

        for key in clusters.keys() {
            //writeln("Cluster ID: ", key);
            ref clusterToAdd = clusters[key];
            var clusterInit = new owned Cluster(clusterToAdd);
            clusterInit.id = key;
            //writeln("Cluster created = ", clusterInit);
            
            //writeClusterToFile(clusterInit);
            //if clusterInit.id == 905 then findAdjNeighinCluster(clusterInit, 415);
            
            if !clusterInit.isSingleton && !clusterInit.isWcc {
                
                //ClusterKCoreDecomposition(clusterInit.members,2);
                //writeln("we are here");
                var newResults = wccHelper(clusterInit);
                
                for mapping in newResults do results.pushBack(mapping);

            }
        }
        var subClusterArrToReturn: [0..#results.size] int;
        for i in 0..#results.size do subClusterArrToReturn[i] = results(i);
        //writeln ("subClusterArrToReturn: ", subClusterArrToReturn);
        return(subClusterArrToReturn);
      } // end of wcc
      writeln("clusterArr = ", clusterArr);
      return clusterArr;
    } // end of runWCC
} // end of WellConnectedComponents module