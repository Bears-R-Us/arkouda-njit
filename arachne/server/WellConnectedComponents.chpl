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
            "./external_libs/VieCut/build/extlib/tlx/tlx/CMakeFiles/tlx.dir/logger.cpp.o";
    
    extern proc c_computeMinCut(src: [] int, dst: [] int, n: int, m: int): int;

    class Cluster {
      var id: int;              // Cluster identifier.
      var n_member: int;        // Cluster size.
      var members: domain(int); // Domain to store cluster members.
      var isWcc: bool;          // Is it a well-connected cluster?
      var isSingleton: bool;    // Is it a singleton cluster?
      var depth: int;           // Clustering depth.

      /** Cluster initializer from array. */
      proc init(members: [] int) {
        this.id = -1;
        this.n_member = members.size;
        this.members = members;
        this.isWcc = false;
        if this.n_member <= 1 then this.isSingleton = true;
        this.depth = 0;
      }        
      
      /** Cluster initializer from domain. */
      proc init(members: domain(int)) {
        this.id = -1;
        this.n_member = members.size;
        this.members = members;
        this.isWcc = false;
        if this.n_member <= 1 then this.isSingleton = true;
        this.depth = 0;
      }

      /** Method to remove nodes with degree 1 (to be implemented). */
      proc removeDegreeOne() {}
    }
 
    // Define a record to encapsulate an array with its own domain
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
      var srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
      var dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
      var segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
      var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
      var clusterArrtemp = wcc(g1);
      var clusterArr = nodeMapGraphG1[clusterArrtemp]; // Map vertices back to original values.

      // Function to calculate the degree of a node within the cluster
      proc findAdjNeighinCluster(cluster: borrowed Cluster, elem: int) throws{
          //writeln("////////////////************//calculateDegree begin");

          var Neighbours: domain(int) = {1..0};
          //writeln("elem = ", elem);
          // Retrieve in-neighbors
          var inNeigh_elem = dstRG1[segRG1[elem]..<segRG1[elem + 1]];
          //writeln("inNeigh_elem: ", inNeigh_elem);
          Neighbours += inNeigh_elem;
          
          // Retrieve out-neighbors
          var outNeigh_elem = dstNodesG1[segGraphG1[elem]..<segGraphG1[elem + 1]];
          Neighbours += outNeigh_elem;
          //writeln("outNeigh_elem: ", outNeigh_elem);
          //writeln("all Neighbours of (",elem," ): ", Neighbours);
          

          // Intersection with cluster to get valid neighbors
          var intersectionDomain = Neighbours & cluster.members;
          //writeln("elem : ",elem, " has degree = ",intersectionDomain.size );

          var NeiArr:[0..intersectionDomain.size-1] int;
          var idx = 0;
          
          for elem in intersectionDomain {
              NeiArr[idx] = elem;
              idx += 1;
          }
          
          //NeiArr = intersectionDomain;
          return NeiArr;
      }

      proc readClustersFile(filename: string) throws {
          // Map from cluster ID to a domain of mapped nodes
          var clusters = new map(int, domain(int));

          var file = open(filename, ioMode.r);
          var reader = file.reader();

          for line in reader.lines() {
              //writeln("line = ", line);
              // Split the line by whitespace or tabs
              var fields = line.split();
              if fields.size >= 2 {

                  var originalNode = fields(0): int;
                  // Cluster ID
                  var clusterID = fields(1): int;

                  // Perform binary search on nodeMapGraphG1 to find the originalNode
                  const (found, idx) = binarySearch(nodeMapGraphG1, originalNode);

                  if found {
                      // Use the index as the mapped node if the originalNode was found
                      var mappedNode = idx;

                      // Check if the clusterID exists in the map
                      if clusters.contains(clusterID) {
                          // Add the mapped node to the existing domain for that cluster
                          clusters[clusterID].add(mappedNode);
                      } else {
                          // Create a new domain with the mapped node and add it to the map
                          var d: domain(int) = {mappedNode};
                          clusters[clusterID] = d;
                      }
                  } else {
                      // Handle the case where the originalNode is not found in nodeMapGraphG1
                      //writeln("Error: Original node ", originalNode, " not found in nodeMapGraphG1.");
                      //writeln("*****************dummy node found");
                  }
              }
          }

          // Close the file and reader after reading
          reader.close();
          file.close();


          // Return the map of clusters (cluster ID -> domain of mapped nodes)
          return clusters;
      }

      // Function to calculate the degree of a node within the cluster
      proc calculateDegree(cluster: domain(int), elem: int): int throws{
        const ref inNeigh_elem = dstRG1[segRG1[elem]..<segRG1[elem+1]];
        const ref outNeigh_elem = dstNodesG1[segGraphG1[elem]..<segGraphG1[elem+1]];
        var intersection = inNeigh_elem & outNeigh_elem;
        return intersection.size;
      }

      proc removeDegreeOne(cluster: borrowed Cluster) throws{

          // Iterate over the members and collect elements that need to be removed
          for elem in cluster.members {
            //writeln("$$$$$ ENTER calculateDegree");
              if calculateDegree(cluster.members, elem) < 2 {
                  //writeln("$$$$$ EXIT calculateDegree");
                  cluster.members.remove(elem);
                  //writeln("Marked for removal: ", elem);
              }
          }
          cluster.n_member = cluster.members.size;
          if cluster.n_member <2 then cluster.isSingleton = true;
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
              //writeln("the cluster = ",cluster," is well connected");
              cluster.isWcc = true;
              //writeln("the cluster.isWcc updated = ",cluster.isWcc," is well connected");
              return true;
          }

          return false;
      }
      // The created edges is not sorted. should be? 
      proc createVieCutGraph(nodes: domain(int)){
        //writeln("////////////////************createVieCutGraph begin");
        var edgeSet = new set((int, int));  // A set to store unique edges as (src, dst) pairs
        // //writeln("Nodes are: ", nodes);
        for elem in nodes {
            const ref inNeigh_elem = dstRG1[segRG1[elem]..<segRG1[elem + 1]];
            const ref outNeigh_elem = dstNodesG1[segGraphG1[elem]..<segGraphG1[elem + 1]];
            var valid_neis = inNeigh_elem & outNeigh_elem;
            // //writeln("valid neighbors = ", valid_neis);

            for neigh in valid_neis {
              edgeSet.add((elem, neigh));
              //edgeSet.add((neigh, elem));
            }
            // //writeln("edgeSet- outNeigh added = ", edgeSet);
        }

        // Initialize the src and dst arrays based on the size of the edgeSet
        var src, dst: [{0..edgeSet.size-1}] int;

        // Populate src and dst arrays from the edgeSet
        // I should find better this will be too slow
        
        var src_index = 0;

        for edge in edgeSet {
            src[src_index] = edge(0);  // The source node
            dst[src_index] = edge(1);  // The destination node
            src_index += 1;
        }

        // Sort the edge list, rename the vertex identifiers, and get the new map.
        var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
        var (remappedSrc, remappedDst, mapper) = oneUpper(sortedSrc, sortedDst);
        // //writeln("remappedSrc = ", remappedSrc);
        // //writeln("remappedDst = ", remappedDst);
        // //writeln("     mapper = ", mapper);

        // //writeln("src: ", src);
        // //writeln("dst: ", dst);
        return(remappedSrc,remappedDst,remappedSrc.size,mapper.size,mapper);
      }

      proc callMinCut(nodes: domain(int)): (int, list(clustListArray)) {
          //writeln("////////////////************callMinCut begin");

          //bring an int cutSize
          //bring list of uniqu nodes in each new partition
          //should return List or arrys of clusters
          var (src, dst, m, n, mapper) = createVieCutGraph(nodes);
          //writeln("!!!!! We get out of creating the VieCut Graph");

        //   //writeln("src = ", src);
        //   //writeln("dst = ", dst);
          writeln("  m = ", m);
          writeln("  n = ", n);

          var cut = c_computeMinCut(src, dst, n, m);
          writeln("The returned cut is ", cut);
          writeln();

          var cluster1 = [0, 4, 5];  // First array
          var cluster2 = [6, 7, 1, 8, 9, 10, 2];  // Second array

          // Create clustListArray instances
          var domVarryArray1 = new clustListArray(cluster1);
          var domVarryArray2 = new clustListArray(cluster2);

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
          fileWriter.writeln("# number of members: " + cluster.n_member: string);
          fileWriter.writeln("# cluster depth: " + cluster.depth: string);
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
          
          // Base case: check if a well connected cluster is found
          if cluster.isWcc == true {
              //writeln("WC Cluster found = ", cluster.members);
              // Add the well-connected cluster to the list
              allWCC.pushBack(cluster.id);
              allWCC.pushBack(cluster.n_member);
              
              // Attempt to write the well-connected cluster to a file
              writeClusterToFile(cluster);

              return allWCC;
          }

          //Preprocessing: remove degree-one 
          removeDegreeOne(cluster);

          // Check if the cluster is not a singleton and has more than 10 members
          if !cluster.isSingleton && cluster.n_member > 10 {

              // Update sub-cluster properties
              var currentDpeth = cluster.depth;
              var currentID = cluster.id;

              // Perform min-cut to get cutSize and sub-clusters
              var (cutSize, clusterList) = callMinCut(cluster.members);
              
              if !isWellConnected(cluster, cutSize){
                  // Iterate over each sub-cluster
                  //forall minCutReturnedArr in clusterList{

                  for minCutReturnedArr in clusterList{

                      //writeln("minCutReturnedArr = ", minCutReturnedArr);
                      var subCluster = new owned Cluster(minCutReturnedArr.a);
                      subCluster.depth = currentDpeth + 1;
                      subCluster.id = currentID;

                      //writeln("subCluster created = ", subCluster);

                      var newSubClusters: list(int, parSafe=true);

                      // Collect clusters from recursive call
                      newSubClusters = wccHelper(subCluster);

                      
                      // Use a loop to add elements from newMappings to allmappings
                      for findings in newSubClusters do allWCC.pushBack(findings);
                      //writeln("newSubClusters found :", allWCC);
                  }

              }
          }

          return allWCC;
      }

      proc wcc(g1: SegGraph): [] int throws {
          //writeln("graph loaded with ", g1.n_vertices," and ", g1.n_edges," edges");
          //writeln("we are lading the clusters....");
          
          var results: list(int, parSafe=true);

          //var clusters = readClustersFile("/scratch/users/md724/DataSets/wcc/clustering.tsv");
          var clusters = readClustersFile(inputcluster_filePath);

          // Print each cluster with its mapped nodes
          for key in clusters.keys() {
              //writeln("Cluster ID: ", key);
              
              var clusterInit = new owned Cluster(clusters[key]);
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
          var subClusterArrToReturn: [0..#results.size](int);
          for i in 0..#results.size do subClusterArrToReturn[i] = results(i);
          //writeln ("subClusterArrToReturn: ", subClusterArrToReturn);
          return(subClusterArrToReturn);

          //return([0,9,9,9]);

      } // end of wcc
      //writeln("clusterArr: ", clusterArr);
      return clusterArr;
    } // end of runWCC
} // end of WellConnectedComponents module