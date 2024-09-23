module WellConnectedComponents {
    // Chapel modules.
    use Reflection;
    use List;
    use Random;
    use IO;
    use Time;
    use Set;
    use Map;
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
        var id: int;                 // cluster id
        var n_member: int;           // Size of the cluster
        var members: domain(int);    // Domain to store cluster members
        var is_wcc: bool = false;    // Indicates if it's a well-connected component
        var is_singleton: bool = false; // Indicates if it's a singleton cluster
        var depth: int;              // Clustering depth

        /** Cluster initializer. */
        proc init(membersArray: [] int) {
            this.id = -1;
            this.n_member = membersArray.size;

            // Initialize an empty domain and add members from the array
            this.members = {1..0};
            this.members += membersArray;
            // Check if it's a singleton cluster (only one member)
            if this.n_member <= 1 then
            this.is_singleton = true;

            this.is_wcc = false;
            this.depth = 0;
        }        
        
        proc init(membersArray: domain(int)) {
            this.id = -1;
            this.n_member = membersArray.size;

            // Initialize an empty domain and add members from the array
            this.members = {1..0};
            this.members += membersArray;
            // Check if it's a singleton cluster (only one member)
            if this.n_member <= 1 then
            this.is_singleton = true;

            this.is_wcc = false;
            this.depth = 0;
        }

        /** Method to remove nodes with degree 1 (to be implemented). */
        proc removeDegreeOne() {
            // Calculate cluster degree and remove nodes with degree 1
            // Update cluster nodes accordingly
        }
    }
 
    // Define a record to encapsulate an array with its own domain
    record DomVarryArray {
        var DOM: domain(1);       // Domain of the array
        var Arr: [DOM] int;         // Array over the domain

        // Constructor to initialize the array with a given domain and data
        proc init(data: [] int) {
            // Initialize the domain based on the size of the data
            this.DOM = {0..data.size-1};
            // Initialize the array over the domain
            this.Arr = [i in DOM] data[i];
        }
    }
    /** Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
    searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
    array that maps the isomorphic vertices of `g1` to those of `g2`.*/
    proc runWCC (g1: SegGraph, st: borrowed SymTab, inputcluster_filePath:string):[] int throws {
        ////////////////////Test area///////////////////////////////////////////////////
        var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
        var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
        var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
        var srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
        var dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
        var segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
        var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
        var clusterArrtemp = wcc(g1);
        var clusterArr = nodeMapGraphG1[clusterArrtemp]; // Map vertices back to original values.

        record ConnectivityMetrics {
            var averageEdgeDisjointPaths: real;
            var threshold: real;
            var isWellConnected: bool;

            proc init() {
                this.averageEdgeDisjointPaths = 0.0;
                this.threshold = 0.0;
                this.isWellConnected = false;
            }
        }

        // Function to calculate the degree of a node within the cluster
        proc findAdjNeighinCluster(cluster: borrowed Cluster, elem: int) throws{
            writeln("////////////////************//calculateDegree begin");

            var Neighbours: domain(int);
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
/*
        // Function to calculate the number of edge-disjoint paths between two nodes in a cluster
        // Uses Max Flow (Ford-Fulkerson or Edmonds-Karp) algorithm, where each edge has capacity 1.
        proc calculateEdgeDisjointPaths(cluster: borrowed Cluster, nodeA: int, nodeB: int): int throws{
            
            const nc: int = cluster.n_member;
            var clusterArr:[0..nc-1] int; 
            var idx = 0;
            for elem in cluster.members {
                clusterArr[idx] = elem;
                idx += 1;
            }
            // Check if nodeA and nodeB are the same
            if nodeA == nodeB then return 0; // No path needed between the same nodes
            
            const (nodeA_found, nodeA_idx) = binarySearch(clusterArr, nodeA);
            const (nodeB_found, nodeB_idx) = binarySearch(clusterArr, nodeB);
            if !nodeA_found || !nodeB_found then return 0;


            // Sparse residual graph
            //const D: domain(2) = {0..nc-1, 0..nc-1};
            //var residual: sparse subdomain(D);

            var residual:[0..nc-1, 0..nc-1] int;
            // Populate sparse residual graph from cluster
            forall i in 0..nc-1 {
                const u = clusterArr[i];
                var Nei_u_in_cluster = findAdjNeighinCluster(cluster, u);
                
                forall v in Nei_u_in_cluster{
                    const (found, idx) = binarySearch(clusterArr, v);
                    if found {
                        residual[u, idx] = 1;
                        residual[idx, u] = 1;
                    }

                }
            }

            // Max Flow from nodeA to nodeB
            var maxFlow = 0;

            // Array to store parent nodes in the path (used to trace augmenting paths)
            var parent: [0..nc-1] int;

            // Breadth-First Search (BFS) to find augmenting paths in the residual graph
            proc bfs(source: int, sink: int, parent: [] int): bool {
                
                var visited: [0..nc-1] bool;
                visited = false;
                
                var queue: list(int);
                queue.pushBack(source);

                visited[source] = true;
                parent[source] = -1;

                var flag: bool = false;

                while !queue.isEmpty() {
                    const u = queue.popBack();

                // Iterate only over neighbors of u in the residual graph
                    for (u, v) in residual.domain {
                        // If there's a residual capacity and v is not visited
                        if !visited[v] && residual[u, v] > 0 {
                            queue.pushBack(v);
                            visited[v] = true;
                            parent[v] = u;

                            // If we reached the sink, stop the search
                            if v == sink {
                                flag = true;
                            }
                        }
                    }
                }
                return flag;
            }

            // Ford-Fulkerson implementation using BFS to find augmenting paths
            while bfs(nodeA_idx, nodeB_idx, parent) {
                    // Find the minimum residual capacity in the augmenting path found by BFS
                    var pathFlow: int;
                    for v in nodeB_idx .. nodeA_idx by -1 {
                        const u = parent[v];
                        pathFlow = min(pathFlow, residual[u, v]);
                    }

                    // Update residual capacities along the path
                    for v in nodeB_idx..nodeA_idx by -1 {
                        const u = parent[v];
                        residual[u, v] -= pathFlow;
                        residual[v, u] += pathFlow; // Reverse flow for residual capacity
                    }

                    // Add path flow to the overall flow
                    maxFlow += pathFlow;
                }

                // Return the maximum number of edge-disjoint paths
                return maxFlow;
            }

        // Function to compute average number of edge-disjoint paths within a cluster
        proc computeAverageEdgeDisjointPaths(cluster: borrowed Cluster): real {
            var totalPaths: int = 0;
            var count: int = 0;

            // Iterate over all unique pairs in the cluster
            for nodeA in cluster.members {
                for nodeB in cluster.members {
                    if nodeA < nodeB {
                         
                        totalPaths += calculateEdgeDisjointPaths(cluster, nodeA, nodeB);
                        count += 1;
                    }
                }
            }

                if count > 0 {
                    return real(totalPaths) / real(count);
                } else {
                    return 0.0;
                }
        }

        // Function to determine if a cluster is well connected based on average paths
        proc assessConnectivity(cluster: borrowed Cluster): ConnectivityMetrics {
            var metrics = ConnectivityMetrics();

            metrics.averageEdgeDisjointPaths = computeAverageEdgeDisjointPaths(cluster);
            
            // Define the threshold (e.g., log10(n))
            metrics.threshold = log10(real(cluster.n_member));

            // Determine connectivity
            metrics.isWellConnected = metrics.averageEdgeDisjointPaths > metrics.threshold;

            writeln("cluster: ", cluster," metrics: ", metrics);

        return metrics;
        }
*/

/////////////////////////////////////////////////////////////////////////////////////////////////////
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
                        writeln("Error: Original node ", originalNode, " not found in nodeMapGraphG1.");
                        writeln("*****************dummy node found");
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
            writeln("////////////////************//calculateDegree begin");

            var Neighbours: domain(int);
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
            var intersectionDomain = Neighbours & cluster;
            writeln("elem : ",elem, " has degree = ",intersectionDomain.size );

            return intersectionDomain.size;
        }

        proc removeDegreeOne(cluster: borrowed Cluster) throws{

            // Iterate over the members and collect elements that need to be removed
            forall elem in cluster.members {
                if calculateDegree(cluster.members, elem) < 2 {
                    cluster.members.remove(elem);
                    //writeln("Marked for removal: ", elem);
                }
            }
            cluster.n_member = cluster.members.size;
            if cluster.n_member <2 then cluster.is_singleton = true;
            writeln("cluster after removeing degree one nodes: ", cluster);
            //return cluster;  // Return the modified cluster
        }
        
        // function is wrong I should call it by edgeCutSize
        proc isWellConnected(cluster: borrowed Cluster, edgeCutSize: int): bool throws {
            writeln("////////////////************isWellConnected begin");

            // Compute the base-10 logarithm of 'numEdges' and take the floor
            var logN = floor(log10(cluster.members.size: real));
            // Convert the result to an integer if needed
            var floorLog10N: int = logN:int;
            
            //Well Connected Function
            if edgeCutSize > floorLog10N {
                writeln("the cluster = ",cluster," is well connected");
                cluster.is_wcc = true;
                writeln("the cluster.is_wcc updated = ",cluster.is_wcc," is well connected");
                return true;
            }

            return false;
        }
        // The created edges is not sorted. should be? 
        proc createVieCutGraph(nodes: domain(int)){
            writeln("////////////////************createVieCutGraph begin");

            var edgeSet:  set((int, int));  // A set to store unique edges as (src, dst) pairs

            //writeln("Nodes are: ", nodes);
            for elem in nodes {
                            
                var node_nei: domain(int);
                
                //writeln("elem is ", elem);
                // Find in-neighbors of the current element
                var inNeigh_elem = dstRG1[segRG1[elem]..<segRG1[elem + 1]];
                //writeln("inNeigh_elem = ", inNeigh_elem);
                node_nei += inNeigh_elem;

                // Find out-neighbors of the current element
                var outNeigh_elem = dstNodesG1[segGraphG1[elem]..<segGraphG1[elem + 1]];
                //writeln("outNeigh_elem = ", outNeigh_elem);
                node_nei += outNeigh_elem;

                var valid_neis = node_nei & nodes;
                //writeln("valid neighbors = ", valid_neis);

                for neigh in valid_neis {
                    edgeSet.add((elem, neigh));
                    edgeSet.add((neigh, elem));
                }
                //writeln("edgeSet- outNeigh added = ", edgeSet);

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


            writeln("src: ", src);
            writeln("dst: ", dst);
            return(src,dst,src.size);
        }

        proc callMinCut(nodes: domain(int)): (int, list(DomVarryArray)) {
            writeln("////////////////************callMinCut begin");

            //bring an int cutSize
            //bring list of uniqu nodes in each new partition
            //should return List or arrys of clusters
            var (src, dst, m) = createVieCutGraph(nodes);

            var cut = c_computeMinCut(src, dst, 10, m);
            // supposed *Viecut called* and it returned cluster1, cluster2
            writeln("!!!!! The returned cut is ", cut);

            var cluster1 = [0, 4, 5 ];  // First array
            var cluster2 = [6, 7, 1, 8, 9, 10, 2];  // Second array

            // Create DomVarryArray instances
            var domVarryArray1 = new DomVarryArray(cluster1);
            var domVarryArray2 = new DomVarryArray(cluster2);

            var cluslist : list(DomVarryArray);
            // Push the instances into the list
            cluslist.pushBack(domVarryArray1);
            cluslist.pushBack(domVarryArray2);
            writeln("cluslist = ", cluslist);
            return(cut, cluslist);
        }


        // Function to write cluster members to a file
        proc writeClusterToFile(cluster: borrowed Cluster) throws {
            writeln("////////////////************writeClusterToFile begin");

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
                writeln("member :", member:string);
                fileWriter.writeln(member:string);
            }
            
            // Close the file to ensure data is flushed. 
            try fileWriter.close();
            try file.close();
            
            writeln("WCC written to ", filename);
        }



        proc wccHelper(cluster: borrowed Cluster): list(int) throws{
            writeln("////////////////************wccHelper begin");

            // Initialize an empty list to collect well-connected clusters
            var allWCC: list(int);
            
            // Base case: check if a well connected cluster is found
            if cluster.is_wcc == true {
                writeln("WC Cluster found = ", cluster.members);
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
            if !cluster.is_singleton && cluster.n_member > 10 {

                // Update sub-cluster properties
                var currentDpeth = cluster.depth;
                var currentID = cluster.id;

                // Perform min-cut to get cutSize and sub-clusters
                var (cutSize, clusterList) = callMinCut(cluster.members);
                
                if !isWellConnected(cluster, cutSize){
                    // Iterate over each sub-cluster
                    //forall minCutReturnedArr in clusterList{

                    for minCutReturnedArr in clusterList{

                        writeln("minCutReturnedArr = ", minCutReturnedArr);
                        var subCluster = new owned Cluster(minCutReturnedArr.Arr);
                        subCluster.depth = currentDpeth + 1;
                        subCluster.id = currentID;

                        writeln("subCluster created = ", subCluster);

                        var newSubClusters: list(int, parSafe=true);

                        // Collect clusters from recursive call
                        newSubClusters = wccHelper(subCluster);

                       
                        // Use a loop to add elements from newMappings to allmappings
                        for findings in newSubClusters do allWCC.pushBack(findings);
                        writeln("newSubClusters found :", allWCC);
                    }

                }
            }

            return allWCC;
        }

        proc wcc(g1: SegGraph): [] int throws {
            writeln("graph loaded with ", g1.n_vertices," and ", g1.n_edges," edges");
            writeln("we are lading the clusters....");
            
            var results: list(int, parSafe=true);

            //var clusters = readClustersFile("/scratch/users/md724/DataSets/wcc/clustering.tsv");
            var clusters = readClustersFile(inputcluster_filePath);

            // Print each cluster with its mapped nodes
            for key in clusters.keys() {
                writeln("Cluster ID: ", key);
                
                var clusterInit = new owned Cluster(clusters[key]);
                clusterInit.id = key;
                writeln("Cluster created = ", clusterInit);
                
                //writeClusterToFile(clusterInit);
                //if clusterInit.id == 905 then findAdjNeighinCluster(clusterInit, 415);
                
                if !clusterInit.is_singleton && !clusterInit.is_wcc {
                    
                    //ClusterKCoreDecomposition(clusterInit.members,2);
                    writeln("we are here");
                    var newResults = wccHelper(clusterInit);
                    
                    for mapping in newResults do results.pushBack(mapping);

                }
            }

            
            //var clusterInit = new owned Cluster(inputClusterArr);
            //writeln("Cluster created = ", clusterInit);
            var subClusterArrToReturn: [0..#results.size](int);
            for i in 0..#results.size do subClusterArrToReturn[i] = results(i);
            writeln ("subClusterArrToReturn: ", subClusterArrToReturn);
            return(subClusterArrToReturn);

            //return([0,9,9,9]);

        } // end of WCC
        writeln("clusterArr: ", clusterArr);
        return clusterArr;
    } //end of runWCC
} // end of WellConnectedComponents module