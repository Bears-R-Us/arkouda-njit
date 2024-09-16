module SubgraphIsomorphism {
    // Chapel modules.
    use Reflection;
    use List;
    use Random;
    use IO;
    use Time;
    use Set;
    use Map;
    use Sort;

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

    class Cluster {
        var n_member: int;           // Size of the cluster
        var members: domain(int);    // Domain to store cluster members
        var is_wcc: bool = false;    // Indicates if it's a well-connected component
        var is_singleton: bool = false; // Indicates if it's a singleton cluster
        var depth: int;              // Clustering depth

        /** Cluster initializer. */
        proc init(membersArray: [] int) {
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
 

    /** Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
    searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
    array that maps the isomorphic vertices of `g1` to those of `g2`.*/
    proc runVF2 (g1: SegGraph, g2: SegGraph, st: borrowed SymTab):[] int throws {
        var TimerArrNew:[0..30] real(64) = 0.0;
        var numIso: int = 0;

        // Extract the g1/G/g information from the SegGraph data structure.
        var srcNodesG1Dist = toSymEntry(g1.getComp("SRC"), int).a;
        var dstNodesG1Dist = toSymEntry(g1.getComp("DST"), int).a;
        var segGraphG1Dist = toSymEntry(g1.getComp("SEGMENTS"), int).a;
        var srcRG1Dist = toSymEntry(g1.getComp("SRC_R"), int).a;
        var dstRG1Dist = toSymEntry(g1.getComp("DST_R"), int).a;
        var segRG1Dist = toSymEntry(g1.getComp("SEGMENTS_R"), int).a;
        var nodeMapGraphG1Dist = toSymEntry(g1.getComp("VERTEX_MAP"), int).a;

        // Extract the g2/H/h information from the SegGraph data structure.
        var srcNodesG2Dist = toSymEntry(g2.getComp("SRC"), int).a;
        var dstNodesG2Dist = toSymEntry(g2.getComp("DST"), int).a;
        var segGraphG2Dist = toSymEntry(g2.getComp("SEGMENTS"), int).a;
        var srcRG2Dist = toSymEntry(g2.getComp("SRC_R"), int).a;
        var dstRG2Dist = toSymEntry(g2.getComp("DST_R"), int).a;
        var segRG2Dist = toSymEntry(g2.getComp("SEGMENTS_R"), int).a;
        var nodeMapGraphG2Dist = toSymEntry(g2.getComp("VERTEX_MAP"), int).a;

        // Get the number of vertices and edges for each graph.
        var nG1 = nodeMapGraphG1Dist.size;
        var mG1 = srcNodesG1Dist.size;
        var nG2 = nodeMapGraphG2Dist.size;
        var mG2 = srcNodesG2Dist.size;

        //******************************************************************************************
        //******************************************************************************************
        // OLIVER NOTE: 
        // Relabeled node labels and edge relationships id values so those of H match those of G to 
        // speed up semantic checks. 
        // 
        // In the SegGraph data structure for property graphs, there could be many different types 
        // of labels and relationships. Therefore, we will do some preprocessing here to relabel
        // all labels and relationships and place them into sets for quick intersections.
        //
        // This assumes that all labels and relationships are strings BUT some labels and 
        // relationships can be unsigned or regular integers. If this is the case then borrowed 
        // SegStringSymEntry below would be empty. We currently do not do a check for this since all
        // of our test data has string labels and relationships BUT we should fix this in the 
        // future. 
        //
        // All of the code contained between the //**** comments (roughly ~100 lines) should
        // probably eventually be a function that lives where SegGraph is defined to perform a 
        // globalized relabeling and creating arrays of sets to speed up comparing the labels and
        // relationships of two or more different graphs.
        var edgeRelationshipsGraphG1 = (g1.getComp("EDGE_RELATIONSHIPS"):(borrowed MapSymEntry(
                                            string, (string, borrowed SegStringSymEntry)
                                        ))).stored_map;
        var nodeLabelsGraphG1 = (g1.getComp("VERTEX_LABELS"):(borrowed MapSymEntry(
                                            string, (string, borrowed SegStringSymEntry)
                                        ))).stored_map;

        var edgeRelationshipsGraphG2 = (g2.getComp("EDGE_RELATIONSHIPS"):(borrowed MapSymEntry(
                                            string, (string, borrowed SegStringSymEntry)
                                        ))).stored_map;
        var nodeLabelsGraphG2 = (g2.getComp("VERTEX_LABELS"):(borrowed MapSymEntry(
                                            string, (string, borrowed SegStringSymEntry)
                                        ))).stored_map;

        var relationshipStringToInt, labelStringToInt = new map(string, int);

        // Create global relationship mapper for G1 and G2.
        var id = 0;
        for k in edgeRelationshipsGraphG1.keys() {
            var segString = getSegString(edgeRelationshipsGraphG1[k][1].name, st);
            for i in 0..segString.size-1 {
                var val = segString[i];
                if !relationshipStringToInt.contains(val) {
                    relationshipStringToInt.add(val, id);
                    id += 1;
                }
            }
        }
        for k in edgeRelationshipsGraphG2.keys() {
            var segString = getSegString(edgeRelationshipsGraphG2[k][1].name, st);
            for i in 0..edgeRelationshipsGraphG2[k][1].size-1 {
                var val = segString[i];
                if !relationshipStringToInt.contains(val) {
                    relationshipStringToInt.add(val, id);
                    id += 1;
                }
            }
        }
        
        // Create global label mapper for G1 and G2.
        id = 0;
        for k in nodeLabelsGraphG1.keys() {
            var segString = getSegString(nodeLabelsGraphG1[k][1].name, st);
            for i in 0..nodeLabelsGraphG1[k][1].size-1 {
                var val = segString[i];
                if !labelStringToInt.contains(val) {
                    labelStringToInt.add(val, id);
                    id += 1;
                }
            }
        }
        for k in nodeLabelsGraphG2.keys() {
            var segString = getSegString(nodeLabelsGraphG2[k][1].name, st);
            for i in 0..nodeLabelsGraphG2[k][1].size-1 {
                var val = segString[i];
                if !labelStringToInt.contains(val) {
                    labelStringToInt.add(val, id);
                    id += 1;
                }
            }
        }

        // Create new "arrays of sets" to make semantic checks quicker by allowing usage of Chapel's
        // internal hash table intersections via sets.
        var convertedRelationshipsG1Dist = makeDistArray(g1.n_edges, domain(int));
        var convertedRelationshipsG2Dist = makeDistArray(g2.n_edges, domain(int));
        var convertedLabelsG1Dist = makeDistArray(g1.n_vertices, domain(int));
        var convertedLabelsG2Dist = makeDistArray(g2.n_vertices, domain(int));

        for (k,v) in zip(edgeRelationshipsGraphG1.keys(), edgeRelationshipsGraphG1.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedRelationshipsG1Dist[i].add(relationshipStringToInt[mapper[x]]);
        }

        for (k,v) in zip(edgeRelationshipsGraphG2.keys(), edgeRelationshipsGraphG2.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do
                convertedRelationshipsG2Dist[i].add(relationshipStringToInt[mapper[x]]);
        }

        for (k,v) in zip(nodeLabelsGraphG1.keys(), nodeLabelsGraphG1.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedLabelsG1Dist[i].add(labelStringToInt[mapper[x]]);
        }

        for (k,v) in zip(nodeLabelsGraphG2.keys(), nodeLabelsGraphG2.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedLabelsG2Dist[i].add(labelStringToInt[mapper[x]]);
        }
        //******************************************************************************************
        //******************************************************************************************

        //************************************LOCALIZATION******************************************
        var srcNodesG1: [0..<mG1] int = srcNodesG1Dist;
        var dstNodesG1: [0..<mG1] int = dstNodesG1Dist;
        var segGraphG1: [0..<nG1+1] int = segGraphG1Dist;
        var srcRG1: [0..<mG1] int = srcRG1Dist;
        var dstRG1: [0..<mG1] int = dstRG1Dist;
        var segRG1: [0..<nG1+1] int = segRG1Dist;
        var nodeMapGraphG1: [0..<nG1] int = nodeMapGraphG1Dist;
        var convertedRelationshipsG1: [0..<mG1] domain(int) = convertedRelationshipsG1Dist;
        var convertedLabelsG1: [0..<nG1] domain(int) = convertedLabelsG1Dist;

        var srcNodesG2: [0..<mG2] int = srcNodesG2Dist;
        var dstNodesG2: [0..<mG2] int = dstNodesG2Dist;
        var segGraphG2: [0..<nG2+1] int = segGraphG2Dist;
        var srcRG2: [0..<mG2] int = srcRG2Dist;
        var dstRG2: [0..<mG2] int = dstRG2Dist;
        var segRG2: [0..<nG2+1] int = segRG2Dist;
        var nodeMapGraphG2: [0..<nG2] int = nodeMapGraphG2Dist;
        var convertedRelationshipsG2: [0..<mG2] domain(int) = convertedRelationshipsG2Dist;
        var convertedLabelsG2: [0..<nG2] domain(int) = convertedLabelsG2Dist;
        //******************************************************************************************
        var IsoArr:[0..3] int = [0,1,2];

        // Define the clusters as arrays
        var cluster1 = [0, 4, 5, 6, 7, 1, 8, 9, 10, 2];  // First array
        var cluster2 = [3, 11, 12, 13];  // Second array
        var cluster3 = [14, 15, 17, 16, 18, 19];  // Third array
        var cluster4 = [14];  // Forth array

        wcc (g1, cluster1);

        writeln("\n_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*");
        writeln("\n_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*");
        writeln("\n_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*");
        
        proc calculateDegree(cluster: domain(int), elem: int): int throws{
            var Neighbours: domain(int);
            var inNeigh_elem  = dstRG1[segRG1[elem]..<segRG1[elem + 1]];
            var outNeigh_elem = dstNodesG1[segGraphG1[elem]..<segGraphG1[elem + 1]];
            Neighbours += inNeigh_elem;
            Neighbours += outNeigh_elem;

            var intersectionDomain = Neighbours & cluster;
            //writeln("processing node ", elem);
            //writeln("intersectionDomain = ", intersectionDomain);
            //writeln("degree of elem(", elem, ") = ",intersectionDomain.size );
            return(intersectionDomain.size);

        }
        proc removeDegreeOne(cluster: borrowed Cluster) throws{

            // Iterate over the members and collect elements that need to be removed
            forall elem in cluster.members {
                if calculateDegree(cluster.members, elem) < 2 {
                    cluster.members.remove(elem);
                    writeln("Marked for removal: ", elem);
                }
            }
            cluster.n_member = cluster.members.size;
            if cluster.n_member <2 then cluster.is_singleton = true;
            //return cluster;  // Return the modified cluster
        }
        // function is wrong I should call it by edgeCutSize
        proc isWellConnected(cluster: borrowed Cluster, edgeCutSize: int): bool throws {
            var total: int;
            total = + reduce forall elem in cluster.members do
                calculateDegree(cluster.members, elem);
            writeln("total = ", total);

            var numEdges: int;

            if total % 2 == 0 {
                // 'total' is even, proceed with the division
                numEdges = total / 2;
                writeln("numEdges: ", numEdges);
            } else {
                // 'total' is odd, throw an error
                throw new Error("Error: total degree is odd.");
            }

            if numEdges > 0 then {
                // Compute the base-10 logarithm of 'numEdges' and take the floor
                var logValue = floor(log10(numEdges: real));

                // Convert the result to an integer if needed
                var floorLog10NumEdges: int = logValue:int;

                // Output the result
                writeln("The floor of log base 10 of ", numEdges, " is: ", floorLog10NumEdges);
            } else {
                throw new Error("Error: 'numEdges' must be a positive integer.");
            }

            // Determine the return value later
            // For now, return true if the cluster is well-connected
            return true;
        }

        

        //Assumptions:
        //The graph is undirected, and each edge is represented in both directions in src and dst. Oliver?
        //The cluster (graph) is connected.
/*
        // Function to perform a simple randomized min-cut (Karger's algorithm)
        proc callMinCut(nodes: domain(int)) {

            // Number of nodes remaining
            var remainingNodes = nodes.size;
            var total:int;
            total = + reduce forall elem in nodes do
                calculateDegree(nodes, elem);
            
            var edgesSize: int = total/2; 
            var nodesArr: [0..<nodes.size] int;
            nodesArr += nodes;

            var supernodes = nodesArr;

            // Create a random number generator (RNG) stream
            var rng = new owned RandomStream(int);

            // Randomized contraction process
            while remainingNodes > 2 {
                // Randomly select an edge
                var edgeIndex = Random.rand(0, edges.size - 1);
                var (u, v) = edges[edgeIndex];

                // Get supernodes for u and v
                var su = supernodes[u];
                var sv = supernodes[v];

                // If they are already in the same supernode, skip
                if su == sv {
                    edges.remove(edgeIndex);
                    continue;
                }


        }
        }
*/
        proc callMinCut(nodes: domain(int)) {
            writeln("MinCut called");
            //bring an int cutSize
            //bring list of uniqu nodes in each new partition
        }
        proc wccHelper(cluster: borrowed Cluster): Cluster throws{
            // Base case: check if a well connected cluster is found
            if cluster.is_wcc == true {
                writeln("WC Cluster found = ", cluster.members);
                // Process the found solution
                //for elem in state.core do allmappings.pushBack(elem);
                return cluster;
            }
            removeDegreeOne(cluster);

            if !cluster.is_singleton == true && cluster.n_member > 10 && !cluster.is_wcc == true{
                
                var (cutSize, clusterNew1, clusterNew2) = callMinCut(cluster.members);
                
                isWellConnected(cluster, cutSize);

                if !cluster.is_wcc == true {
                    //create new cluster for each and call the wccHelper
                    // Viecut brings src , dst?!
                    forallreturnedcluster{}
                    wccHelper();
                }
                }

            }
            /*
            for NewCluster in cuttedClusters{
                wccHelper(NewCluster);
            }
            */
            var temp = cluster;
            return(temp);
        }
        proc wcc(g1: SegGraph, inputClusterArr: [?D] int): [] int throws {
            writeln("Running");
            var clusterInit = new owned Cluster(inputClusterArr);
            writeln("Cluster created = ", clusterInit);

            if !clusterInit.is_singleton && !clusterInit.is_wcc {
                wccHelper(clusterInit);
            }
            //wccHelper(clusterInit);
            writeln("Cluster after call and return = ", clusterInit);
            return([0,9,9,9]);

        } // end of WCC

        
        return IsoArr;
    } //end of runWCC
} // end of WellConnected module

        

