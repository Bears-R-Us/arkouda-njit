module SubgraphIsomorphism {
    // Chapel modules.
    use Reflection;
    use List;

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
    use AryUtil;
    // Global 
    // Global counter for isomorphisms
    var globalIsoCounter: atomic int;
    
    proc runUllmann(g1: SegGraph, g2: SegGraph, SubgraphDegree: [?D1] int, 
            graphDegree: [?D2] int, Orig_Label_Mapper_G_to_Pass: [?D3] string, 
            Orig_Label_Mapper_H_to_Pass: [?D4] string, Orig_Relationships_Mapper_G_to_Pass: [?D5] string, 
            Orig_Relationships_Mapper_H_to_Pass: [?D6] string) throws{


        // Extract the G information from PropGraph DS
        var srcNodesG1 = toSymEntry(g1.getComp("SRC"), int).a;
        var dstNodesG1 = toSymEntry(g1.getComp("DST"), int).a;
        var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS"), int).a;
        var edgeRelationshipsGraphG1 = toSymEntry(g1.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var nodeLabels_GraphG1 = toSymEntry(g1.getComp("VERTEX_LABELS"), domain(int)).a;
        var nodeMap_GraphG1 = toSymEntry(g1.getComp("NODE_MAP"), int).a;

        // Extract the H information from PropGraph DS
        var srcNodesG2 = toSymEntry(g2.getComp("SRC"), int).a;
        var dstNodesG2 = toSymEntry(g2.getComp("DST"), int).a;
        var segGraphG2 = toSymEntry(g2.getComp("SEGMENTS"), int).a;
        var edgeRelationshipsGraphG2 = toSymEntry(g2.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var nodeLabels_GraphG2 = toSymEntry(g2.getComp("VERTEX_LABELS"), domain(int)).a;  

        //writeln("nodeMap_GraphG1 = ", nodeMap_GraphG1);
        //writeln("dstNodesG1 = ", dstNodesG1);        
        
        //writeln("srcNodesG2 = ", srcNodesG2);
        //writeln("dstNodesG2 = ", dstNodesG2);
        
        var IsoList = ullmannSubgraphIsomorphism11(g1, g2, SubgraphDegree, graphDegree);     
        var IsoArrtemp = IsoList.toArray();
        writeln("IsoArrtemp = ", IsoArrtemp);

        var IsoArr = nodeMap_GraphG1[IsoArrtemp];

        // Function to check is there any edge from Source node to Destination node. 
        // If there is it will get back the Original Relationship (Label) from the mapped INDEX
        proc PropGraphRelationshipMapper(segGraph, dstNodes, edgeRelationshipsGraph, 
                                        fromNode: int, toNode: int, Mapper): (bool, string) throws {
            //writeln("-----------------PropGraphRelationshipMapper called-------------------\n");
            var BoolValue : bool = false;
            var StringLabelValue : string;

            // Check if there is an edge from "fromNode" to "toNode" in PropGraph
            var adj_list_of_fromNode_start = segGraph[fromNode];
            var adj_list_of_fromNode_end = segGraph[fromNode+1]-1;
            
            var Edge_found = bin_search_v(dstNodes, adj_list_of_fromNode_start, adj_list_of_fromNode_end, toNode);

            if Edge_found > -1 then {
                BoolValue = true;
                
                var setToConvert = edgeRelationshipsGraph[Edge_found];
                for elemnts in setToConvert{
                    StringLabelValue = Mapper[elemnts];
                }

            }

            return (BoolValue, StringLabelValue);
        }  // end of PropGraphRelationshipMapper

        proc PropGraphNodeLabelMapper(nodeLabels_Graph, srearchNode: int, Mapper): (bool, string) throws {
            //writeln("-----------------PropGraphNodeLabelMapper called-------------------\n");

            var BoolValue : bool = false;
            var StringLabelValue : string;

        
            var setToConvert =  nodeLabels_Graph[srearchNode];

            // remember make a time to write an IF to check the existing of index!!
            // if it was out of range return FALSE
            for elemnts in setToConvert{
                    StringLabelValue = Mapper[elemnts];
            }
            if StringLabelValue.size > 0 then {
            BoolValue = true;
            } // If there is at least 1 label, print out the string representation of the one at index 0.
            
            return (BoolValue, StringLabelValue);
        }
    
        // Function to check if the vertex v of H can be added to the current mapping
        // Returns true if it can be added, false otherwise
        proc isIsomorphic(v: int, mapping: [?D] int): bool throws {
            //writeln("-----------------isIsomorphic called-------------------");
            //writeln("-----------------v = ",v,"mapping = ", mapping,"-------------------");
            var i = mapping[v];  // Vertex i in G corresponds to vertex v in H

            var label_i_G1 = PropGraphNodeLabelMapper(nodeLabels_GraphG1, i, Orig_Label_Mapper_G_to_Pass)[1];
            var label_v_G2 = PropGraphNodeLabelMapper(nodeLabels_GraphG2, v, Orig_Label_Mapper_H_to_Pass)[1];

            // Check if the node labels are the same
            if label_i_G1 != label_v_G2 {
                return false;
            }

            
            for u in 0..v-1 {
                //writeln("$$$$$$$$$ We reached isIsomorphic 2");
                //writeln(" u= ",u, " mapping[u]= ", mapping[u],"\n\n");

                if mapping[u] > -1 {  // If u in H is mapped to some vertex in G
                                    // Check if there is an edge from u to v in H
                    //writeln("if mapping[u] > -1 {");
                    var (flag_u_v_G2, rel_u_v_G2) = PropGraphRelationshipMapper(segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, u, v, Orig_Relationships_Mapper_H_to_Pass);

                    if flag_u_v_G2 {
                        // Check if there is an edge from mapping[u] to mapping[v] in G
                        // And check if the edge labels are the same
                        //writeln("We have an edge in subgraph. NOW lets check in G with mapped nodes:\n\n");
                        var um = mapping[u];
                        var vm = mapping[v];
                        
                        var (flag_um_vm_G1, rel_um_vm_G1) = PropGraphRelationshipMapper(segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, um, vm, Orig_Relationships_Mapper_G_to_Pass);
                        
                        if !flag_um_vm_G1 || (rel_u_v_G2 != rel_um_vm_G1) {
                            //writeln("-----------------isIsomorphic returned False1");
                            return false;
                        }
                    }

                    // Check if there is an edge from v to u in H
                    var (flag_v_u_G2, rel_v_u_G2) = PropGraphRelationshipMapper(segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, v, u, Orig_Relationships_Mapper_H_to_Pass);
                    if flag_v_u_G2 { 

                        // Check if there is an edge from mapping[v] to mapping[u] in G
                        // And check if the edge labels are the same
                        var um = mapping[u];
                        var vm = mapping[v];

                        var (flag_vm_um_G1, rel_vm_um_G1) = PropGraphRelationshipMapper(segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, vm, um, Orig_Relationships_Mapper_G_to_Pass);

                        if !flag_vm_um_G1 || rel_v_u_G2 != rel_vm_um_G1{
                        //if um_found<0 || u_found <0{
                            //writeln("if !PropGraphRelationshipMapper(G, vm, um, SymTablePassed)[0] || !PropGraphRelationshipMapper(H, v, u, SymTablePassed)[0]{");
                            //writeln("-----------------isIsomorphic returned False2");
                            return false;
                        }
                    }
                }
            }
            //writeln("isiso return true ");
            //writeln("-----------------isIsomorphic returned True");

            return true;
        }
        
        // Recursive function for Ullmann's subgraph isomorphism algorithm
        proc ullmannSubgraphIsomorphism11Helper(g1: SegGraph, g2: SegGraph, v: int, 
                                                visited: [?D1] bool, mapping: [?D2] int, 
                                                graphDegree: [?D3] int): list(int)  throws {
            //writeln("-----------------ullmannSubgraphIsomorphism11Helper called-------------------");
            //writeln("-----------------v = ",v," visited = ", visited,"mapping = ", mapping,"-------------------");

            var localIsoList: list(int, parSafe=true);  // List to store the isomorphisms found in the current branch
            var localIsoCounter = 0;  // Count the number of isomorphisms found in the current branch
            
            for i in 0..g1.n_vertices-1 {
                if (!visited[i] && graphDegree[i] >= 1) { 
                    //writeln("Here 1");
                    visited[i] = true;  // Mark the vertex as visited
                    mapping[v] = i;  // Add the vertex to the current mapping
                    // If the vertex can be added to the current mapping
                    if (isIsomorphic(v, mapping )) {
                        // If all vertices in H have been visited
                        //writeln("Here 2");
                        if (v >= g2.n_vertices-1) {
                            //writeln("Here 3");
                            var isComplete = true;  // Check if all vertices in the subgraph have been mapped
                            for j in 0..g2.n_vertices-1 {
                                if (mapping[j] < 0) {
                                    isComplete = false;
                                    break;
                                }
                            }
                            // If the mapping is complete, add the current mapping to the isomorphism list
                            if (isComplete) {
                                //writeln("Here 4");
                                //writeln("mapping = ", mapping);
                                for elm in mapping{
                                    localIsoList.pushBack(elm);
                                    //writeln("localIsoList = ", localIsoList);
                                }    
                            }
                        }
                        else {
                            //writeln("Here 5");
                            // Recursively call the function for the next vertex
                            var subIsoList = ullmannSubgraphIsomorphism11Helper(g1, g2, v+1, visited, mapping, graphDegree);
                            //writeln("subIsoList= ",subIsoList );
                            if (subIsoList.size > 0) {
                                // Add isomorphisms found in the sub-branch to the current isomorphism list
                                for elm in subIsoList {
                                    localIsoList.pushBack(elm);
                                    //writeln("pushBack of ",isoMapping );
                                }
                            }
                        }
                    }
                    // Backtrack: unvisit the vertex and remove it from the mapping
                    visited[i] = false;
                    mapping[v] = -1;
                }
            }
            //writeln("localIsoList= ", localIsoList);
            return localIsoList;  // Return the list of isomorphisms found in the current branch
        } // end of ullmannSubgraphIsomorphism11Helper

        // Ullmann's subgraph isomorphism algorithm
        //proc ullmannSubgraphIsomorphism11(G: SegGraph, H: SegGraph, subGraphVerticesSortedByDegree: [?D1] int, 
        //                                   graphDegree: [?D2] int) throws {

        proc ullmannSubgraphIsomorphism11(g1: SegGraph, g2: SegGraph, SubgraphDegree: [?D1] int, 
            graphDegree: [?D2] int): list(int) throws {

            var subIsoListToReturn: list(int, parSafe = true);
            //writeln("-----------------ullmannSubgraphIsomorphism11 called-------------------");

            //writeln("subIsoListToReturn at the begining = ",subIsoListToReturn);

            // // Create an array to hold the vertices sorted by degree
            // var subGraphVerticesSortedByDegree: [1..H.numVertices] int;
            // for v in 1..H.numVertices {
            //     subGraphVerticesSortedByDegree[v] = v;
            // }

            // // Sort the array based on degrees in descending order
            // for i in 1..H.numVertices {
            //     for j in i+1..H.numVertices {
            //         if H.nodeDegree[subGraphVerticesSortedByDegree[i]] < H.nodeDegree[subGraphVerticesSortedByDegree[j]] {
            //             var tmp = subGraphVerticesSortedByDegree[i];
            //             subGraphVerticesSortedByDegree[i] = subGraphVerticesSortedByDegree[j];
            //             subGraphVerticesSortedByDegree[j] = tmp;
            //         }
            //     }
            // }

            // Parallelize over the vertices of subGraph based on degree order!
            // Check it realy changes the running time? I have doubt because of parallelism!
            forall idx in 0..g2.n_vertices-1 with(ref subIsoListToReturn){
                //var v = subGraphVerticesSortedByDegree[idx];
                var v = idx;
                var visited: [0..g1.n_vertices-1] bool;  // Array to keep track of visited vertices
                var mapping: [0..g2.n_vertices-1] int;  // Array for the current mapping
            
                mapping = -1;  // Initialize the mapping array to -1 (indicating no mapping)
                visited = false;  // Initialize all vertices as unvisited
                // Find isomorphisms for the current vertex v
                var subIsoList = ullmannSubgraphIsomorphism11Helper(g1, g2, v, visited, mapping, graphDegree);
                //writeln("$$$$$$ WE GET HERE 2");
                //writeln("subIsoList =", subIsoList);
                //writeln("subIsoList.size = ", subIsoList.size);
                //writeln("subIsoList = ",subIsoList);

                

                if (subIsoList.size > 0) {
                    // Print isomorphisms found by the current task without merging
                    //writeln("Passedjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjjj");
                    //writeln("subIsoListToReturn =", subIsoListToReturn);
                    var taskIsoCounter = 0;
                    for isoElm in subIsoList {
                        //writeln("isoElm",isoElm);
                        //taskIsoCounter += 1;
                        subIsoListToReturn.pushBack(isoElm);
                    }
                    
                    // Add the number of isomorphisms found by the current task to the global counter
                    globalIsoCounter.add(taskIsoCounter);
                }
            }
            //subIsoListToReturn = subIsoList;
            // Print the total number of isomorphisms found
            //writeln("Total isomorphisms found: ", globalIsoCounter.read());
            //writeln("subIsoListToReturn :",subIsoListToReturn);
            //return (subIsoListToReturn, globalIsoCounter.read());
            return (subIsoListToReturn);
        } // end of ullmannSubgraphIsomorphism11

        return(IsoArr, IsoArr.size);
    }// end of runUllmann    
} // end of module