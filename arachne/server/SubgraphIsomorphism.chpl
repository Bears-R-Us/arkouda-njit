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
    // Global counter for isomorphisms
    var globalIsoCounter: atomic int;
    //var SymTablePassed: SymTab;
    // Function to check is there any edge from Source node to Destination node. 
    // If there is it will get back the Original Relationship (Label) from the mapped INDEX
    proc PropGraphRelationshipMapper(PropGraph: SegGraph, fromNode: int, toNode: int, SymTablePassed: borrowed SymTab): (bool, string) throws {
        var BoolValue : bool = false;
        var StringLabelValue : string;

        var srcNodes = toSymEntry(PropGraph.getComp("SRC"), int).a;
        var dstNodes = toSymEntry(PropGraph.getComp("DST"), int).a;
        var segGraph = toSymEntry(PropGraph.getComp("SEGMENTS"), int).a;
        var edgeRelationshipsGraph = toSymEntry(PropGraph.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        
        var relationship_mapper_Graph_entry = toSegStringSymEntry(PropGraph.getComp("EDGE_RELATIONSHIPS_MAP"));
        var relationship_mapper_Graph = assembleSegStringFromParts(relationship_mapper_Graph_entry.offsetsEntry, relationship_mapper_Graph_entry.bytesEntry, SymTablePassed);                      

        // Check if there is an edge from "fromNode" to "toNode" in PropGraph
        var adj_list_of_fromNode_start = segGraph[fromNode];
        var adj_list_of_fromNode_end = segGraph[fromNode+1]-1;
        //writeln("PropGraphRelationshipMapper CALLED FOR = ","( fromNode = ", fromNode, " toNode = ", toNode," )");
        
        var Edge_found = bin_search_v(dstNodes, adj_list_of_fromNode_start, adj_list_of_fromNode_end, toNode);
        //writeln("srcNodes =", srcNodes);
        //writeln("dstNodes = ",dstNodes );
        //writeln("Edge_found = ",Edge_found );
        if Edge_found > -1 then {
            BoolValue = true;
            var setToConvert = edgeRelationshipsGraph[Edge_found];
            //writeln("edgeRelationshipsGraph[Edge_found] = ", edgeRelationshipsGraph[Edge_found]);
            for elemnts in setToConvert{
                StringLabelValue = relationship_mapper_Graph[elemnts];
            }

        }
        //writeln("StringLabelValue = ",StringLabelValue);
        //writeln("BoolValue = ", BoolValue);
        return (BoolValue, StringLabelValue);

    }
    proc PropGraphNodeLabelMapper(PropGraph: SegGraph, srearchNode: int, SymTablePassed: borrowed SymTab): (bool, string) throws {
        var BoolValue : bool = false;
        var StringLabelValue : string;

        // Extract the graph information needed for Graph Vertex Labels! 
        var nodeLabels_Graph = toSymEntry(PropGraph.getComp("VERTEX_LABELS"), domain(int)).a;
        var label_mapper_Graph_entry = toSegStringSymEntry(PropGraph.getComp("VERTEX_LABELS_MAP"));
        var label_mapper_Graph = assembleSegStringFromParts(label_mapper_Graph_entry.offsetsEntry, label_mapper_Graph_entry.bytesEntry, SymTablePassed);
        
        var setToConvert =  nodeLabels_Graph[srearchNode];
        // remember make a time to write an IF to check the existing of index!!
        // if it was out of range return FALSE
        for elemnts in setToConvert{
                StringLabelValue = label_mapper_Graph[elemnts];
        }
        if StringLabelValue.size > 0 then {
           BoolValue = true;
        } // If there is at least 1 label, print out the string representation of the one at index 0.
        /*if PropGraph.hasComp("NODE_MAP"){
           var NodeMaplVAr = toSymEntry(PropGraph.getComp("NODE_MAP"));
           writeln("*********************55555555555555555555555***********************");
           writeln("NodeMaplVAr = ", NodeMaplVAr );
        }   
        else 
        {
           writeln("WE HAVE NOTHING HERE"); 
        } */   
        
        return (BoolValue, StringLabelValue);
    }

    // Function to check if the vertex v of H can be added to the current mapping
    // Returns true if it can be added, false otherwise
    proc isIsomorphic(G: SegGraph, H: SegGraph, v: int, mapping: [?D] int, SymTablePassed: borrowed SymTab): bool throws {
        var i = mapping[v];  // Vertex i in G corresponds to vertex v in H
/*        
        // Extract the graph information needed for G - Main Graph 
        
        var srcG = toSymEntry(G.getComp("SRC"), int).a;
        var dstG = toSymEntry(G.getComp("DST"), int).a;
        var segG = toSymEntry(G.getComp("SEGMENTS"), int).a;
        // Edge Relashionships (Labels) 
        var edgeRelationshipsG = toSymEntry(G.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var relationship_mapper_G_entry = toSegStringSymEntry(G.getComp("EDGE_RELATIONSHIPS_MAP"));
        var relationship_mapper_G = assembleSegStringFromParts(relationship_mapper_G_entry.offsetsEntry, relationship_mapper_G_entry.bytesEntry, SymTablePassed);                      

        // Extract the graph information needed for H - Subgrapg 
        var nodeLabelsH = toSymEntry(H.getComp("VERTEX_LABELS"), domain(int)).a;

        var srcH = toSymEntry(H.getComp("SRC"), int).a;
        var dstH = toSymEntry(H.getComp("DST"), int).a;
        var segH = toSymEntry(H.getComp("SEGMENTS"), int).a;
        // Edge Relashionships (Labels)  
        var edgeRelationshipsH = toSymEntry(H.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var relationship_mapper_H_entry = toSegStringSymEntry(H.getComp("EDGE_RELATIONSHIPS_MAP"));
        var relationship_mapper_H = assembleSegStringFromParts(relationship_mapper_H_entry.offsetsEntry, relationship_mapper_H_entry.bytesEntry, SymTablePassed);
        writeln("**********************************\n");
        writeln("Extracted information needed of G:\n");
        writeln("**********************************\n");

        writeln("srcG = ", srcG);
        writeln("dstG = ", dstG);
        writeln("segG = ", segG);
        writeln("edgeRelationshipsG = ", edgeRelationshipsG);
        writeln("edgeRelationshipsG[0] = ", edgeRelationshipsG[0]);
        
        writeln("relationship_mapper_G[0] = ", relationship_mapper_G[0]);
        writeln("relationship_mapper_G[1] = ", relationship_mapper_G[1]);
        writeln("relationship_mapper_G[2] = ", relationship_mapper_G[2]);
        writeln("relationship_mapper_G[3] = ", relationship_mapper_G[3]);


        //writeln("relationship_mapper_G[X] = ", relationship_mapper_G[X]);
 */       
 /*       writeln("H, 0, 1 ",PropGraphRelationshipMapper(H, 0, 1, SymTablePassed));
        writeln("Node Label H, 0 ",PropGraphNodeLabelMapper(H, 0 , SymTablePassed));
        writeln("Node Label H, 1 ",PropGraphNodeLabelMapper(H, 1 , SymTablePassed));
        writeln("H, 1, 0 ",PropGraphRelationshipMapper(H, 1, 0, SymTablePassed));

        writeln("G, 0, 1 ",PropGraphRelationshipMapper(G, 0, 1, SymTablePassed));
        writeln("Node Label G, 0 ",PropGraphNodeLabelMapper(G, 0 , SymTablePassed));
        writeln("Node Label G, 1 ",PropGraphNodeLabelMapper(G, 1 , SymTablePassed));
        writeln("G, 1, 0 ",PropGraphRelationshipMapper(G, 1, 0, SymTablePassed));

        writeln("G, 1, 3  EXISTS ",PropGraphRelationshipMapper(G, 1, 3, SymTablePassed));
        writeln("G, 3, 1  DOES'NT exist ",PropGraphRelationshipMapper(G, 3, 1, SymTablePassed));
*/

 /*       writeln("H, 0, 3 ",PropGraphRelationshipMapper(H, 0, 3, SymTablePassed));
        writeln("H, 3, 0 ",PropGraphRelationshipMapper(H, 3, 0, SymTablePassed));
        writeln("H, 0, 2 ",PropGraphRelationshipMapper(H, 0, 2, SymTablePassed));
        writeln("H, 100, 17 ",PropGraphRelationshipMapper(G, 100, 17, SymTablePassed));
*/
        
/*        
        writeln("Node Label H, 1 ",PropGraphNodeLabelMapper(H, 1 , SymTablePassed));
        writeln("Node Label H, 2 ",PropGraphNodeLabelMapper(H, 2 , SymTablePassed));
        writeln("Node Label H, 3 ",PropGraphNodeLabelMapper(H, 3 , SymTablePassed));
        writeln("Node Label H, 4 ",PropGraphNodeLabelMapper(H, 4 , SymTablePassed));
        writeln("Node Label H, 200 ",PropGraphNodeLabelMapper(G, 2 , SymTablePassed));*/
/*        
        //writeln("Node Label G, 3 ",PropGraphNodeLabelMapper(G, 3 , SymTablePassed));
        //writeln("Node Label H, 1 ",PropGraphNodeLabelMapper(H, 1 , SymTablePassed));
        //writeln("Node Label H, 0 ",PropGraphNodeLabelMapper(H, 0 , SymTablePassed));

        
        //return true;
    
        //writeln("relationship_mapper_G[0] =",relationship_mapper_G[0] );                                                       
*/        
        //writeln("\n\n****************** We reached isIsomorphic 1 ", "to check v= ", v ," mapping= ", mapping);
        // Check if the node labels are the same
         if PropGraphNodeLabelMapper(H, v, SymTablePassed)[1] != PropGraphNodeLabelMapper(G, i, SymTablePassed)[1] {
        //if nodeLabelsH[v] != nodeLabelsG[i] {
            //writeln("if PropGraphNodeLabelMapper(H, v, SymTablePassed)[1] != PropGraphNodeLabelMapper(G, i, SymTablePassed)[1] {");
            return false;
        }

        
        for u in 0..v-1 {
            //writeln("$$$$$$$$$ We reached isIsomorphic 2");
            //writeln(" u= ",u, " mapping[u]= ", mapping[u],"\n\n");

            if mapping[u] > -1 {  // If u in H is mapped to some vertex in G
                                  // Check if there is an edge from u to v in H
                //writeln("if mapping[u] > -1 {");
/*                var adj_list_of_u_from_H_start = segH[u];
                var adj_list_of_u_from_H_end = segH[u+1]-1;
                writeln("******************************");
                writeln("segH=",segH);
                writeln("******************************");

                writeln("adj_list_of_u_from_H_start = ",segH[u]);
                writeln("adj_list_of_u_from_H_end = ", segH[u+1]-1);

                writeln("dstH= ",dstH);
                writeln("******************************");
                
                var v_found = bin_search_v(dstH, adj_list_of_u_from_H_start, adj_list_of_u_from_H_end, v);
                writeln("There is an edge in subgraph between u =", u, ", v = ",v, "\n\n");
                writeln("The index of this edge is v_found= ", v_found);
                
                //writeln("edgeRelationshipsG = ", edgeRelationshipsG);
                writeln("edgeRelationshipsH [v_found] = ", edgeRelationshipsH[v_found]);
                writeln("This means edge with index ",v_found," has label = SOMEthong but it's mapping index is ",edgeRelationshipsH[v_found] );

                //var edgeIndexH_v = edgeRelationshipsH[v_found];

                writeln("dstH[v_found]= ",dstH[v_found]);

                writeln("segH[v_found]= ", segH[v_found],"\n\n");
*/
                if PropGraphRelationshipMapper(H, u, v, SymTablePassed)[0] {
                //if v_found>= 0 {
                    // Check if there is an edge from mapping[u] to mapping[v] in G
                    // And check if the edge labels are the same
                    //writeln("We have an edge in subgraph. NOW lets check in G with mapped nodes:\n\n");
                    var um = mapping[u];
                    var vm = mapping[v];
/*
                    var adj_list_of_um_from_G_start = segG[um];
                    var adj_list_of_um_from_G_end = segG[um+1]-1;

                    var vm_found = bin_search_v(dstG, adj_list_of_um_from_G_start, adj_list_of_um_from_G_end, vm);
                    //var edgeIndexG_vm = edgeRelationshipsG[vm_found];

                    writeln("(((((((((((((((((((((v_found is geater than -1 . lets find edge in G");
                    writeln("mapping= ", mapping);*/
                    //writeln("u = ", u , " equivalent of u is um = ", mapping[u]);
                    //writeln("v = ", v , " equivalent of v is vm = ", mapping[v]);
/*                    
                    writeln("This means edge with index ",vm_found," has label = SOMEthong but it's mapping index is ",edgeRelationshipsG[vm_found] );
                    //writeln("srcG= ",srcG);
                    //writeln("dstG= ",dstG);
                    writeln("edgeRelationshipsH[v_found]= ",edgeRelationshipsH[v_found]);
                    //writeln("edgeRelationshipsH",edgeRelationshipsH);
*/                    
                    if !PropGraphRelationshipMapper(G, um, vm, SymTablePassed)[0] {
                    //if vm_found >=0{
                    //writeln("edgeRelationshipsG[vm_found]= ",edgeRelationshipsG[vm_found]);
                    //writeln("edgeRelationshipsG",edgeRelationshipsG);
                    //writeln("hhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhh");
                    //writeln("relationship_mapper_H[v_found] = ",relationship_mapper_H[v_found]," v_found = ",v_found);
                    //writeln("relationship_mapper_G[vm_found] = ",relationship_mapper_G[vm_found], " vm_found = ",vm_found);
                    
                    //writeln("edgeIndex = ", edgeIndex);
                    //writeln(edgeIndex.type:string);
                    }
                    if !PropGraphRelationshipMapper(G, um, vm, SymTablePassed)[0] ||
                        PropGraphRelationshipMapper(H, u, v, SymTablePassed)[1] != PropGraphRelationshipMapper(G, um, vm, SymTablePassed)[1]{
                        //writeln("!PropGraphRelationshipMapper(G, um, vm, SymTablePassed)[0] = ",!PropGraphRelationshipMapper(G, um, vm, SymTablePassed)[0]);
                        //writeln("PropGraphRelationshipMapper(H, u = ",u," v = ", v,"SymTablePassed)[1] = ",PropGraphRelationshipMapper(H, u, v, SymTablePassed)[1]);
                        //writeln("PropGraphRelationshipMapper(G, um = ", um," vm = ", vm, "SymTablePassed)[1] = ", PropGraphRelationshipMapper(G, um, vm, SymTablePassed)[1]);

                    //if vm_found <0 || relationship_mapper_H[v_found] != relationship_mapper_G[vm_found] {
                        return false;
                    }
                }

                // Check if there is an edge from v to u in H
/*                var adj_list_of_v_from_H_start = segH[v];
                var adj_list_of_v_from_H_end = segH[v+1];
                var u_found = bin_search_v(dstH, adj_list_of_v_from_H_start, adj_list_of_v_from_H_end, u);
                var edgeIndexH_u = edgeRelationshipsH[u_found];
                writeln("edgeIndexH_u = edgeRelationshipsH[u_found], edgeIndexH");
              
                writeln("u_found = ", u_found);
*/                
                if PropGraphRelationshipMapper(H, v, u, SymTablePassed)[0]{ 
                   //writeln("if PropGraphRelationshipMapper(H, v, u, SymTablePassed)[0]{ ");
                //if u_found >=0 {
                    // Check if there is an edge from mapping[v] to mapping[u] in G
                    // And check if the edge labels are the same
                    var um = mapping[u];
                    var vm = mapping[v];
/*
                    var adj_list_of_vm_from_G_start = segG[vm];
                    var adj_list_of_vm_from_G_end = segG[vm+1];
                    var um_found = bin_search_v(dstG, adj_list_of_vm_from_G_start, adj_list_of_vm_from_G_end, um);
                    //var edgeIndexG_um = edgeRelationshipsG[um_found];
                    writeln("$$$$$$$$$ We reached isIsomorphic 6");*/
                    //writeln("um = ", um);
                    //writeln("vm = ", vm);
                    //writeln("relationship_mapper_H[u_found] = ",relationship_mapper_H[u_found]," u_found = ",u_found);
/*
                    writeln("relationship_mapper_G[0] = ",relationship_mapper_G[0]);
                    writeln("relationship_mapper_G[1] = ",relationship_mapper_G[1]);
                    writeln("relationship_mapper_G[2] = ",relationship_mapper_G[2]);
                    writeln("relationship_mapper_G[3] = ",relationship_mapper_G[3]);
                    writeln("relationship_mapper_G[4] = ",relationship_mapper_G[4]);
                    writeln("relationship_mapper_G[5] = ",relationship_mapper_G[5]);

                    //writeln("relationship_mapper_G[um_found] = ",relationship_mapper_G[edgeIndexG_um], " um_found = ",um_found);
*/
                    //writeln("PropGraphRelationshipMapper(G, vm, um, SymTablePassed)[0] = ", PropGraphRelationshipMapper(G, vm, um, SymTablePassed)[0]);
                    //writeln("PropGraphRelationshipMapper(H, v, u, SymTablePassed)[0] = ", PropGraphRelationshipMapper(H, v, u, SymTablePassed)[0]);
                    if !PropGraphRelationshipMapper(G, vm, um, SymTablePassed)[0] || !PropGraphRelationshipMapper(H, v, u, SymTablePassed)[0]{
                    //if um_found<0 || u_found <0{
                        //writeln("if !PropGraphRelationshipMapper(G, vm, um, SymTablePassed)[0] || !PropGraphRelationshipMapper(H, v, u, SymTablePassed)[0]{");
                        return false;
                    }
                    else if PropGraphRelationshipMapper(H, v, u, SymTablePassed)[1] != PropGraphRelationshipMapper(G, vm, um, SymTablePassed)[1]{
                    //else if relationship_mapper_H[u_found] != relationship_mapper_G[um_found] {
                        //writeln(" else if PropGraphRelationshipMapper(H, v, u, SymTablePassed)[1] != PropGraphRelationshipMapper(G, vm, um, SymTablePassed)[1]{");
                        return false;
                    }
                }
            }
        }
        //writeln("isiso return true ");
        return true;
    }
    
    // Recursive function for Ullmann's subgraph isomorphism algorithm
    proc ullmannSubgraphIsomorphism11Helper(G: SegGraph, H: SegGraph, v: int, 
                                            visited: [?D1] bool, mapping: [?D2] int, 
                                            graphDegree: [?D3] int, st: borrowed SymTab): list([1..H.n_vertices] int)  throws {
        var isomorphismList: list(list(int));

        var localIsoList: list([1..H.n_vertices] int);  // List to store the isomorphisms found in the current branch
        var localIsoCounter = 0;  // Count the number of isomorphisms found in the current branch

//        writeln("^^^^^^^^^^^^^^^^Ullmann Helper begins:");   
//        writeln("$$$$$$ WE GET HERE 3");

        for i in 0..G.n_vertices-1 {
            if (!visited[i] && graphDegree[i] >= 1) { 
                visited[i] = true;  // Mark the vertex as visited
                mapping[v] = i;  // Add the vertex to the current mapping
                // If the vertex can be added to the current mapping
                if (isIsomorphic(G, H, v, mapping, st )) {
                    // If all vertices in H have been visited
                    if (v >= H.n_vertices-1) {
                        var isComplete = true;  // Check if all vertices in the subgraph have been mapped
                        for j in 0..H.n_vertices-1 {
                            if (mapping[j] < 0) {
                                isComplete = false;
                                break;
                            }
                        }
                        // If the mapping is complete, add the current mapping to the isomorphism list
                        if (isComplete) {
                            localIsoList.pushBack(mapping);
                        }
                    }
                    else {
                        // Recursively call the function for the next vertex
                        var subIsoList = ullmannSubgraphIsomorphism11Helper(G, H, v+1, visited, mapping, graphDegree, st);
                        //writeln("subIsoList= ",subIsoList );
                        if (subIsoList.size > 0) {
                            // Add isomorphisms found in the sub-branch to the current isomorphism list
                            for isoMapping in subIsoList {
                                localIsoList.pushBack(isoMapping);
                                writeln("pushBack of ",isoMapping );
                            }
                        }
                    }
                }
                // Backtrack: unvisit the vertex and remove it from the mapping
                visited[i] = false;
                mapping[v] = -1;
            }
        }
        writeln("localIsoList= ", localIsoList);
        return localIsoList;  // Return the list of isomorphisms found in the current branch
    } // end of ullmannSubgraphIsomorphism11Helper

    // Ullmann's subgraph isomorphism algorithm
    //proc ullmannSubgraphIsomorphism11(G: SegGraph, H: SegGraph, subGraphVerticesSortedByDegree: [?D1] int, 
    //                                   graphDegree: [?D2] int) throws {
    proc ullmannSubgraphIsomorphism11(G: SegGraph, H: SegGraph, SubgraphDegree: [?D1] int, 
                                       graphDegree: [?D2] int, st: borrowed SymTab) throws {
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
        forall idx in 0..H.n_vertices-1 {
            //var v = subGraphVerticesSortedByDegree[idx];
            var v = idx;
            var visited: [0..G.n_vertices-1] bool;  // Array to keep track of visited vertices
            var mapping: [0..H.n_vertices-1] int;  // Array for the current mapping
           
            mapping = -1;  // Initialize the mapping array to -1 (indicating no mapping)
            visited = false;  // Initialize all vertices as unvisited
            // Find isomorphisms for the current vertex v
            var subIsoList = ullmannSubgraphIsomorphism11Helper(G, H, v, visited, mapping, graphDegree, st);
            //writeln("$$$$$$ WE GET HERE 2");
            //writeln("subIsoList =", subIsoList);
            if (subIsoList.size > 0) {
                // Print isomorphisms found by the current task without merging
                var taskIsoCounter = 0;
                for isoMapping in subIsoList {
                    taskIsoCounter += 1;
                    writeln("Isomorphism #", taskIsoCounter, ":");
                    for k in 0..H.n_vertices-1 {
                        var mappedVertex = isoMapping[k];
                        if (mappedVertex >= 0) {
                            writeln("Subgraph vertex ", k, " -> Graph vertex ", mappedVertex);
                        }
                    }
                }
                
                // Add the number of isomorphisms found by the current task to the global counter
                globalIsoCounter.add(taskIsoCounter);
            }
        }
    
        // Print the total number of isomorphisms found
        writeln("Total isomorphisms found: ", globalIsoCounter.read());
    } // end of ullmannSubgraphIsomorphism11
} // end of module