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

    // Global counter for isomorphisms
    var globalIsoCounter: atomic int;

    // Function to check if the vertex v of H can be added to the current mapping
    // Returns true if it can be added, false otherwise
    proc isIsomorphic(G: SegGraph, H: SegGraph, v: int, mapping: [?D] int): bool throws {
        var i = mapping[v];  // Vertex i in G corresponds to vertex v in H
        
        // Extract the graph information needed for G and H. 
        var nodeLabelsG = toSymEntry(G.getComp("VERTEX_LABELS"), domain(int)).a;
        var edgeRelationshipsG = toSymEntry(G.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var srcG = toSymEntry(G.getComp("SRC"), int).a;
        var dstG = toSymEntry(G.getComp("DST"), int).a;
        var segG = toSymEntry(G.getComp("SEGMENTS"), int).a;

        var nodeLabelsH = toSymEntry(H.getComp("VERTEX_LABELS"), domain(int)).a;
        var edgeRelationshipsH = toSymEntry(H.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var srcH = toSymEntry(H.getComp("SRC"), int).a;
        var dstH = toSymEntry(H.getComp("DST"), int).a;
        var segH = toSymEntry(H.getComp("SEGMENTS"), int).a;

        // Check if the node labels are the same
        if nodeLabelsH[v] != nodeLabelsG[i] {
            return false;
        }

        // Check if the in-degree + out-degree of every vertex in H is less than or equal to 
        // the corresponding vertex in G
        for u in 0..v-1 {
            if mapping[u] > 0 {  // If u in H is mapped to some vertex in G
                // Check if there is an edge from u to v in H
                var adj_list_of_u_from_H_start = segH[u];
                var adj_list_of_u_from_H_end = segH[u+1];
                var v_found = bin_search_v(dstH, adj_list_of_u_from_H_start, adj_list_of_u_from_H_end, v);
                if v_found {
                    // Check if there is an edge from mapping[u] to mapping[v] in G
                    // And check if the edge labels are the same
                    var um = mapping[u];
                    var vm = mapping[v];

                    var adj_list_of_um_from_G_start = segG[um];
                    var adj_list_of_um_from_G_end = segG[um+1];
                    var vm_found = bin_search_v(dstG, adj_list_of_um_from_G_start, adj_list_of_um_from_G_end, vm);

                    if !vm_found || edgeRelationshipsH[v_found] != edgeRelationshipsG[vm_found] {
                        return false;
                    }
                }

                // Check if there is an edge from v to u in H
                var adj_list_of_v_from_H_start = segH[v];
                var adj_list_of_v_from_H_end = segH[v+1];
                var u_found = bin_search_v(dstH, adj_list_of_v_from_H_start, adj_list_of_v_from_H_end, u);
                if u_found {
                    // Check if there is an edge from mapping[u] to mapping[v] in G
                    // And check if the edge labels are the same
                    var um = mapping[u];
                    var vm = mapping[v];

                    var adj_list_of_vm_from_G_start = segG[vm];
                    var adj_list_of_vm_from_G_end = segG[vm+1];
                    var um_found = bin_search_v(dstG, adj_list_of_vm_from_G_start, adj_list_of_vm_from_G_end, um);

                    if !um_found || edgeRelationshipsH[u_found] != edgeRelationshipsG[um_found] {
                        return false;
                    }
                }
            }
        }
        return true;
    }
    
    // Recursive function for Ullmann's subgraph isomorphism algorithm
    proc ullmannSubgraphIsomorphism11Helper(G: SegGraph, H: SegGraph, v: int, visited: [?D1] bool, mapping: [?D2] int, graphDegree: [?D3] int): list([1..H.n_vertices] int)  throws {
        var isomorphismList: list(list(int));

        var localIsoList: list([1..H.n_vertices] int);  // List to store the isomorphisms found in the current branch
        var localIsoCounter = 0;  // Count the number of isomorphisms found in the current branch

        writeln("$$$$$$ WE GET HERE 3");

        for i in 0..G.n_vertices-1 {
            writeln("$$$$$$ WE GET HERE 4");
            if (!visited[i] && graphDegree[i] >= 1) { 
                visited[i] = true;  // Mark the vertex as visited
                mapping[v] = i;  // Add the vertex to the current mapping
                // If the vertex can be added to the current mapping
                if (isIsomorphic(G, H, v, mapping)) {
                    // If all vertices in H have been visited
                    if (v >= H.n_vertices-1) {
                        var isComplete = true;  // Check if all vertices in the subgraph have been mapped
                        for j in 0..H.n_vertices-1 {
                            if (mapping[j] < 1) {
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
                        var subIsoList = ullmannSubgraphIsomorphism11Helper(G, H, v+1, visited, mapping, graphDegree);
                        if (subIsoList.size > 0) {
                            // Add isomorphisms found in the sub-branch to the current isomorphism list
                            for isoMapping in subIsoList {
                                localIsoList.pushBack(isoMapping);
                            }
                        }
                    }
                }
                writeln("$$$$$$ WE GET HERE 5");
                // Backtrack: unvisit the vertex and remove it from the mapping
                visited[i] = false;
                mapping[v] = -1;
            }
        }
        return localIsoList;  // Return the list of isomorphisms found in the current branch
    } // end of ullmannSubgraphIsomorphism11Helper

    // Ullmann's subgraph isomorphism algorithm
    proc ullmannSubgraphIsomorphism11(G: SegGraph, H: SegGraph, subGraphVerticesSortedByDegree: [?D1] int, graphDegree: [?D2] int) throws {
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
        coforall idx in 0..H.n_vertices-1 {
            var v = subGraphVerticesSortedByDegree[idx];
            var visited: [0..G.n_vertices-1] bool;  // Array to keep track of visited vertices
            var mapping: [0..H.n_vertices-1] int;  // Array for the current mapping
            mapping = -1;  // Initialize the mapping array to -1 (indicating no mapping)
            visited = false;  // Initialize all vertices as unvisited
            // Find isomorphisms for the current vertex v
            writeln("$$$$$$ WE GET HERE 1");
            var subIsoList = ullmannSubgraphIsomorphism11Helper(G, H, v, visited, mapping, graphDegree);
            if (subIsoList.size > 0) {
                // Print isomorphisms found by the current task without merging
                //writeln("Isomorphisms found by task ", v, ":");
                var taskIsoCounter = 0;
                for isoMapping in subIsoList {
                    taskIsoCounter += 1;
                    writeln("Isomorphism #", taskIsoCounter, ":");
                    for k in 0..H.n_vertices-1 {
                        var mappedVertex = isoMapping[k];
                        if (mappedVertex > 0) {
                            writeln("Subgraph vertex ", k, " -> Graph vertex ", mappedVertex);
                        }
                    }
                    //writeln("----");
                }
                
                // Add the number of isomorphisms found by the current task to the global counter
                globalIsoCounter.add(taskIsoCounter);
            }
        }
    
        // Print the total number of isomorphisms found
        writeln("Total isomorphisms found: ", globalIsoCounter.read());
    } // end of ullmannSubgraphIsomorphism11
} // end of module