module DipArrayPropertyGraphMsg {
    // Chapel modules.
    use Reflection;
    use Set;
    use Time; 
    use Sort; 
    use List;
    use Atomics;
    
    // Arachne Modules.
    use Utils; 
    use GraphArray;
    use SegmentedString;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use ArgSortMsg;
    use AryUtil;
    use Logging;
    use Message;

    // 2D arrays from Ben.
    use SymEntry2D;
    
    // Server message logger. 
    private config const logLevel = LogLevel.DEBUG;
    const smLogger = new Logger(logLevel);
    var outMsg:string;

    /**
    * Adds node labels to the nodes of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipArrayaddNodeLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var arrays = msgArgs.getValueOf("Arrays");

        // Extract the names of the arrays storing the nodeIDs and labels.
        var arrays_list = arrays.split();
        var nodes_name = arrays_list[0];
        var labels_name = arrays_list[1];
        
        // Extract the nodes array that is an integer array.
        var nodes_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(nodes_name, st);
        var nodes_sym = toSymEntry(nodes_entry, int);
        var nodes_arr = nodes_sym.a;

        // Extract the labels array which is a string array aka a segmented string.
        var labels_arr:SegString = getSegString(labels_name, st);

        // Get graph for usage.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        // Extract the node map to get the internal vertex values.
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;

        var timer:stopwatch();
        timer.start();
        //Create the indices into the two-dimensional label byte array.  
        var lbl_set = new set(string, parSafe=true);
        forall i in nodes_arr.domain with (ref lbl_set) do lbl_set.add(labels_arr[i]);
        var lbl_set_arr = lbl_set.toArray();
        var num_labels = lbl_set_arr.size;
        var D_lbl: domain(string);
        D_lbl += lbl_set_arr;
        var lbl_arr: [D_lbl] int;
        forall (ind,val) in zip(lbl_set_arr.domain, lbl_set_arr) do lbl_arr[val] = ind;

        // Create the two-dimensional byte array. 
        var D_byte_label_arrays: domain(2) dmapped Block({0..<num_labels, 0..<node_map.size}) = {0..<num_labels, 0..<node_map.size};
        var byte_label_arrays: [D_byte_label_arrays] atomic bool;

        // Populate the two-dimesional byte array. 
        forall i in nodes_arr.domain {
            var lbl = labels_arr[i];
            var lbl_ind = lbl_arr[lbl];
            var internal_vertex = bin_search_v(node_map, node_map.domain.lowBound, node_map.domain.highBound, nodes_arr[i]);
            if (internal_vertex != -1) then byte_label_arrays[lbl_ind,internal_vertex].write(true);
        }
        var count_2: atomic int = 0;
        forall a in byte_label_arrays with (ref count_2) do if a.read() == true then count_2.add(1);
        writeln("$$$$$ count_2 = ", count_2);
        
        // Add two-dimensional array into symbol table using Ben's approach!
        graph.withComp(new shared SymEntry2D(byte_label_arrays):GenSymEntry, "DIP_ARR_NODE_LABELS");
        graph.withComp(new shared SymEntry(lbl_set_arr):GenSymEntry, "DIP_ARR_LBL_INDICES");
        timer.stop();  
        var repMsg = "labels added";
        outMsg = "DipARRaddNodeLabels took " + timer.elapsed():string + " sec ";

        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipArrayaddNodeLabelsMsg

    /**
    * Adds edge relationships to the edges of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipArrayaddEdgeRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var arrays = msgArgs.getValueOf("Arrays");

        // Extract the names of the arrays passed to the function.
        var arrays_list = arrays.split();
        var src_name = arrays_list[0];
        var dst_name = arrays_list[1];
        var rel_name = arrays_list[2];
        
        // Extract the actual arrays for each of the names above.
        var src_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(src_name, st);
        var src_sym = toSymEntry(src_entry, int);
        var src = src_sym.a;
        
        var dst_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(dst_name, st);
        var dst_sym = toSymEntry(dst_entry, int);
        var dst = dst_sym.a;

        var rel_arr:SegString = getSegString(rel_name, st);

        var timer:stopwatch;
        timer.start();
        
        // Get graph for usage and needed arrays.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;
        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
        var start_idx = toSymEntry(graph.getComp("START_IDX"), int).a;
        var neighbor = toSymEntry(graph.getComp("NEIGHBOR"), int).a;
        var src_actual = toSymEntry(graph.getComp("SRC"), int).a;
        var dst_actual = toSymEntry(graph.getComp("DST"), int).a;

        var rel_set = new set(string, parSafe=true);
        forall i in src.domain with (ref rel_set) do rel_set.add(rel_arr[i]);

        var rel_set_arr = rel_set.toArray();
        var num_relationships = rel_set_arr.size;
        var D_lbl: domain(string);
        D_lbl += rel_set_arr;
        var relations_arr: [D_lbl] int;
        forall (ind,val) in zip(rel_set_arr.domain, rel_set_arr) do relations_arr[val] = ind;

        var D_byte_relationship_arrays: domain(2) dmapped Block({0..<num_relationships, 0..<src_actual.size}) = {0..<num_relationships, 0..<src_actual.size};
        var byte_relationship_arrays: [D_byte_relationship_arrays] bool;
        byte_relationship_arrays = false;
        
        forall (i,j) in zip(src.domain, dst.domain) with (ref byte_relationship_arrays, ref rel_arr){
            var u = node_map_r[src[i]];
            var v = node_map_r[dst[j]];

            var start = start_idx[u];
            var end = start + neighbor[u];

            var neighborhood = dst_actual[start..end-1];
            var edge_ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, v);
            var rel = rel_arr[i];
            var rel_ind = relations_arr[rel];

            byte_relationship_arrays[rel_ind,edge_ind] = true;
        }
        // var count_2: atomic int = 0;
        // forall a in byte_relationship_arrays with (ref count_2) do if a == true then count_2.add(1);
        // writeln("count_2 = ", count_2);

        // Add two-dimensional array into symbol table using Ben's approach!
        graph.withComp(new shared SymEntry2D(byte_relationship_arrays):GenSymEntry, "DIP_ARR_RELATIONSHIPS");
        graph.withComp(new shared SymEntry(rel_set_arr):GenSymEntry, "DIP_ARR_REL_INDICES");
        timer.stop();  

        var repMsg = "relationships added";
        outMsg = "DipARRaddEdgeRelationships took " + timer.elapsed():string + " sec ";

        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipArrayaddEdgeRelationshipsMsg

    /**
    * Adds properties to the nodes of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipArrayaddNodePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {        
        var repMsg = "DipArrayaddNodePropertiesMsg node properties not implemented";
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipArrayaddNodePropertiesMsg

    /**
    * Adds properties to the edges of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipArrayaddEdgePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        var repMsg = "DipArrayaddEdgePropertiesMsg edge properties not implemented";
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipArrayaddEdgePropertiesMsg

    /**
    * Queries the property graph and returns either arrays of strings or arrays of integer values
    * that represent vertices and edges.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipArrayqueryMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var arraysName = msgArgs.getValueOf("Arrays");

        // Extracts the arrays we are going to use that will hold our query arrays.
        var arrays_list = arraysName.split();

        // Extract graph data for usage in this function.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;
        var start_idx = toSymEntry(graph.getComp("START_IDX"), int).a;
        var neighbor = toSymEntry(graph.getComp("NEIGHBOR"), int).a;
        var src_actual = toSymEntry(graph.getComp("SRC"), int).a;
        var dst_actual = toSymEntry(graph.getComp("DST"), int).a;
        var node_labels = toSymEntry2D(graph.getComp("DIP_ARR_NODE_LABELS"), bool).a;
        var dip_arr_lbl_indices = toSymEntry(graph.getComp("DIP_ARR_LBL_INDICES"), string).a;
        var edge_relationships = toSymEntry2D(graph.getComp("DIP_ARR_RELATIONSHIPS"), bool).a;
        var dip_arr_rel_indices = toSymEntry(graph.getComp("DIP_ARR_REL_INDICES"), string).a;

        /********** QUERY NODES **********/
        var return_list = new list(string);
        if (arrays_list[0] != "no_nodes_to_find") {
            // Extract the array that contains the nodes whose labels we are looking for.
            var nodes_to_find_name = arrays_list[0];
            var nodes_to_find_entry : borrowed GenSymEntry = getGenericTypedArrayEntry(nodes_to_find_name, st);
            var nodes_to_find_sym = toSymEntry(nodes_to_find_entry, int);
            var nodes_to_find = nodes_to_find_sym.a;

            // Convert array to associative domain to maintain the found labels.
            var nodes_to_find_set : domain(int);
            // nodes_to_find_set += node_map_r[nodes_to_find];
            for node in nodes_to_find do nodes_to_find_set += node_map_r[node];
            var return_array_lbl : [nodes_to_find_set] string;
            return_array_lbl = "";

            // Search in parallel for the nodes whose labels we want to find. 
            var timer:stopwatch;
            timer.start();
            // forall (i,j) in node_labels.domain { // i is the row index and j is the column index
            //     if (nodes_to_find_set.contains(j)) {
            //         if node_labels[i,j] == true {
            //             return_array_lbl[j] += dip_arr_lbl_indices[i] + " "; 
            //         }
            //     }
            // }
            forall node in nodes_to_find_set with (ref return_array_lbl) {
                forall (lbl_index,_) in node_labels.domain[.., node..node] with (ref return_array_lbl) {
                    if node_labels.localAccess[lbl_index,node] == true {
                        return_array_lbl[node] += dip_arr_lbl_indices[lbl_index] + " ";
                    }
                }
            }
            timer.stop();
            var time_msg = "node query DIP-ARR took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_array_lbl = ", return_array_lbl);
        }
        /********** QUERY EDGES **********/
        if ((arrays_list[1] != "no_edges_to_find_src") && (arrays_list[2]) != "no_edges_to_find_dst") {
            // Extract the arrays that contains the edges whose relationships we are looking for.
            var edges_to_find_src_name = arrays_list[1];
            var edges_to_find_src_entry : borrowed GenSymEntry = getGenericTypedArrayEntry(edges_to_find_src_name, st);
            var edges_to_find_src_sym = toSymEntry(edges_to_find_src_entry, int);
            var edges_to_find_src = edges_to_find_src_sym.a;

            var edges_to_find_dst_name = arrays_list[2];
            var edges_to_find_dst_entry : borrowed GenSymEntry = getGenericTypedArrayEntry(edges_to_find_dst_name, st);
            var edges_to_find_dst_sym = toSymEntry(edges_to_find_dst_entry, int);
            var edges_to_find_dst = edges_to_find_dst_sym.a;

            // Convert arrays to associative domain to maintain the edge indices we must find.
            var edge_indices_to_find_set : domain(int, parSafe=true);
            forall (u,v) in zip(edges_to_find_src, edges_to_find_dst) with (ref edge_indices_to_find_set) {
                var ui = node_map_r[u];
                var vi = node_map_r[v];

                var start = start_idx[ui];
                var end = start + neighbor[ui];

                ref neighborhood = dst_actual[start..end-1];
                var edge_ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, vi);
                edge_indices_to_find_set += edge_ind;
            }
            var return_array_rel : [edge_indices_to_find_set] string;
            var return_array_prop : [edge_indices_to_find_set] string;
            return_array_rel = "";
            return_array_prop = "";
            
            // Search in parallel for the nodes whose labels we want to find. 
            var timer:stopwatch;
            timer.start();
            // forall (i,j) in edge_relationships.domain { // i is the row index and j is the column index
            //     if (edge_indices_to_find_set.contains(j)) {
            //         if edge_relationships[i,j] == true {
            //             return_array_rel[j] += dip_arr_rel_indices[i] + " "; 
            //         }
            //     }
            // }
            forall edge in edge_indices_to_find_set with (ref return_array_rel) {
                forall (rel_index,_) in edge_relationships.domain[.., edge..edge] with (ref return_array_rel) {
                    if edge_relationships.localAccess[rel_index,edge] == true {
                        return_array_rel[edge] += dip_arr_rel_indices[rel_index] + " ";
                    }
                }
            }
            timer.stop();
            var time_msg = "edge query DIP-ARR took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_array_rel = ", return_array_rel);
            // writeln("$$$$$$$$$$ return_array_prop = ", return_array_prop);
        }
        if (arrays_list[3] != "no_labels_to_find") {
            // Extract the array that contains the labels we are looking for.
            var labels_to_find_name = arrays_list[3];
            var labels_to_find : SegString = getSegString(labels_to_find_name, st);

            // Convert array to associative domain to maintain the relationships to find.
            var labels_to_find_set : domain(string);
            var label_indices_to_find_set : domain(int);
            for i in 0..<labels_to_find.size do labels_to_find_set += labels_to_find[i];
            var return_set : domain(int, parSafe = true);

            // Generate the indices of the rows we are to target.
            for (i,lbl) in zip(dip_arr_lbl_indices.domain, dip_arr_lbl_indices) {
                if labels_to_find_set.contains(lbl) {
                    label_indices_to_find_set += i;
                }
            }
            
            // Search in parallel for the nodes that have those labels.
            var timer:stopwatch;
            timer.start();
            // forall (i,j) in node_labels.domain with (ref return_set) { 
            //     if label_indices_to_find_set.contains(i) {
            //         if node_labels[i,j] == true {
            //             return_set += node_map[j];
            //         }
            //     }
            // }
            forall lbl in label_indices_to_find_set with (ref return_set) {
                forall (_, node) in node_labels.domain[lbl..lbl, ..] with (ref return_set) {
                    if node_labels.localAccess[lbl,node] == true {
                        return_set += node;
                    }
                }
            }
            timer.stop();
            var time_msg = "label query DIP-DLL took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_set = ", return_set);
        }
        if (arrays_list[4] != "no_relationships_to_find") {
            // Extract the array that contains the relationships we are looking for. 
            var relationships_to_find_name = arrays_list[4];
            var relationships_to_find : SegString = getSegString(relationships_to_find_name, st);

            // Convert array to associative domain to maintain the relationships to find.
            var relationships_to_find_set : domain(string);
            var relationship_indices_to_find_set : domain(int);
            for i in 0..<relationships_to_find.size do relationships_to_find_set += relationships_to_find[i];
            var return_set : domain(int, parSafe=true);

            // Generate the indices of the rows we are to target.
            for (i,rel) in zip(dip_arr_rel_indices.domain, dip_arr_rel_indices) {
                if relationships_to_find_set.contains(rel) {
                    relationship_indices_to_find_set += i;
                }
            }

            // Search in parallel for the edges that have those relationships.
            var timer:stopwatch;
            timer.start();
            // forall (i,j) in edge_relationships.domain with (ref return_set) { 
            //     if relationship_indices_to_find_set.contains(i) {
            //         if edge_relationships[i,j] == true {
            //             return_set += j;
            //         }
            //     }
            // }
            forall rel in relationship_indices_to_find_set with (ref return_set) {
                forall (_, edge) in edge_relationships.domain[rel..rel, ..] with (ref return_set) {
                    if edge_relationships.localAccess[rel,edge] == true {
                        return_set += edge;
                    }
                }
            }
            timer.stop();
            var time_msg = "relationship query DIP-DLL took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_set = ", return_set);
        }
        if (arrays_list[5] != "no_node_properties_to_find") {
            var time_msg = "node properties query DIP-DLL not implemented";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
        }
        if (arrays_list[6] != "no_edge_properties_to_find") {
            var time_msg = "edge properties query DIP-DLL not implemented";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
        }

        var repMsg = "query completed";
        // Print out debug information to arkouda server output.
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } //end of DipDArrrayqueryMsg

    use CommandMap;
    registerFunction("DipArrayaddNodeLabels", DipArrayaddNodeLabelsMsg, getModuleName());
    registerFunction("DipArrayaddEdgeRelationships", DipArrayaddEdgeRelationshipsMsg, getModuleName());
    registerFunction("DipArrayaddNodeProperties", DipArrayaddNodePropertiesMsg, getModuleName());
    registerFunction("DipArrayaddEdgeProperties", DipArrayaddEdgePropertiesMsg, getModuleName());
    registerFunction("DipArrayquery", DipArrayqueryMsg, getModuleName());
}