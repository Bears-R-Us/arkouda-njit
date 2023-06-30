module DipDLLPropertyGraphMsg {
    // Chapel modules.
    use Reflection;
    use Set;
    use Time; 
    use Sort; 
    use List;
    
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
    proc DipDLLaddNodeLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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
        
        // Extract the revesred node_map to see what each original node value maps to.
        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;
        
        // Create array of lists to store the data nodes for each label.
        var node_labels: [node_map.domain] list(shared Node, parSafe=true);

        var timer:stopwatch;
        timer.start();

        var count: atomic int; // our counter
        var lock$: sync bool;   // the mutex lock

        count.write(1);       // Only let two tasks in at a time.
        lock$.writeXF(true);  // Set lock$ to full (unlocked)
        // Note: The value doesn't actually matter, just the state
        // (full:unlocked / empty:locked)
        // Also, writeXF() fills (F) the sync var regardless of its state (X)

        forall i in nodes_arr.domain with (ref last_label_tracker){
            var lbl = labels_arr[i];
            var vertex = node_map_r[nodes_arr[i]];
            var new_node = new shared Node(lbl, vertex);
            node_labels[node_map_r[nodes_arr[i]]].pushBack(new_node);

            // Create a barrier.
            do {
                lock$.readFE();           // Read lock$ (wait)
            } while (count.read() < 1); // Keep waiting until a spot opens up
            
            count.sub(1);          // decrement the counter
            lock$.writeXF(true); // Set lock$ to full (signal)
            if (!last_label_tracker.contains(lbl)) {
                last_label_tracker.add(lbl, new_node);
            }
            else {                    
                var prev_node = last_label_tracker[lbl];
                prev_node.append(new_node);                    
                last_label_tracker.replace(lbl, new_node);
            }
            count.add(1);        // Increment the counter
            lock$.writeXF(true); // Set lock$ to full (signal)
        }
        writeln("$$$$$$ node_labels = ", node_labels);
        
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(node_labels):GenSymEntry, "DIP_DLL_NODE_LABELS");
        timer.stop();  
        var repMsg = "labels added";
        outMsg = "DipDLLaddNodeLabels took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipDLLaddNodeLabelsMsg

    /**
    * Adds edge relationships to the edges of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipDLLaddEdgeRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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

        // Create array of lists to store relationships and populate it. 
        var relationships: [src_actual.domain] list(shared Node, parSafe=true);

        var count: atomic int; // our counter
        var lock$: sync bool;   // the mutex lock

        count.write(1);       // Only let two tasks in at a time.
        lock$.writeXF(true);  // Set lock$ to full (unlocked)
        // Note: The value doesn't actually matter, just the state
        // (full:unlocked / empty:locked)
        // Also, writeXF() fills (F) the sync var regardless of its state (X)
        forall (i,j) in zip(src.domain, dst.domain) with (ref relationships, ref rel_arr, ref last_relationship_tracker){
            var u = node_map_r[src[i]];
            var v = node_map_r[dst[j]];

            var start = start_idx[u];
            var end = start + neighbor[u];

            var neighborhood = dst_actual[start..end-1];
            var ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, v);

            var rel = rel_arr[i];
            var new_node = new shared Node(rel, ind);
            relationships[ind].pushBack(new_node); // or j

            // Create a barrier.
            do {
                lock$.readFE();           // Read lock$ (wait)
            } while (count.read() < 1); // Keep waiting until a spot opens up
            
            count.sub(1);          // decrement the counter
            lock$.writeXF(true); // Set lock$ to full (signal)
            if (!last_relationship_tracker.contains(rel)) {
                last_relationship_tracker.add(rel, new_node);
            }
            else {                    
                var prev_node = last_relationship_tracker[rel];
                prev_node.append(new_node);                    
                last_relationship_tracker.replace(rel, new_node);
            }
            count.add(1);        // Increment the counter
            lock$.writeXF(true); // Set lock$ to full (signal)
        }
        writeln("$$$$$$ relationships = ", relationships);
        
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(relationships):GenSymEntry, "DIP_DLL_RELATIONSHIPS");
        timer.stop();
        var repMsg = "relationships added";
        outMsg = "DipDLLaddEdgeRelationships took " + timer.elapsed():string + " sec";
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipDLLaddEdgeRelationshipsMsg

    /**
    * Adds properties to the nodes of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipDLLaddNodePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var arrays = msgArgs.getValueOf("Arrays");
        var columns = msgArgs.getValueOf("Columns");

        // Extract the names of the arrays storing the nodeIDs and labels.
        var arrays_list = arrays.split();
        var nodes_name = arrays_list[0];

        // Extract the column names.
        var cols_list = columns.split();
        
        // Extract the nodes array that is an integer array.
        var nodes_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(nodes_name, st);
        var nodes_sym = toSymEntry(nodes_entry, int);
        var nodes_arr = nodes_sym.a;

        // Get graph for usage.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;
        var node_props: [node_map.domain] list((string,string), parSafe=true);
        if graph.hasComp("NODE_PROPS") {
            node_props = toSymEntry(graph.getComp("NODE_PROPS"), list((string,string), parSafe=true)).a;
        }

        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
        var timer:stopwatch;
        timer.start();
        forall i in 1..arrays_list.size - 1 {
            var curr_prop_arr:SegString = getSegString(arrays_list[i], st);
            forall j in nodes_arr.domain {
                node_props[node_map_r[nodes_arr[j]]].append((cols_list[i],curr_prop_arr[j]));
            }   
        }
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(node_props):GenSymEntry, "NODE_PROPS");
        timer.stop();
        
        var repMsg = "node properties added";
        outMsg = "Adding node properties to property graph takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipDLLaddNodePropertiesMsg

    /**
    * Adds properties to the edges of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipDLLaddEdgePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var arrays = msgArgs.getValueOf("Arrays");
        var columns = msgArgs.getValueOf("Columns");

        // Extract the names of the arrays passed to the function.
        var arrays_list = arrays.split();
        var cols_list = columns.split();
        var src_name = arrays_list[0];
        var dst_name = arrays_list[1];
        
        // Extract the actual arrays for each of the names above.
        var src_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(src_name, st);
        var src_sym = toSymEntry(src_entry, int);
        var src = src_sym.a;
        
        var dst_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(dst_name, st);
        var dst_sym = toSymEntry(dst_entry, int);
        var dst = dst_sym.a;

        var timer:stopwatch;
        timer.start();
        
        // Get graph for usage and needed arrays.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
        var start_idx = toSymEntry(graph.getComp("START_IDX"), int).a;
        var neighbor = toSymEntry(graph.getComp("NEIGHBOR"), int).a;
        var src_actual = toSymEntry(graph.getComp("SRC"), int).a;
        var dst_actual = toSymEntry(graph.getComp("DST"), int).a;

        // Create array of lists to store edge_props and populate it. 
        var edge_props: [src_actual.domain] list((string,string), parSafe=true);
        if(graph.hasComp("EDGE_PROPS")) {
            edge_props = toSymEntry(graph.getComp("EDGE_PROPS"), list((string,string), parSafe=true)).a;
        }

        forall x in 2..arrays_list.size - 1 {
            var curr_prop_arr:SegString = getSegString(arrays_list[x], st);
            forall (i,j) in zip(src.domain, dst.domain) {
                var u = node_map_r[src[i]];
                var v = node_map_r[dst[j]];

                var start = start_idx[u];
                var end = start + neighbor[u];

                var neighborhood = dst_actual[start..end-1];
                var ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, v);

                edge_props[ind].append((cols_list[x],curr_prop_arr[i])); // or j
            }
        }
        
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(edge_props):GenSymEntry, "EDGE_PROPS");
        timer.stop();
        var repMsg = "edge properties added";
        outMsg = "Adding edge properties to property graph takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipDLLaddEdgePropertiesMsg
    
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
    proc DipDLLqueryMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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
        var node_labels = toSymEntry(graph.getComp("DIP_SLL_NODE_LABELS"), list(string, parSafe=true)).a;
        var edge_relationships = toSymEntry(graph.getComp("DIP_SLL_RELATIONSHIPS"), list(string, parSafe=true)).a;
        var node_properties = toSymEntry(graph.getComp("DIP_SLL_NODE_PROPS"), list((string,string), parSafe=true)).a;
        var edge_properties = toSymEntry(graph.getComp("DIP_SLL_EDGE_PROPS"), list((string,string), parSafe=true)).a;

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
            nodes_to_find_set += nodes_to_find;
            var return_array_lbl : [nodes_to_find_set] string;
            var return_array_prop : [nodes_to_find_set] string;
            return_array_lbl = "";
            return_array_prop = "";

            // Search in parallel for the nodes whose labels we want to find. 
            var timer:stopwatch;
            timer.start();
            forall u in nodes_to_find {
                for lbl in node_labels[node_map_r[u]] {
                    return_array_lbl[u] += lbl + " "; 
                }
                for prop in node_properties[node_map_r[u]] {
                    return_array_prop[u] += "(" + prop[0] + ", " + prop[1] + ")";
                }
            }
            timer.stop();
            var time_msg = "node query DIP-SLL took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_array_lbl = ", return_array_lbl);
            // writeln("$$$$$$$$$$ return_array_prop = ", return_array_prop);
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
            forall u in edge_indices_to_find_set {
                for rel in edge_relationships[u] {
                    return_array_rel[u] += rel + " "; 
                }
                for prop in edge_properties[u] {
                    return_array_prop[u] += "(" + prop[0] + ", " + prop[1] + ")";
                }
            }
            timer.stop();
            var time_msg = "edge query DIP-SLL took " + timer.elapsed():string + " sec";
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
            for i in 0..<labels_to_find.size do labels_to_find_set += labels_to_find[i];
            var return_set : domain(int, parSafe = true);

            // Search in parallel for the nodes that have those labels.
            var timer:stopwatch;
            timer.start();
            forall (u, u_label_set) in zip(node_labels.domain, node_labels) with (ref return_set) {
                for lbl in u_label_set {
                    if labels_to_find_set.contains(lbl) {
                        return_set += u;
                    }
                }
            }
            timer.stop();
            var time_msg = "label query DIP-SLL took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_set = ", return_set);
        }
        if (arrays_list[4] != "no_relationships_to_find") {
            // Extract the array that contains the relationships we are looking for. 
            var relationships_to_find_name = arrays_list[4];
            var relationships_to_find : SegString = getSegString(relationships_to_find_name, st);

            // Convert array to associative domain to maintain the relationships to find.
            var relationships_to_find_set : domain(string);
            for i in 0..<relationships_to_find.size do relationships_to_find_set += relationships_to_find[i];
            var return_set : domain(int, parSafe=true);

            // Search in parallel for the edges that have those relationships.
            var timer:stopwatch;
            timer.start();
            forall (edge_ind, edge_ind_relationship_set) in zip(edge_relationships.domain, edge_relationships) with (ref return_set) {
                for rel in edge_ind_relationship_set {
                    if relationships_to_find_set.contains(rel) {
                        return_set += edge_ind;
                    }
                }
            }
            timer.stop();
            var time_msg = "relationship query DIP-SLL took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_set = ", return_set);
        }
        if (arrays_list[5] != "no_node_properties_to_find") {
            // Extract the array that contains the node properties we are looking for.
            var node_props_to_find_name = arrays_list[5];
            var node_props_to_find : SegString = getSegString(node_props_to_find_name, st);

            // Convert array to associative domain to maintain the relationships to find.
            var node_props_to_find_set : domain(string);
            for i in 0..<node_props_to_find.size do node_props_to_find_set += node_props_to_find[i];
            var return_set : domain(int, parSafe = true);

            // Search in parallel for the nodes that have those labels.
            var timer:stopwatch;
            timer.start();
            forall (u, u_node_prop_set) in zip(node_properties.domain, node_properties) with (ref return_set) {
                for prop in u_node_prop_set {
                    if ((node_props_to_find_set.contains(prop[0])) && (prop[0] != "")) {
                        return_set += u;
                    }
                }
            }
            timer.stop();
            var time_msg = "node properties query DIP-SLL took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_set = ", return_set);
        }
        if (arrays_list[6] != "no_edge_properties_to_find") {
            // Extract the array that contains the relationships we are looking for. 
            var edge_props_to_find_name = arrays_list[6];
            var edge_props_to_find : SegString = getSegString(edge_props_to_find_name, st);

            // Convert array to associative domain to maintain the relationships to find.
            var edge_props_to_find_set : domain(string);
            for i in 0..<edge_props_to_find.size do edge_props_to_find_set += edge_props_to_find[i];
            var return_set : domain(int, parSafe=true);

            // Search in parallel for the edges that have those relationships.
            var timer:stopwatch;
            timer.start();
            forall (edge_ind, edge_ind_edge_props_set) in zip(edge_properties.domain, edge_properties) with (ref return_set) {
                for prop in edge_ind_edge_props_set {
                    if ((edge_props_to_find_set.contains(prop[0])) && (prop[0] != "")) {
                        return_set += edge_ind;
                    }
                }
            }
            timer.stop();
            var time_msg = "edge properties query DIP-SLL took " + timer.elapsed():string + " sec";
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);
            // writeln("$$$$$$$$$$ return_set = ", return_set);
        }

        var repMsg = "query completed";
        // Print out debug information to arkouda server output.
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } //end of DipDLLqueryMsg

    use CommandMap;
    registerFunction("DipDLLaddNodeLabels", DipDLLaddNodeLabelsMsg, getModuleName());
    registerFunction("DipDLLaddEdgeRelationships", DipDLLaddEdgeRelationshipsMsg, getModuleName());
    registerFunction("DipDLLaddNodeProperties", DipDLLaddNodePropertiesMsg, getModuleName());
    registerFunction("DipDLLaddEdgeProperties", DipDLLaddEdgePropertiesMsg, getModuleName());
    registerFunction("DipDLLqueryMsg", DipDLLqueryMsg, getModuleName());
}