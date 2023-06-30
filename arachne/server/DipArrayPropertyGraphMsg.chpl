module DipArrayPropertyGraphMsg {
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
        
        // Extract the revesred node_map to see what each original node value maps to.
        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
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
        var byte_label_arrays: [D_byte_label_arrays] bool;
        byte_label_arrays = false;

        // Populate the two-dimesional byte array. 
        forall i in nodes_arr.domain {
            var lbl = labels_arr[i];
            var lbl_ind = lbl_arr[lbl];
            var vertex = node_map_r[nodes_arr[i]];

            byte_label_arrays[lbl_ind,vertex] = true;
        }
        // var count_2: atomic int = 0;
        // forall a in byte_label_arrays with (ref count_2) do if a == true then count_2.add(1);
        // Add the component for the node labels for the graph. 
        
        // TODO: add two-dimensional array into symbol table!
        // graph.withComp(new shared SymEntry(byte_label_arrays):GenSymEntry, "DIP_ARR_NODE_LABELS");
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

        // Create array of lists to store relationships and populate it. 
        var relationships: [src_actual.domain] list(string, parSafe=true);

        /*****************************************************/
        /********************* DIP-Array *********************/
        /*****************************************************/
        timer.clear();
        timer.start();
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
            var ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, v);

            byte_relationship_arrays[relations_arr[rel_arr[i]],[ind]] = true;
        }
        var count_2: atomic int = 0;
        forall a in byte_relationship_arrays with (ref count_2) do if a == true then count_2.add(1);
        timer.stop();
        writeln("$$$$$$$$$$ BUILDING DIP-array RELATIONSHIPS TIME TAKES: ", timer.elapsed());
        writeln("$$$$$relationship_count = ", count_2);
        writeln();

        /*************************************************************************/
        /******************** QUERYING ENTIRE RELATIONSHIPS **********************/
        /*************************************************************************/
        var relationships_to_find = ["teammates", "friends"];

        /********************* DIP-array *********************/
        timer.clear();
        timer.start();
        var edges_list = new list((int,int), parSafe=true);
        
        // Turn relationships to find into an associative domain.
        var D_relationships_to_find: domain(string);
        D_relationships_to_find += relationships_to_find;
        
        // Slice our associative array of relationship_name to index value according to the 
        // relationships we are looking for. Save these indices to an associative domain for easy
        // lookup.
        var relations_arr_slice = relations_arr[D_relationships_to_find];
        var D_indices_of_relationships_to_find: domain(int);
        D_indices_of_relationships_to_find += relations_arr_slice;

        var forall_comp : stopwatch;
        var count_forall1 = 0;
        var count_forall2 = 0;
        writeln("dims = ", D_byte_relationship_arrays.dims());
        forall_comp.start();
        forall (i,j) in byte_relationship_arrays.domain with (ref edges_list, + reduce count_forall1) {
            if D_indices_of_relationships_to_find.contains(i) {
                if byte_relationship_arrays[i,j] == true { 
                    count_forall1 += 1;
                    edges_list.append((src_actual[j], dst_actual[j]));
                }
            }
        }
        forall_comp.stop();
        writeln("$$$$$ one forall loop time = ", forall_comp.elapsed());
        edges_list.clear();
        forall_comp.clear();
        forall_comp.start();
        forall i in D_byte_relationship_arrays.dim(0) with (ref edges_list, + reduce count_forall2) {
            forall j in D_byte_relationship_arrays.dim(1) with (ref edges_list, + reduce count_forall2) {
                if D_indices_of_relationships_to_find.contains(i) {
                    if byte_relationship_arrays[i,j] == true {
                        count_forall2 += 1;
                        edges_list.append((src_actual[j], dst_actual[j]));
                    }
                }
            }
        }
        forall_comp.stop();
        writeln("$$$$$ two forall loop time = ", forall_comp.elapsed());
        
        timer.stop();
        writeln("$$$$$$$$$$ QUERYING DIP-array RELATIONSHIPS TIME TAKES: ", timer.elapsed());
        writeln("$$$$$DIP-array query size = ", edges_list.size);
        writeln();

        /**********************************************************/
        /******************** QUERYING EDGES **********************/
        /**********************************************************/
        var src_to_find = [32,22];
        var dst_to_find = [1,1];

        /********************* DIP-array *********************/
        timer.clear();
        timer.start();
        var relationships_list = new list((int,string), parSafe=true);        

        for i in src_to_find.domain {
            var u = src_to_find[i];
            var v = dst_to_find[i];
            
            var ui = node_map_r[u];
            var vi = node_map_r[v];

            var start = start_idx[ui];
            var end = start + neighbor[ui];

            var neighborhood = dst_actual[start..end-1];
            var edge_ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, vi);
            forall j in D_byte_relationship_arrays.dim(0) with (ref relationships_list) {
                if (byte_relationship_arrays[j, edge_ind] == true) then relationships_list.append((j,rel_set_arr[j]));
            }
        }
        timer.stop();
        writeln("$$$$$$$$$$ QUERYING DIP-array EDGES TIME TAKES: ", timer.elapsed());
        writeln("$$$$$DIP-array query size = ", relationships_list.size);
        writeln();
        
        /****************************************************/
        /********************* END CODE *********************/
        /****************************************************/
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(relationships):GenSymEntry, "RELATIONSHIPS");
        timer.stop();
        var repMsg = "relationships added";
        outMsg = "Adding relationships to property graph takes " + timer.elapsed():string;
        
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
    } // end of DipArrayaddEdgePropertiesMsg
    use CommandMap;
    registerFunction("DipArrayaddNodeLabels", DipArrayaddNodeLabelsMsg, getModuleName());
    registerFunction("DipArrayaddEdgeRelationships", DipArrayaddEdgeRelationshipsMsg, getModuleName());
    registerFunction("DipArrayaddNodeProperties", DipArrayaddNodePropertiesMsg, getModuleName());
    registerFunction("DipArrayaddEdgeProperties", DipArrayaddEdgePropertiesMsg, getModuleName());
}