module DipSLLPropertyGraphMsg {
    // Chapel modules.
    use Reflection;
    use Set;
    use Time; 
    use Sort; 
    use List;
    use CopyAggregation;
    use CommDiagnostics;
    
    // Arachne Modules.
    use Utils; 
    use GraphArray;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use SegmentedString;
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
    proc DipSLLaddNodeLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var arrays = msgArgs.getValueOf("Arrays");

        // Extract the names of the arrays storing the vertices and their labels.
        var arrays_list = arrays.split();
        var input_vertices_name = arrays_list[0];
        var input_labels_name = arrays_list[1];
        var label_mapper_name = arrays_list[2];
        
        // Extract the vertices containing labels to be inputted.
        var input_vertices_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(input_vertices_name, st);
        var input_vertices_sym = toSymEntry(input_vertices_entry, int);
        var input_vertices = input_vertices_sym.a;

        // Extract the labels to be inputted for each of the vertices.
        var input_labels_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(input_labels_name, st);
        var input_labels_sym = toSymEntry(input_labels_entry, int);
        var input_labels = input_labels_sym.a;

        // Extract the label mapper to be sent to each locale.
        var label_mapper:SegString = getSegString(label_mapper_name, st);

        // Extract the graph we are operating with from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        // Extract the node_map array to get the internal vertex values for our graph.
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;

        // Create the array of domains that will store the labels for our vertices.
        var vertex_labels: [node_map.domain] domain(int);

        var timer:stopwatch;
        timer.start();
        forall i in input_vertices.domain { // for each input vertex, update its label list. 
            var lbl = input_labels[i]; // local
            var u = input_vertices[i]; // local
            vertex_labels[u] += lbl; // remote
        }
        timer.stop();

        // Add the component for the node labels for the graph.
        graph.withComp(new shared SymEntry(vertex_labels):GenSymEntry, "VERTEX_LABELS");
        graph.withComp(new shared SegStringSymEntry(label_mapper.offsets, label_mapper.values, string):GenSymEntry, "VERTEX_LABELS_MAP");
        var repMsg = "labels added";
        outMsg = "DipSLLaddNodeLabels took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipSLLaddNodeLabelsMsg

    /**
    * Adds edge relationships to the edges of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipSLLaddEdgeRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var arrays = msgArgs.getValueOf("Arrays");

        // Extract the names of the arrays passed to the function.
        var arrays_list = arrays.split();
        var input_internal_edge_indices_name = arrays_list[0];
        var input_relationships_name = arrays_list[1];
        var relationship_mapper_name = arrays_list[2];
        
        // Extract the actual arrays for each of the names above.
        var input_internal_edge_indices_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(input_internal_edge_indices_name, st);
        var input_internal_edge_indices_sym = toSymEntry(input_internal_edge_indices_entry, int);
        var input_internal_edge_indices = input_internal_edge_indices_sym.a;

        var input_relationships_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(input_relationships_name, st);
        var input_relationships_sym = toSymEntry(input_relationships_entry, int);
        var input_relationships = input_relationships_sym.a;

        var relationship_mapper:SegString = getSegString(relationship_mapper_name, st);

        // Get graph for usage and needed arrays.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var src_actual = toSymEntry(graph.getComp("SRC"), int).a;
        var dst_actual = toSymEntry(graph.getComp("DST"), int).a;
        var segments = toSymEntry(graph.getComp("SEGMENTS"), int).a;

        // Create array of lists to store relationships and populate it. 
        var edge_relationships: [src_actual.domain] domain(int);
        
        var timer:stopwatch;
        timer.start();
        forall i in input_internal_edge_indices.domain {
            var rel = input_relationships[i];
            var ind = input_internal_edge_indices[i];
            edge_relationships[ind] += rel;
        }
        
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(edge_relationships):GenSymEntry, "EDGE_RELATIONSHIPS");
        graph.withComp(new shared SegStringSymEntry(relationship_mapper.offsets, relationship_mapper.values, string):GenSymEntry, "EDGE_RELATIONSHIPS_MAP");
        timer.stop();
        var repMsg = "edge relationships added";
        outMsg = "DipSLLaddEdgeRelationships took " + timer.elapsed():string + " sec";
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipSLLaddEdgeRelationshipsMsg

    /**
    * Adds properties to the nodes of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipSLLaddNodePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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
        if graph.hasComp("DIP_SLL_NODE_PROPS") {
            node_props = toSymEntry(graph.getComp("DIP_SLL_NODE_PROPS"), list((string,string), parSafe=true)).a;
        }

        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
        var timer:stopwatch;
        timer.start();
        forall j in nodes_arr.domain {
            for i in 1..arrays_list.size -1 {
                var curr_prop_arr:SegString = getSegString(arrays_list[i], st);
                node_props[node_map_r[nodes_arr[j]]].pushBack((cols_list[i],curr_prop_arr[j]));
            }
        }

        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(node_props):GenSymEntry, "DIP_SLL_NODE_PROPS");
        timer.stop();
        var repMsg = "node properties added";
        outMsg = "DipSLLaddNodeProperties took " + timer.elapsed():string + " sec";
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipSLLaddNodePropertiesMsg

    /**
    * Adds properties to the edges of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipSLLaddEdgePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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
        if(graph.hasComp("DIP_SLL_EDGE_PROPS")) {
            edge_props = toSymEntry(graph.getComp("DIP_SLL_EDGE_PROPS"), list((string,string), parSafe=true)).a;
        }

        forall (i,j) in zip(src.domain, dst.domain) {
            for x in 2..arrays_list.size - 1 {
                var u = node_map_r[src[i]];
                var v = node_map_r[dst[j]];

                var start = start_idx[u];
                var end = start + neighbor[u];

                var neighborhood = dst_actual[start..end - 1];
                var ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, v);

                var curr_prop_arr:SegString = getSegString(arrays_list[x], st);
                edge_props[ind].pushBack((cols_list[x],curr_prop_arr[i])); // or j
            }
        }
        
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(edge_props):GenSymEntry, "DIP_SLL_EDGE_PROPS");
        timer.stop();
        var repMsg = "edge properties added";
        outMsg = "DipSLLaddEdgeProperties took " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of DipSLLaddEdgePropertiesMsg

    proc getNodeLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract the needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");

        // Get graph for usage and the node label mapper. 
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var label_mapper_entry = toSegStringSymEntry(graph.getComp("VERTEX_LABELS_MAP"));

        // Add new copies of each to the symbol table.
        var label_mapper = assembleSegStringFromParts(label_mapper_entry.offsetsEntry, label_mapper_entry.bytesEntry, st);
        var repMsg = 'created ' + st.attrib(label_mapper.name) + '+created bytes.size %t'.format(label_mapper.nBytes);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    proc getEdgeRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract the needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");

        // Get graph for usage and the edge relationship mapper. 
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var relationship_mapper_entry = toSegStringSymEntry(graph.getComp("EDGE_RELATIONSHIPS_MAP"));

        // Add new copies of each to the symbol table.
        var relationship_mapper = assembleSegStringFromParts(relationship_mapper_entry.offsetsEntry, relationship_mapper_entry.bytesEntry, st);
        var repMsg = 'created ' + st.attrib(relationship_mapper.name) + '+created bytes.size %t'.format(relationship_mapper.nBytes);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    /**
    * Queries the property graph and returns a boolean array indicating which nodes contain the 
    * given labels.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipSLLqueryLabelMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var labelsToFindName = msgArgs.getValueOf("LabelsToFindName");

        // Extract graph data for usage in this function.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var node_labels = toSymEntry(graph.getComp("VERTEX_LABELS"), domain(int)).a;

        // Extract the array that contains the labels we are looking for.
        var labels_to_find_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(labelsToFindName, st);
        var labels_to_find_sym = toSymEntry(labels_to_find_entry, int);
        var labels_to_find = labels_to_find_sym.a;

        // Convert array to associative domain to maintain the labels to find.
        var labels_to_find_set : domain(int);
        forall lbl_id in labels_to_find with (ref labels_to_find_set) do labels_to_find_set += lbl_id;
        var return_array : [node_labels.domain] bool;

        // Search in parallel for the nodes that have the labels to find.
        var timer:stopwatch;
        timer.start();
        forall (u, u_label_set) in zip(node_labels.domain, node_labels) with (ref return_array) {
            for lbl in u_label_set {
                if labels_to_find_set.contains(lbl) {
                    return_array[u] = true;
                    break;
                }
            }
        }
        timer.stop();
        var time_msg = "label query DIP-SLL took " + timer.elapsed():string + " sec";
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);

        var retName = st.nextName();
        var retEntry = new shared SymEntry(return_array);
        st.addEntry(retName, retEntry);
        var repMsg = 'created ' + st.attrib(retName);

        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } //end of DipSLLqueryLabelMsg

    /**
    * Queries the property graph and returns a boolean array indicating which edges contain the 
    * given relationships.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc DipSLLqueryRelationshipMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var relationshipsToFindName = msgArgs.getValueOf("RelationshipsToFindName");

        // Extract graph data for usage in this function.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var edge_relationships = toSymEntry(graph.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;

        // Extract the array that contains the relationships we are looking for.
        var relationships_to_find_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(relationshipsToFindName, st);
        var relationships_to_find_sym = toSymEntry(relationships_to_find_entry, int);
        var relationships_to_find = relationships_to_find_sym.a;

        // Convert array to associative domain to maintain the relationships to find.
        var relationships_to_find_set : domain(int);
        forall rel_id in relationships_to_find with (ref relationships_to_find_set) do relationships_to_find_set += rel_id;
        var return_array : [edge_relationships.domain] bool;

        // Search in parallel for the nodes that have the labesl to find.
        var timer:stopwatch;
        timer.start();
        forall (u, u_relationship_set) in zip(edge_relationships.domain, edge_relationships) with (ref return_array) {
            for rel in u_relationship_set {
                if relationships_to_find_set.contains(rel) {
                    return_array[u] = true;
                    break;
                }
            }
        }
        timer.stop();
        var time_msg = "relationship query DIP-SLL took " + timer.elapsed():string + " sec";
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);

        var retName = st.nextName();
        var retEntry = new shared SymEntry(return_array);
        st.addEntry(retName, retEntry);
        var repMsg = 'created ' + st.attrib(retName);

        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } //end of DipSLLqueryRelationshipMsg

    use CommandMap;
    registerFunction("DipSLLaddNodeLabels", DipSLLaddNodeLabelsMsg, getModuleName());
    registerFunction("DipSLLaddEdgeRelationships", DipSLLaddEdgeRelationshipsMsg, getModuleName());
    registerFunction("DipSLLaddNodeProperties", DipSLLaddNodePropertiesMsg, getModuleName());
    registerFunction("DipSLLaddEdgeProperties", DipSLLaddEdgePropertiesMsg, getModuleName());
    registerFunction("getNodeLabels", getNodeLabelsMsg, getModuleName());
    registerFunction("getEdgeRelationships", getEdgeRelationshipsMsg, getModuleName());
    registerFunction("DipSLLqueryLabel", DipSLLqueryLabelMsg, getModuleName());
    registerFunction("DipSLLqueryRelationship", DipSLLqueryRelationshipMsg, getModuleName());
}