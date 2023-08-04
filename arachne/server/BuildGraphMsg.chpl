module BuildGraphMsg {
    // Chapel modules.
    use Reflection;
    use Set;
    use Time; 
    use Sort; 
    use List;
    use ReplicatedDist;
    
    // Arachne Modules.
    use Utils;
    use GraphArray;
    use SegmentedString;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use ServerErrors;
    use ServerErrorStrings;
    use ArgSortMsg;
    use AryUtil;
    use Logging;
    use Message;
    
    // Server message logger. 
    private config const logLevel = ServerConfig.logLevel;
    private config const logChannel = ServerConfig.logChannel;
    const bgmLogger = new Logger(logLevel, logChannel);
    var outMsg:string;

    /**
    * Convert akarrays to a graph object. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc addEdgesFromMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        
        // Parse the message from the Python front-end.
        var akarray_srcS = msgArgs.getValueOf("AkArraySrc");
        var akarray_dstS = msgArgs.getValueOf("AkArrayDst");
        var akarray_vmapS = msgArgs.getValueOf("AkArrayVmap");
        var akarray_segS = msgArgs.getValueOf("AkArraySeg");
        var akarray_weightS = msgArgs.getValueOf("AkArrayWeight");
        var weightedS = msgArgs.getValueOf("Weighted");
        var directedS = msgArgs.getValueOf("Directed");
        var num_verticesS = msgArgs.getValueOf("NumVertices");
        var num_edgesS = msgArgs.getValueOf("NumEdges");

        var propertied:bool;
        if msgArgs.contains("IsPropGraph") {
            propertied = true;
        }

        // Extract the names of the arrays and the data for the non-array variables.
        var src_name:string = (akarray_srcS:string);
        var dst_name:string = (akarray_dstS:string);
        var vmap_name:string = (akarray_vmapS:string);
        var seg_name:string = (akarray_segS:string);
        var weight_name:string = (akarray_weightS:string);

        var weighted:bool;
        weightedS = weightedS.toLower();
        weighted = weightedS:bool;

        var directed:bool;
        directedS = directedS.toLower();
        directed = directedS:bool;

        var num_vertices:int;
        num_vertices = num_verticesS:int;

        var num_edges:int;
        num_edges = num_edgesS:int;

        // Timer for populating the graph data structure. 
        var timer:stopwatch;
        timer.start();

        // Get the symbol table entires for the edge, weight, and node map arrays.
        var akarray_src_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(src_name, st);
        var akarray_dst_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(dst_name, st);
        var akarray_vmap_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(vmap_name, st);
        var akarray_seg_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(seg_name, st);
        var akarray_weight_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(weight_name, st);

        // Extract the data for use. 
        var akarray_src_sym = toSymEntry(akarray_src_entry,int);
        var src = akarray_src_sym.a;

        var akarray_dst_sym = toSymEntry(akarray_dst_entry,int);
        var dst = akarray_dst_sym.a;

        var akarray_vmap_sym = toSymEntry(akarray_vmap_entry, int);
        var vmap = akarray_vmap_sym.a;

        var akarray_seg_sym = toSymEntry(akarray_seg_entry, int);
        var segments = akarray_seg_sym.a;

        var graph = new shared SegGraph(num_vertices, num_edges, directed, weighted, propertied);
        graph.withComp(new shared SymEntry(src):GenSymEntry, "SRC")
            .withComp(new shared SymEntry(dst):GenSymEntry, "DST")
            .withComp(new shared SymEntry(segments):GenSymEntry, "SEGMENTS")
            .withComp(new shared SymEntry(vmap):GenSymEntry, "NODE_MAP");

        if weighted {
            select akarray_weight_entry.dtype {
                when DType.Int64 {
                    var akarray_weight_sym = toSymEntry(akarray_weight_entry, int);
                    var e_weight = akarray_weight_sym.a;
                    graph.withComp(new shared SymEntry(e_weight):GenSymEntry, "EDGE_WEIGHT");
                }
                when DType.UInt64 {
                    var akarray_weight_sym = toSymEntry(akarray_weight_entry, uint);
                    var e_weight = akarray_weight_sym.a;
                    graph.withComp(new shared SymEntry(e_weight):GenSymEntry, "EDGE_WEIGHT");
                }
                when DType.Float64 {
                    var akarray_weight_sym = toSymEntry(akarray_weight_entry, real);
                    var e_weight = akarray_weight_sym.a;
                    graph.withComp(new shared SymEntry(e_weight):GenSymEntry, "EDGE_WEIGHT");
                }
                otherwise {
                    var errorMsg = notImplementedError(pn, akarray_weight_entry.dtype);
                    bgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
                    return new MsgTuple(errorMsg, MsgType.ERROR);
                }
            }
        }

        // Create the ranges array that keeps track of the vertices the edge arrays store on each
        // locale.
        var D_sbdmn = {0..numLocales-1} dmapped Replicated();
        var ranges : [D_sbdmn] (int,locale);

        // Write the local subdomain low value to the ranges array.
        coforall loc in Locales {
            on loc {
                var low_vertex = src[src.localSubdomain().low];

                coforall rloc in Locales do on rloc { 
                    ranges[loc.id] = (low_vertex,loc);
                }
            }
        }
        graph.withComp(new shared SymEntry(ranges):GenSymEntry, "RANGES");

        // Add graph to the specific symbol table entry. 
        var graphEntryName = st.nextName();
        var graphSymEntry = new shared GraphSymEntry(graph);
        st.addEntry(graphEntryName, graphSymEntry);
        var repMsg = graphEntryName;
        
        // Print out the length of time it takes to read in and build a known graph file.
        timer.stop();
        outMsg = "Building graph from two edge arrays took " + timer.elapsed():string + " sec";
        
        // Print out debug information to arkouda server output. 
        bgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addEdgesFromMsg

    /**
    * Generates a subgraph from a graph after filtering for specific edge relationships, node
    * labels, and properties.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc subgraphViewMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Get graph for usage and needed arrays.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;
        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
        var start_idx = toSymEntry(graph.getComp("START_IDX"), int).a;
        var neighbor = toSymEntry(graph.getComp("NEIGHBOR"), int).a;
        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var dst = toSymEntry(graph.getComp("DST"), int).a;
        var relationships = toSymEntry(graph.getComp("RELATIONSHIPS"), list(string, parSafe=true)).a;
        var node_labels = toSymEntry(graph.getComp("NODE_LABELS"), list(string, parSafe=true)).a;
        var node_props = toSymEntry(graph.getComp("NODE_PROPS"), list((string, string), parSafe=true)).a;
        var edge_props = toSymEntry(graph.getComp("EDGE_PROPS"), list((string, string), parSafe=true)).a;

        // Keep track of the edges that will make up the subgraph.
        var edge_tracker: [src.domain] int;
        edge_tracker = 0; 

        var timer:stopwatch;
        timer.start();
        // Extract the actual arrays for each of the names above.
        if msgArgs.contains("FilterLabelsExists"){
            var filter_labels_name = msgArgs.getValueOf("FilterLabelsName");
            var filter_labels_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(filter_labels_name, st);
            var filter_labels_sym = toSymEntry(filter_labels_entry, int);
            var filter_labels = filter_labels_sym.a;

            forall u in filter_labels {
                var start = start_idx[node_map_r[u]];
                var end = start + neighbor[node_map_r[u]];
                forall i in start..end-1 {
                    edge_tracker[i] = 1;
                }
            }
        }

        if msgArgs.contains("FilterRelationshipsExists") {
            var filter_relationships_src_name = msgArgs.getValueOf("FilterRelationshipsSrcName");
            var filter_relationships_src_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(filter_relationships_src_name, st);
            var filter_relationships_src_sym = toSymEntry(filter_relationships_src_entry, int);
            var filter_relationships_src = filter_relationships_src_sym.a;

            var filter_relationships_dst_name = msgArgs.getValueOf("FilterRelationshipsDstName");
            var filter_relationships_dst_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(filter_relationships_dst_name, st);
            var filter_relationships_dst_sym = toSymEntry(filter_relationships_dst_entry, int);
            var filter_relationships_dst = filter_relationships_dst_sym.a;

            forall (i,j) in zip(filter_relationships_src.domain, filter_relationships_dst.domain) {
                var u = node_map_r[filter_relationships_src[i]];
                var v = node_map_r[filter_relationships_dst[j]];

                var start = start_idx[u];
                var end = start + neighbor[u];

                var neighborhood = dst[start..end-1];
                var ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, v);

                edge_tracker[ind] = 1;
            }
        }

        if msgArgs.contains("FilterNodePropertiesExists") {
            var filter_node_properties_name = msgArgs.getValueOf("FilterNodePropertiesName");
            var filter_node_properties_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(filter_node_properties_name, st);
            var filter_node_properties_sym = toSymEntry(filter_node_properties_entry, int);
            var filter_node_properties = filter_node_properties_sym.a;

            forall u in filter_node_properties {
                var start = start_idx[node_map_r[u]];
                var end = start + neighbor[node_map_r[u]];
                forall i in start..end-1 {
                    edge_tracker[i] = 1;
                }
            }
        }

        if msgArgs.contains("FilterEdgePropertiesExists") {
            var filter_edge_properties_src_name = msgArgs.getValueOf("FilterEdgePropertiesSrcName");
            var filter_edge_properties_src_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(filter_edge_properties_src_name, st);
            var filter_edge_properties_src_sym = toSymEntry(filter_edge_properties_src_entry, int);
            var filter_edge_properties_src = filter_edge_properties_src_sym.a;

            var filter_edge_properties_dst_name = msgArgs.getValueOf("FilterEdgePropertiesDstName");
            var filter_edge_properties_dst_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(filter_edge_properties_dst_name, st);
            var filter_edge_properties_dst_sym = toSymEntry(filter_edge_properties_dst_entry, int);
            var filter_edge_properties_dst = filter_edge_properties_dst_sym.a;

            forall (i,j) in zip(filter_edge_properties_src.domain, filter_edge_properties_dst.domain) {
                var u = node_map_r[filter_edge_properties_src[i]];
                var v = node_map_r[filter_edge_properties_dst[j]];

                var start = start_idx[u];
                var end = start + neighbor[u];

                var neighborhood = dst[start..end-1];
                var ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, v);

                edge_tracker[ind] = 1;
            }
        }
        var ne = + reduce edge_tracker;
        var new_src = makeDistArray(ne, int);
        var new_dst = makeDistArray(ne, int);

        var next_slot = 0;
        for (i,u) in zip(edge_tracker.domain, edge_tracker) {
            if(u == 1) {
                new_src[next_slot] = src[i];
                new_dst[next_slot] = dst[i];
                next_slot += 1;
            }
        }
        timer.stop();

        // Add new copies of each to the symbol table.
        var repMsg = "";
        
        var attrNameNewSrc = st.nextName();
        var attrEntryNewSrc = new shared SymEntry(new_src);
        st.addEntry(attrNameNewSrc, attrEntryNewSrc);

        var attrNameNewDst = st.nextName();
        var attrEntryNewDst = new shared SymEntry(new_dst);
        st.addEntry(attrNameNewDst, attrEntryNewDst);

        repMsg = "created " + st.attrib(attrNameNewSrc) + "+ created " + st.attrib(attrNameNewDst);
        outMsg = "Generating edge list for subgraph view takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        bgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of subgraphViewMsg

    use CommandMap;
    registerFunction("addEdgesFrom", addEdgesFromMsg, getModuleName());
    registerFunction("subgraphView", subgraphViewMsg, getModuleName());
}