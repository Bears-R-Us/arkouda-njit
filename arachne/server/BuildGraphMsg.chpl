module BuildGraphMsg {
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
    * Read a graph whose number of vertices and edges are known before analysis. Saves time in 
    * building the graph data structure. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc readKnownEdgelistMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): 
                              MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var neS = msgArgs.getValueOf("NumOfEdges");
        var nvS = msgArgs.getValueOf("NumOfVertices");
        var pathS = msgArgs.getValueOf("Path");
        var weightedS = msgArgs.getValueOf("Weighted");
        var directedS = msgArgs.getValueOf("Directed");
        var commentsS = msgArgs.getValueOf("Comments");
        var filetypeS = msgArgs.getValueOf("FileType");

        // Convert parsed message to needed data types for Chapel operations.
        var ne:int = (neS:int);
        var nv:int = (nvS:int);
        var path:string = (pathS:string);

        var weighted:bool; 
        weightedS = weightedS.toLower();
        weighted = (weightedS:bool);

        var directed:bool;
        directedS = directedS.toLower();
        directed = (directedS:bool);

        var comments:string = (commentsS:string);
        var filetype:string = (filetypeS:string);

        if (filetype == "mtx") {
            comments = "%";
        }

        // Write message to show which file was read in. 
        outMsg = "path of read file = " + path;
        smLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        // Graph data structure building timer. 
        var timer:stopwatch;
        timer.start();

        // Initializing the arrays that make up our double-index data structure.
        var src = makeDistArray(ne,int);
        var edge_domain = src.domain;

        var neighbor = makeDistArray(nv,int);
        var vertex_domain = neighbor.domain;

        // TODO: We intitialize memory we do not need. For example, directed graphs do not require
        //       reversed arrays. This must be fixed, but may require significant code changes.
        // Edge index arrays. 
        var dst, srcR, dstR, iv: [edge_domain] int;
        var e_weight, e_weightR: [edge_domain] real;
        // Vertex index arrays. 
        var start_i, neighborR, start_iR: [vertex_domain] int;

        // Check to see if the file can be opened correctly. 
        try {
            var f = open(path, ioMode.r);
            f.close();
        } catch {
            smLogger.error(getModuleName(),getRoutineName(),getLineNumber(), "Error opening file.");
        }

        // Read the file line by line. 
        readLinebyLine(src, dst, e_weight, path, comments, weighted);

        // Sort our edge arrays for easy lookup of neighbor vertices. 
        if (!weighted) {
            try { 
                combine_sort(src, dst, e_weight, weighted, false);
            } catch {
                try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                    "Combine sort error.");
            }
        } else {
            try { 
                combine_sort(src, dst, e_weight, weighted, true);
            } catch {
                try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                    "Combine sort error.");
            }
        }

        // Set neighbor (vertex index array) information based off edges, 
        set_neighbor(src, start_i, neighbor);

        // Create the reversed arrays for undirected graphs
        if (!directed) {
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                           "Read undirected graph.");
            coforall loc in Locales  {
                on loc {
                    forall i in srcR.localSubdomain(){
                        srcR[i] = dst[i];
                        dstR[i] = src[i];

                        if (weighted) {
                            e_weightR = e_weight[i];
                        }
                    }
                }
            }
            if (!weighted) {
                try  { 
                    combine_sort(srcR, dstR, e_weightR, weighted, false);
                } catch {
                    try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),"Combine sort error");
                }
            } else {
                try  { 
                    combine_sort(srcR, dstR, e_weightR, weighted, true);
                } catch {
                    try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),"Combine sort error");
                }
            }
            set_neighbor(srcR,start_iR,neighborR);
        }

        // Add graph data structure to the symbol table. 
        var graph = new shared SegGraph(ne, nv, directed, weighted);
        graph.withComp(new shared SymEntry(src):GenSymEntry, "SRC")
             .withComp(new shared SymEntry(dst):GenSymEntry, "DST")
             .withComp(new shared SymEntry(start_i):GenSymEntry, "START_IDX")
             .withComp(new shared SymEntry(neighbor):GenSymEntry, "NEIGHBOR");

        if (!directed) {
            graph.withComp(new shared SymEntry(srcR):GenSymEntry, "SRC_R")
                 .withComp(new shared SymEntry(dstR):GenSymEntry, "DST_R")
                 .withComp(new shared SymEntry(start_iR):GenSymEntry, "START_IDX_R")
                 .withComp(new shared SymEntry(neighborR):GenSymEntry, "NEIGHBOR_R");
        }

        if (weighted) {
            graph.withComp(new shared SymEntry(e_weight):GenSymEntry, "EDGE_WEIGHT");

            if (!directed) {
                graph.withComp(new shared SymEntry(e_weightR):GenSymEntry, "EDGE_WEIGHT_R");
            }
        }

        // Add graph to the specific symbol table entry. 
        var graphEntryName = st.nextName();
        var graphSymEntry = new shared GraphSymEntry(graph);
        st.addEntry(graphEntryName, graphSymEntry);
        var repMsg = nvS + '+ ' + neS + '+ ' + directedS + '+ ' + weighted:int:string + '+' + graphEntryName;
        
        // Print out the length of time it takes to read in and build a known graph file.
        timer.stop();
        outMsg = "Building graph from known edge file takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of readKnownEdgelistMsg

    /**
    * Read a graph whose number of vertices and edges are unknown before analysis.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc readEdgelistMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var pathS = msgArgs.getValueOf("Path");
        var weightedS = msgArgs.getValueOf("Weighted");
        var directedS = msgArgs.getValueOf("Directed");
        var commentsS = msgArgs.getValueOf("Comments");
        var filetypeS = msgArgs.getValueOf("FileType");

        // Convert parsed message to needed data types for Chapel operations.
        var path:string = (pathS:string);

        var weighted:bool; 
        weightedS = weightedS.toLower();
        weighted = (weightedS:bool);

        var directed:bool;
        directedS = directedS.toLower();
        directed = (directedS:bool);

        var comments:string = (commentsS:string);
        var filetype:string = (filetypeS:string);

        if (filetype == "mtx") {
            comments = "%";
        }

        // Graph data structure building timer. 
        var timer:stopwatch;
        timer.start();

        // Check to see if the file can be opened correctly. 
        try {
            var f = open(path, ioMode.r);
            f.close();
        } catch {
            smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),"Error opening file.");
        }

        // Perform a first pass over the file to get number of edges and vertices.
        var f = open(path, ioMode.r);
        var r = f.reader(kind = ionative);
        var line:string;
        var a,b,c:string;
        var edge_count:int = 0;

        // Add vertices to a set and count number of lines which is number of edges.
        var vertex_set = new set(int, parSafe = true);
        while (r.readLine(line)) {
            // Ignore comments for all files and matrix dimensions for mtx files.
            if (line[0] == comments) {
                edge_count -= 1; 
                continue;
            } else {
                if (edge_count < 0) {
                    edge_count = 0; 
                    continue;
                }
            }

            // Parse our vertices and weights, if applicable. 
            if (weighted == false) {
                (a,b) = line.splitMsgToTuple(2);
            } else {
                (a,b,c) = line.splitMsgToTuple(3);
            }
            
            // Add vertices to a vertex_set. 
            vertex_set.add(a:int);
            vertex_set.add(b:int);

            // Keep track of the number of edges read from file lines. 
            edge_count += 1;
        }

        // Write the number of edges and vertices. 
        var ne:int = edge_count; 
        var nv:int = (vertex_set.size:int);

        // Initializing the arrays that make up our double-index data structure.
        var src = makeDistArray(ne, int);
        var edge_domain = src.domain;

        var neighbor = makeDistArray(nv,int);
        var vertex_domain = neighbor.domain;

        // TODO: We intitialize memory we do not need. For example, directed graphs do not require
        //       reversed arrays. This must be fixed, but may require significant code changes.
        // Edge index arrays. 
        var dst, srcR, dstR, iv: [edge_domain] int;
        var e_weight, e_weightR: [edge_domain] real;
        // Vertex index arrays. 
        var start_i, neighborR, start_iR: [vertex_domain] int;

        // Read the file line by line.
        readLinebyLine(src, dst, e_weight, path, comments, weighted); 
        
        // Remap the vertices to a new range.
        var node_map: [vertex_domain] int;
        var rev_node_domain: domain(int);
        var node_map_r: [rev_node_domain] int;
        var new_nv:int = vertex_remap(src, dst, nv, node_map, node_map_r, rev_node_domain);
      
        if (!weighted) {
            try { 
                combine_sort(src, dst, e_weight, weighted, false);
            } catch {
                try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),"Combine sort error.");
            }
        } else {
            try { 
                combine_sort(src, dst, e_weight, weighted, true);
            } catch {
                try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),"Combine sort error.");
            }
        }

        // Set neighbor (vertex index array) information based off edges,
        set_neighbor(src, start_i, neighbor);

        // Read in undirected graph parts into reversed arrays.
        if (!directed) {
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),"Read undirected graph.");
            coforall loc in Locales  {
                on loc {
                    forall i in srcR.localSubdomain(){
                        srcR[i] = dst[i];
                        dstR[i] = src[i];
                        e_weightR = e_weight[i];
                    }
                }
            }
            if (!weighted) {
                try  { 
                    combine_sort(srcR, dstR, e_weightR, weighted, false);
                } catch {
                    try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                        "Combine sort error");
                }
            } else {
                try  { 
                    combine_sort(srcR, dstR, e_weightR, weighted, true);
                } catch {
                    try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                        "Combine sort error");
                }
            }
            set_neighbor(srcR, start_iR, neighborR);
        }

        // Remove self loops and duplicated edges.
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                       "Remove self loops and duplicated edges");
        var cur = 0;
        var tmpsrc = src;
        var tmpdst = dst;
        var tmpe_weight = e_weight;
        
        for i in 0..ne - 1 {
            // Ignore self-loops. 
            if src[i]==dst[i] {
                continue;
            }
            if (cur == 0) {
                tmpsrc[cur] = src[i];
                tmpdst[cur] = dst[i]; 
                tmpe_weight[cur] = e_weight[i];
                cur += 1;
                continue;
            }
            
            // Ignore duplicated edges.
            if (tmpsrc[cur-1] == src[i]) && (tmpdst[cur-1] == dst[i]) {
                continue;
            } else {
                if (src[i] > dst[i]) {
                    var u = src[i]:int;
                    var v = dst[i]:int;
                    var lu = start_i[u]:int;
                    var nu = neighbor[u]:int;
                    var lv = start_i[v]:int;
                    var nv = neighbor[v]:int;
                    var DupE:int;
                    
                    // Find v->u.
                    DupE = binSearchE(dst,lv,lv+nv-1,u);
                    if (DupE != -1) {
                        continue;
                    }
                }
                tmpsrc[cur] = src[i];
                tmpdst[cur] = dst[i]; 
                tmpe_weight[cur] = e_weight[i]; 
                cur+=1;
            }
        }
        var new_ne = cur;  
 
        var mysrc = makeDistArray(new_ne, int);
        var myedgeD = mysrc.domain;

        var myneighbor = makeDistArray(new_nv, int);
        var myvertexD = myneighbor.domain;

        // Arrays made from the edge domain. 
        var mydst, mysrcR, mydstR, myiv: [myedgeD] int;
        var mye_weight, mye_weightR: [myedgeD] real;

        // Arrays made from the vertex domain. 
        var mystart_i, myneighborR, mystart_iR, mydepth: [myvertexD] int;
        
        // Finish creating the new arrays after removing self-loops and multiedges.
        if (new_ne < ne ) {
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                "Removed " + (ne - new_ne):string + " edges");

            forall i in 0..new_ne-1 {
                mysrc[i] = tmpsrc[i];
                mydst[i] = tmpdst[i];
                mye_weight[i] = tmpe_weight[i];
            }
            try { 
                combine_sort(mysrc, mydst, mye_weight, weighted, false);
            } catch {
                try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                    "Combine sort error.");
            }

            set_neighbor(mysrc, mystart_i, myneighbor);

            if (!directed) { // undirected graph
                coforall loc in Locales  {
                    on loc {
                        forall i in mysrcR.localSubdomain(){
                            mysrcR[i] = mydst[i];
                            mydstR[i] = mysrc[i];
                            mye_weightR[i] = mye_weight[i];
                        }
                    }
                }

                if(!weighted) {
                    try  { 
                        combine_sort(mysrcR, mydstR, mye_weightR, weighted, false);
                    } catch {
                        try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                            "Combine sort error");
                    }
                } else {
                    try  { 
                        combine_sort(mysrcR, mydstR, mye_weightR, weighted, true);
                    } catch {
                        try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                            "Combine sort error");
                    }
                }
                
                set_neighbor(mysrcR, mystart_iR, myneighborR);
            }//end of undirected
        }

        // Finish building graph data structure.
        var graph = new shared SegGraph(ne, nv, directed, weighted);
        if (new_ne < ne) { // Different arrays for when edges had to be removed.
            graph.withComp(new shared SymEntry(mysrc):GenSymEntry, "SRC")
                .withComp(new shared SymEntry(mydst):GenSymEntry, "DST")
                .withComp(new shared SymEntry(mystart_i):GenSymEntry, "START_IDX")
                .withComp(new shared SymEntry(myneighbor):GenSymEntry, "NEIGHBOR")
                .withComp(new shared SymEntry(node_map):GenSymEntry, "NODE_MAP")
                .withComp(new shared SymEntryAD(node_map_r):GenSymEntry, "NODE_MAP_R");

            if (!directed) {
                graph.withComp(new shared SymEntry(mysrcR):GenSymEntry, "SRC_R")
                    .withComp(new shared SymEntry(mydstR):GenSymEntry, "DST_R")
                    .withComp(new shared SymEntry(mystart_iR):GenSymEntry, "START_IDX_R")
                    .withComp(new shared SymEntry(myneighborR):GenSymEntry, "NEIGHBOR_R");
            }

            if (weighted) {
                graph.withComp(new shared SymEntry(mye_weight):GenSymEntry, "EDGE_WEIGHT");

                if (!directed) {
                    graph.withComp(new shared SymEntry(mye_weightR):GenSymEntry, "EDGE_WEIGHT_R");
                }
            }
        } else { // No edge removals.
            graph.withComp(new shared SymEntry(src):GenSymEntry, "SRC")
                .withComp(new shared SymEntry(dst):GenSymEntry, "DST")
                .withComp(new shared SymEntry(start_i):GenSymEntry, "START_IDX")
                .withComp(new shared SymEntry(neighbor):GenSymEntry, "NEIGHBOR")
                .withComp(new shared SymEntry(node_map):GenSymEntry, "NODE_MAP")
                .withComp(new shared SymEntryAD(node_map_r):GenSymEntry, "NODE_MAP_R");

            if (!directed) {
                graph.withComp(new shared SymEntry(srcR):GenSymEntry, "SRC_R")
                    .withComp(new shared SymEntry(dstR):GenSymEntry, "DST_R")
                    .withComp(new shared SymEntry(start_iR):GenSymEntry, "START_IDX_R")
                    .withComp(new shared SymEntry(neighborR):GenSymEntry, "NEIGHBOR_R");
            }

            if (weighted) {
                graph.withComp(new shared SymEntry(e_weight):GenSymEntry, "EDGE_WEIGHT");

                if (!directed) {
                    graph.withComp(new shared SymEntry(e_weightR):GenSymEntry, "EDGE_WEIGHT_R");
                }
            }
        }

        // Add graph to the specific symbol table entry. 
        var graphEntryName = st.nextName();
        var graphSymEntry = new shared GraphSymEntry(graph);
        st.addEntry(graphEntryName, graphSymEntry);
        var repMsg = new_nv:string + '+ ' + new_ne:string + '+ ' + directedS + '+ ' + weighted:int:string + '+' + graphEntryName;

        
        // Print out the length of time it takes to read in and build a known graph file.
        timer.stop();
        outMsg = "Building graph from unknown edge file takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of readEdgelistMsg

    /**
    * Convert akarrays to a graph object. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc addEdgesFromChapelVersionMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var akarray_srcS = msgArgs.getValueOf("AkArraySrc");
        var akarray_dstS = msgArgs.getValueOf("AkArrayDst");
        var akarray_weightS = msgArgs.getValueOf("AkArrayWeight");
        var weightedS = msgArgs.getValueOf("Weighted");
        var directedS = msgArgs.getValueOf("Directed");

        var is_prop_graph:bool;
        if msgArgs.contains("IsPropGraph") {
            is_prop_graph = true;
        }

        // Convert parsed message to needed data types for Chapel operations.
        var src_name:string = (akarray_srcS:string);
        var dst_name:string = (akarray_dstS:string);
        var weight_name:string = (akarray_weightS:string);

        var weighted:bool; 
        weightedS = weightedS.toLower();
        weighted = (weightedS:bool);

        var directed:bool;
        directedS = directedS.toLower();
        directed = (directedS:bool);

        // Graph data structure building timer. 
        var timer:stopwatch;
        timer.start();

        // Extract the entry names from the symbol table to extract the data for use.
        var akarray_src_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(src_name, st);
        var akarray_dst_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(dst_name, st);

        // Extract the data for use. 
        var akarray_src_sym = toSymEntry(akarray_src_entry,int);
        var src = akarray_src_sym.a;

        var akarray_dst_sym = toSymEntry(akarray_dst_entry,int);
        var dst = akarray_dst_sym.a;

        // Perform a first pass over the data to get number of edges and vertices.
        var a,b,c:string;
        var curline:int = 0;

        // Add vertices to a set and count number of lines which is number of edges.
        var vertex_set = new set(int, parSafe = true);
        forall (u,v) in zip(src, dst) with (ref vertex_set){            
            // Add vertices to a vertex_set. 
            vertex_set.add(u:int);
            vertex_set.add(v:int);
        }

        // Write the number of edges and vertices. 
        var ne:int = src.size:int; 
        var nv:int = (vertex_set.size:int);

        // Initializing the arrays that make up our double-index data structure.
        var edge_domain = src.domain;

        var neighbor = makeDistArray(nv,int);
        var vertex_domain = neighbor.domain;

        // TODO: We intitialize memory we do not need. For example, directed graphs do not require
        //       reversed arrays. This must be fixed, but may require significant code changes.
        // Edge index arrays. 
        var srcR, dstR, iv: [edge_domain] int;
        var e_weight, e_weightR: [edge_domain] real;
        // Vertex index arrays. 
        var start_i, neighborR, start_iR: [vertex_domain] int;

        if weighted {
            var akarray_weight_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(weight_name, st);
            var akarray_weight_sym = toSymEntry(akarray_weight_entry, real);
            e_weight = akarray_weight_sym.a;
        }

        // Remap the vertices to a new range.
        var node_map: [vertex_domain] int;
        var rev_node_domain: domain(int);
        var node_map_r: [rev_node_domain] int;
        var new_nv:int = vertex_remap(src, dst, nv, node_map, node_map_r, rev_node_domain);
      
        if (!weighted) {
            try { 
                combine_sort(src, dst, e_weight, weighted, false);
            } catch {
                try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),"Combine sort error.");
            }
        } else {
            try { 
                combine_sort(src, dst, e_weight, weighted, true);
            } catch {
                try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),"Combine sort error.");
            }
        }

        // Set neighbor (vertex index array) information based off edges,
        set_neighbor(src, start_i, neighbor);

        // Read in undirected graph parts into reversed arrays.
        if (!directed) {
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),"Read undirected graph.");
            coforall loc in Locales  {
                on loc {
                    forall i in srcR.localSubdomain(){
                        srcR[i] = dst[i];
                        dstR[i] = src[i];
                        e_weightR = e_weight[i];
                    }
                }
            }
            if (!weighted) {
                try  { 
                    combine_sort(srcR, dstR, e_weightR, weighted, false);
                } catch {
                    try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                        "Combine sort error");
                }
            } else {
                try  { 
                    combine_sort(srcR, dstR, e_weightR, weighted, true);
                } catch {
                    try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                        "Combine sort error");
                }
            }
            set_neighbor(srcR, start_iR, neighborR);
        }

        // Remove self loops and duplicated edges.
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                       "Remove self loops and duplicated edges");
        var cur = 0;
        var tmpsrc = src;
        var tmpdst = dst;
        var tmpe_weight = e_weight;
        
        for i in 0..ne - 1 {
            // Ignore self-loops. 
            if !is_prop_graph {
                if src[i]==dst[i] {
                    continue;
                }
            }
            if (cur == 0) {
                tmpsrc[cur] = src[i];
                tmpdst[cur] = dst[i]; 
                tmpe_weight[cur] = e_weight[i];
                cur += 1;
                continue;
            }
            
            // Ignore duplicated edges.
            if (tmpsrc[cur-1] == src[i]) && (tmpdst[cur-1] == dst[i]) {
                continue;
            } else {
                if ((src[i] > dst[i]) && !directed) {
                    var u = src[i]:int;
                    var v = dst[i]:int;
                    var lu = start_i[u]:int;
                    var nu = neighbor[u]:int;
                    var lv = start_i[v]:int;
                    var nv = neighbor[v]:int;
                    var DupE:int;
                    
                    // Find v->u.
                    DupE = binSearchE(dst,lv,lv+nv-1,u);
                    if (DupE != -1) {
                        continue;
                    }
                }
                tmpsrc[cur] = src[i];
                tmpdst[cur] = dst[i]; 
                tmpe_weight[cur] = e_weight[i]; 
                cur+=1;
            }
        }
        var new_ne = cur;  
 
        var mysrc = makeDistArray(new_ne, int);
        var myedgeD = mysrc.domain;

        var myneighbor = makeDistArray(new_nv, int);
        var myvertexD=myneighbor.domain;

        // Arrays made from the edge domain. 
        var mydst, mysrcR, mydstR, myiv: [myedgeD] int;
        var mye_weight, mye_weightR: [myedgeD] real;

        // Arrays made from the vertex domain. 
        var mystart_i, myneighborR, mystart_iR, mydepth: [myvertexD] int;
        
        // Finish creating the new arrays after removing self-loops and multiedges.
        if (new_ne < ne ) {
            smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                "Removed " + (ne - new_ne):string + " edges");

            forall i in 0..new_ne-1 {
                mysrc[i] = tmpsrc[i];
                mydst[i] = tmpdst[i];
                mye_weight[i] = tmpe_weight[i];
            }
            try { 
                combine_sort(mysrc, mydst, mye_weight, weighted, false);
            } catch {
                try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                    "Combine sort error.");
            }

            set_neighbor(mysrc, mystart_i, myneighbor);

            if (!directed) { // undirected graph
                coforall loc in Locales  {
                    on loc {
                        forall i in mysrcR.localSubdomain(){
                            mysrcR[i] = mydst[i];
                            mydstR[i] = mysrc[i];
                            mye_weightR[i] = mye_weight[i];
                        }
                    }
                }

                if(!weighted) {
                    try  { 
                        combine_sort(mysrcR, mydstR, mye_weightR, weighted, false);
                    } catch {
                        try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                            "Combine sort error");
                    }
                } else {
                    try  { 
                        combine_sort(mysrcR, mydstR, mye_weightR, weighted, true);
                    } catch {
                        try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                            "Combine sort error");
                    }
                }
                set_neighbor(mysrcR, mystart_iR, myneighborR);
            }//end of undirected
        }

        // Finish building graph data structure.
        var graph = new shared SegGraph(ne, nv, directed, weighted);
        if (new_ne < ne) { // Different arrays for when edges had to be removed.
            graph.withComp(new shared SymEntry(mysrc):GenSymEntry, "SRC")
                .withComp(new shared SymEntry(mydst):GenSymEntry, "DST")
                .withComp(new shared SymEntry(mystart_i):GenSymEntry, "START_IDX")
                .withComp(new shared SymEntry(myneighbor):GenSymEntry, "NEIGHBOR")
                .withComp(new shared SymEntry(node_map):GenSymEntry, "NODE_MAP")
                .withComp(new shared SymEntryAD(node_map_r):GenSymEntry, "NODE_MAP_R");

            if (!directed) {
                graph.withComp(new shared SymEntry(mysrcR):GenSymEntry, "SRC_R")
                    .withComp(new shared SymEntry(mydstR):GenSymEntry, "DST_R")
                    .withComp(new shared SymEntry(mystart_iR):GenSymEntry, "START_IDX_R")
                    .withComp(new shared SymEntry(myneighborR):GenSymEntry, "NEIGHBOR_R");
            }

            if (weighted) {
                graph.withComp(new shared SymEntry(mye_weight):GenSymEntry, "EDGE_WEIGHT");

                if (!directed) {
                    graph.withComp(new shared SymEntry(mye_weightR):GenSymEntry, "EDGE_WEIGHT_R");
                }
            }
        } else { // No edge removals.
            graph.withComp(new shared SymEntry(src):GenSymEntry, "SRC")
                .withComp(new shared SymEntry(dst):GenSymEntry, "DST")
                .withComp(new shared SymEntry(start_i):GenSymEntry, "START_IDX")
                .withComp(new shared SymEntry(neighbor):GenSymEntry, "NEIGHBOR")
                .withComp(new shared SymEntry(node_map):GenSymEntry, "NODE_MAP")
                .withComp(new shared SymEntryAD(node_map_r):GenSymEntry, "NODE_MAP_R");

            if (!directed) {
                graph.withComp(new shared SymEntry(srcR):GenSymEntry, "SRC_R")
                    .withComp(new shared SymEntry(dstR):GenSymEntry, "DST_R")
                    .withComp(new shared SymEntry(start_iR):GenSymEntry, "START_IDX_R")
                    .withComp(new shared SymEntry(neighborR):GenSymEntry, "NEIGHBOR_R");
            }

            if (weighted) {
                graph.withComp(new shared SymEntry(e_weight):GenSymEntry, "EDGE_WEIGHT");

                if (!directed) {
                    graph.withComp(new shared SymEntry(e_weightR):GenSymEntry, "EDGE_WEIGHT_R");
                }
            }
        }

        // Add graph to the specific symbol table entry. 
        var graphEntryName = st.nextName();
        var graphSymEntry = new shared GraphSymEntry(graph);
        st.addEntry(graphEntryName, graphSymEntry);
        var repMsg = new_nv:string + '+ ' + new_ne:string + '+ ' + directedS + '+ ' + weighted:int:string + '+' + graphEntryName;
        
        // Print out the length of time it takes to read in and build a known graph file.
        timer.stop();
        outMsg = "Building graph from two edge arrays takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addEdgesFromMsg

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
        // Parse the message from the Python front-end.
        var akarray_srcS = msgArgs.getValueOf("AkArraySrc");
        var akarray_dstS = msgArgs.getValueOf("AkArrayDst");
        var akarray_vmapS = msgArgs.getValueOf("AkArrayVmap");
        var akarray_neiS = msgArgs.getValueOf("AkArrayNei");
        var akarray_strS = msgArgs.getValueOf("AkArrayStr");
        var akarray_weightS = msgArgs.getValueOf("AkArrayWeight");
        var weightedS = msgArgs.getValueOf("Weighted");
        var directedS = msgArgs.getValueOf("Directed");
        var num_verticesS = msgArgs.getValueOf("NumVertices");
        var num_edgesS = msgArgs.getValueOf("NumEdges");

        var is_prop_graph:bool;
        if msgArgs.contains("IsPropGraph") {
            is_prop_graph = true;
        }

        // Extract the names of the arrays and the data for the non-array variables.
        var src_name:string = (akarray_srcS:string);
        var dst_name:string = (akarray_dstS:string);
        var vmap_name:string = (akarray_vmapS:string);
        var nei_name:string = (akarray_neiS:string);
        var str_name:string = (akarray_strS:string);
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
        var akarray_nei_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(nei_name, st);
        var akarray_str_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(str_name, st);
        var akarray_weight_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(weight_name, st);

        // Extract the data for use. 
        var akarray_src_sym = toSymEntry(akarray_src_entry,int);
        var src = akarray_src_sym.a;

        var akarray_dst_sym = toSymEntry(akarray_dst_entry,int);
        var dst = akarray_dst_sym.a;

        var akarray_vmap_sym = toSymEntry(akarray_vmap_entry, int);
        var vmap = akarray_vmap_sym.a;

        var akarray_nei_sym = toSymEntry(akarray_nei_entry, int);
        var neighbor = akarray_nei_sym.a;

        var akarray_str_sym = toSymEntry(akarray_str_entry, int);
        var start_i = akarray_str_sym.a;

        var akarray_weight_sym = toSymEntry(akarray_weight_entry, real);
        var e_weight = akarray_weight_sym.a;

        var graph = new shared SegGraph(num_edges, num_vertices, directed, weighted);
        graph.withComp(new shared SymEntry(src):GenSymEntry, "SRC")
            .withComp(new shared SymEntry(dst):GenSymEntry, "DST")
            .withComp(new shared SymEntry(start_i):GenSymEntry, "START_IDX")
            .withComp(new shared SymEntry(neighbor):GenSymEntry, "NEIGHBOR")
            .withComp(new shared SymEntry(vmap):GenSymEntry, "NODE_MAP");

        if (weighted) {
            graph.withComp(new shared SymEntry(e_weight):GenSymEntry, "EDGE_WEIGHT");
        }

        // Add graph to the specific symbol table entry. 
        var graphEntryName = st.nextName();
        var graphSymEntry = new shared GraphSymEntry(graph);
        st.addEntry(graphEntryName, graphSymEntry);
        var repMsg = graphEntryName;
        
        // Print out the length of time it takes to read in and build a known graph file.
        timer.stop();
        outMsg = "Building graph from two edge arrays took " + timer.elapsed():string + " sec";
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

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
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of subgraphViewMsg

    use CommandMap;
    registerFunction("readKnownEdgelist", readKnownEdgelistMsg, getModuleName());
    registerFunction("readEdgelist", readEdgelistMsg, getModuleName());
    registerFunction("addEdgesFromChapelVersion", addEdgesFromChapelVersionMsg, getModuleName());
    registerFunction("addEdgesFrom", addEdgesFromMsg, getModuleName());
    registerFunction("subgraphView", subgraphViewMsg, getModuleName());
}