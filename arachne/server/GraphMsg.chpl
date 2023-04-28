module GraphMsg {
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
    * Set the neighbor and start_i arrays for the graph data structure.
    *
    * lsrc: int array of src vertices
    * lstart_i: int array of start vertex values based off src
    * lneighbor: int array of number of neighbors based off src
    *
    * returns: nothing
    */
    private proc set_neighbor(lsrc: [?D1] int, lstart_i: [?D2] int, lneighbor: [?D3] int) { 
        var Ne = D1.size;
        forall i in lstart_i {
            i = -1;
        }
        forall i in lneighbor {
            i = 0;
        }
        for i in 0..Ne-1 do {
            lneighbor[lsrc[i]] += 1;
            if (lstart_i[lsrc[i]] == -1) {
                lstart_i[lsrc[i]] = i;
            }
        }
    }// end set_neighbor()

    /**
    * Search for a given key in a sorted array. 
    *
    * ary: int array
    * l: low index bound
    * h: high index bound
    * key: value we are searching for
    *
    * returns: index if key is found, -1 if not found
    */
    private proc bin_search_v(ary: [?D] int, l: int, h: int, key: int): int throws {
        if ( (l < D.lowBound) || (h > D.highBound) || (l < 0)) {
            return -1;
        }
        if ( (l > h) || ((l == h) &&  (ary[l] != key))) {
            return -1;
        }
        if (ary[l] == key) {
            return l;
        }
        if (ary[h] == key) {
            return h;
        }
        
        var m = (l + h) / 2: int;
        
        if ((m == l) ) {
            return -1;
        }
        if (ary[m] == key ) {
            return m;
        } else {
            if (ary[m] < key) {
                return bin_search_v(ary, m+1, h, key);
            }
            else {
                return bin_search_v(ary, l, m-1, key);
            }
        }
    }// end bin_search_v()

    /**
    * Remap vertices to the range 0..Nv-1.
    *
    * lsrc: src array
    * ldst: dst array
    * num_v: number of vertices
    * node_mapper: mapping of the normalized vertices to the original value
    *
    * returns: new array size
    */
    private proc vertex_remap(lsrc: [?D1] int, ldst: [?D2] int, num_v: int, node_mapper: [?D3] int, node_mapper_r: [?D4], ref rev_node_domain: domain): int throws {
        var num_e = lsrc.size;
        var tmpe: [D1] int;

        var vertex_set = new set(int, parSafe = true);
        forall (i,j) in zip (lsrc,ldst) with (ref vertex_set) {
            vertex_set.add(i);
            vertex_set.add(j);
        }
        var vertex_ary = vertex_set.toArray();
        if (vertex_ary.size != num_v) {
            smLogger.error(getModuleName(), getRoutineName(), getLineNumber(), 
                           "Number of vertices is not equal to the given number!");
        }
        smLogger.debug(getModuleName(), getRoutineName(), getLineNumber(),
                       "Total Vertices=" + vertex_ary.size:string + " ? Nv=" + num_v:string);

        sort(vertex_ary);
        forall i in D3 with (ref rev_node_domain) {
            node_mapper[i] = vertex_ary[i];
            rev_node_domain.add(node_mapper[i]);
        }

        forall i in D3 {
            node_mapper_r[node_mapper[i]] = i;
        }

        forall i in 0..num_e-1 {
            lsrc[i] = bin_search_v(vertex_ary, 0, vertex_ary.size-1, lsrc[i]);
            ldst[i] = bin_search_v(vertex_ary, 0, vertex_ary.size-1, ldst[i]);
        }
        
        return vertex_ary.size;
    }

    /**
    * Sort the two arrays together, src and dst. 
    * 
    * lsrc: src array
    * ldst: dst arrray
    * l_weight: edge weight array
    * lWeightedFlag: if edge weight array exists or not
    * sortw: sort the weight array
    *
    * returns: nothing
    */
    private proc combine_sort(lsrc: [?D1] int, ldst: [?D2] int, le_weight: [?D3] real, 
                              lWeightedFlag: bool, sortw = false: bool) {
        param bitsPerDigit = RSLSD_bitsPerDigit;
        var bitWidths: [0..1] int;
        var negs: [0..1] bool;
        var totalDigits: int;
        var size = D1.size;
        var iv: [D1] int;

        for (bitWidth, ary, neg) in zip(bitWidths, [lsrc,ldst], negs) {
            (bitWidth, neg) = getBitWidth(ary);
            totalDigits += (bitWidth + (bitsPerDigit-1)) / bitsPerDigit;
        }

        /**
        * Sort two integers at the same time, src and dst.
        * 
        * halfDig: number of digits to sort. Two values for src and dst
        *
        * returns index vector that sorts the array.
        */
        // TODO: Does this have to be a proc within a proc?
        proc mergedArgsort(param halfDig): [D1] int throws {
            param numBuckets = 1 << bitsPerDigit;
            param maskDigit = numBuckets-1;
            var merged = makeDistArray(size, halfDig*2*uint(bitsPerDigit));
            for jj in 0..size-1 {
                forall i in 0..halfDig-1 {
                    merged[jj][i] = (((lsrc[jj]:uint) >> ((halfDig-i-1)*bitsPerDigit)) & 
                                       (maskDigit:uint)): uint(bitsPerDigit);
                    merged[jj][i+halfDig] = (((ldst[jj]:uint) >> ((halfDig-i-1)*bitsPerDigit)) & 
                                              (maskDigit:uint)): uint(bitsPerDigit);
                }
            }
            var tmpiv = argsortDefault(merged);
            return tmpiv;
        }// end mergedArgsort()

        try {
            if (totalDigits <= 2) {
                iv = mergedArgsort(2);
            } else {
                iv = mergedArgsort(4);
            }
        } catch {
            try! smLogger.error(getModuleName(), getRoutineName(), getLineNumber(),
                                "Merge array error.");
        }

        var tmpedges = lsrc[iv];
        lsrc = tmpedges;
        tmpedges = ldst[iv];
        ldst = tmpedges;

        if (lWeightedFlag && sortw) {
          var tmpedges = le_weight[iv];
          le_weight = tmpedges;
        }
    }//end combine_sort()

    /**
    * Sort the vertices based on their degrees.
    *
    * lsrc: src array
    * ldst: dst array
    * lstart_i: start_i array
    * lneighbor: neighbor array
    * le_weight: e_weight array
    * lneighborR: neighborR array
    * WeightedFlag: flag noting if the graph is weighted or not
    *
    * returns: nothing
    */
    private proc part_degree_sort(lsrc: [?D1] int, ldst: [?D2] int, lstart_i: [?D3] int, 
                                  lneighbor: [?D4] int, le_weight: [?D5] real, lneighborR: [?D6] int,
                                  lWeightedFlag: bool) {
        var DegreeArray, vertex_mapping: [D4] int;
        var tmpedge: [D1] int;
        var Nv = D4.size;
        var iv: [D1] int;

        coforall loc in Locales  {
            on loc {
                forall i in lneighbor.localSubdomain(){
                    DegreeArray[i] = lneighbor[i] + lneighborR[i];
                }
            }
        }
 
        var tmpiv:[D4] int;
        
        try {
            // Get the index based on each vertex's degree
            tmpiv = argsortDefault(DegreeArray);
        } catch {
            try! smLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), 
                                "Error in part degree sort.");
        }
        forall i in 0..Nv-1 {
            // We assume the vertex ID is in 0..Nv-1
            // Given old vertex ID, map it to the new vertex ID
            vertex_mapping[tmpiv[i]]=i;
        }
        coforall loc in Locales  {
            on loc {
                forall i in lsrc.localSubdomain(){
                    tmpedge[i]=vertex_mapping[lsrc[i]];
                }
            }
        }
        lsrc = tmpedge;
        coforall loc in Locales  {
            on loc {
                forall i in ldst.localSubdomain() {
                    tmpedge[i]=vertex_mapping[ldst[i]];
                  }
            }
        }
        ldst = tmpedge;
        coforall loc in Locales  {
            on loc {
                forall i in lsrc.localSubdomain(){
                    if lsrc[i]>ldst[i] {
                        lsrc[i]<=>ldst[i];
                    }
                }
            }
        }
        try  {
            combine_sort(lsrc, ldst,le_weight,lWeightedFlag, true);
        } catch {
            try! smLogger.error(getModuleName(), getRoutineName(), getLineNumber(),
                                "Combine sort error!");
        }
        set_neighbor(lsrc, lstart_i, lneighbor);
    }// end part_degree_sort()

    /**
    * Degree sort for an undirected graph.
    *
    * lsrc: src array
    * ldst: dst array
    * lstart_i: start_i array
    * lneighbor: neighbor array
    * lsrcR: srcR array
    * ldstR: dstR array
    * lstart_iR: start_iR array
    * lneighborR: neighborR array
    * le_weight: weight array
    * lWeightedFlag: flag noting if graph is directed or not.
    *
    * returns: nothing
    */
    // TODO: degree_sort_u() exists and will be used, but not in this pull request saved for future.
    private proc degree_sort_u(lsrc: [?D1] int, ldst: [?D2] int, lstart_i: [?D3] int,
                               lneighbor: [?D4] int, lsrcR: [?D5] int, ldstR: [?D6] int,
                               lstart_iR: [?D7] int, lneighborR: [?D8] int, le_weight: [?D9] real,
                               lWeightedFlag: bool) {

        part_degree_sort(lsrc, ldst, lstart_i, lneighbor, le_weight, lneighborR, lWeightedFlag);
        coforall loc in Locales {
            on loc {
                forall i in lsrcR.localSubdomain(){
                    lsrcR[i]=ldst[i];
                    ldstR[i]=lsrc[i];
                }
            }
        }
        try {
            combine_sort(lsrcR, ldstR,le_weight,lWeightedFlag, false);
        } catch {
            try! smLogger.error(getModuleName(), getRoutineName(), getLineNumber(),
                               "Combine sort error!");
        }
        set_neighbor(lsrcR, lstart_iR, lneighborR);
    } 

    /**
    * Degree sort for an undirected graph.
    *
    * ary: arry to perform the search in
    * l: lowest index of search
    * h: highest index of search
    * key: value we are looking for
    *
    * returns: true if found. 
    */
    proc binSearchE(ary:[?D] int, l:int, h:int, key:int):int {
        if ( (l>h) || ((l==h) && ( ary[l] != key)))  {
            return -1;
        }
        if (ary[l]==key){
            return l;
        }
        if (ary[h]==key){
            return h;
        }
        var m = (l+h)/2:int;
        if ((m==l) ) {
            return -1;
        }
        if (ary[m]==key ){
            return m;
        } else {
            if (ary[m]<key) {
                return binSearchE(ary,m+1,h,key);
            }
            else {
                return binSearchE(ary,l,m-1,key);
            }
        }
    }// end of binSearchE()

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
                    combine_sort(srcR, dstR, e_weightR, weighted, false);
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
    proc addEdgesFromMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var akarray_srcS = msgArgs.getValueOf("AkArraySrc");
        var akarray_dstS = msgArgs.getValueOf("AkArrayDst");
        var akarray_weightS = msgArgs.getValueOf("AkArrayWeight");
        var weightedS = msgArgs.getValueOf("Weighted");
        var directedS = msgArgs.getValueOf("Directed");

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
                    combine_sort(srcR, dstR, e_weightR, weighted, false);
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
            // if src[i]==dst[i] {
            //     continue;
            // }
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
    * Return the edge arrays for a particular graph for further analysis.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc edgesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var ag = gEntry.graph;

        // Extract the edge arrays.
        var timer:stopwatch;
        timer.start();
        var src = toSymEntry(ag.getComp("SRC"), int).a;
        var dst = toSymEntry(ag.getComp("DST"), int).a;

        // Add new copies of each to the symbol table.
        var repMsg = "";
        var attrNameSrc = st.nextName();
        var attrEntrySrc = new shared SymEntry(src); 
        st.addEntry(attrNameSrc, attrEntrySrc);
        repMsg += "created " + st.attrib(attrNameSrc) + "+ ";

        var attrNameDst = st.nextName();
        var attrEntryDst = new shared SymEntry(dst); 
        st.addEntry(attrNameDst, attrEntryDst);
        repMsg += "created " + st.attrib(attrNameDst);

        timer.stop();
        outMsg = "Extracting edges takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of edgesMsg

    /**
    * Return the nodes of a graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc nodesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var ag = gEntry.graph;

        // Extract the edge arrays.
        var timer:stopwatch;
        timer.start();
        var nodes = toSymEntry(ag.getComp("NODE_MAP"), int).a;

        // Add new copies of each to the symbol table.
        var repMsg = "";
        var attrName = st.nextName();
        var attrEntry = new shared SymEntry(nodes);
        st.addEntry(attrName, attrEntry);
        repMsg += "created " + st.attrib(attrName) + "+ ";

        timer.stop();
        outMsg = "Extracting nodes takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of nodesMsg

    /**
    * Return the degree for each vertex in a graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc degreeMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var ag = gEntry.graph;

        // Extract the neighbor arrays.
        var timer:stopwatch;
        timer.start();
        var neighbor = toSymEntry(ag.getComp("NEIGHBOR"), int).a;
        var src = toSymEntry(ag.getComp("SRC"), int).a;
        var dst = toSymEntry(ag.getComp("DST"), int).a;

        // Generate the degree for each vertex of the graph.
        var out_degree: [neighbor.domain] int;
        var in_degree_at: [neighbor.domain] atomic int;
        if (!ag.isDirected()) {
            var neighborR = toSymEntry(ag.getComp("NEIGHBOR_R"), int).a;
            out_degree = neighbor + neighborR;
        }
        else {
            out_degree = neighbor;

            forall u in dst {
                in_degree_at[u].fetchAdd(1);
            }
        }
        
        // Make final in_degree array regular int instead of atomic int.
        var in_degree: [neighbor.domain] int;
        forall i in neighbor.domain {
            in_degree[i] = in_degree_at[i].read();
        }

        // Add new copies of each to the symbol table.
        var repMsg = "";
        
        var attrNameOut = st.nextName();
        var attrEntryOut = new shared SymEntry(out_degree);
        st.addEntry(attrNameOut, attrEntryOut);

        var attrNameIn = st.nextName();
        var attrEntryIn = new shared SymEntry(in_degree);
        st.addEntry(attrNameIn, attrEntryIn);

        repMsg = "created " + st.attrib(attrNameOut) + "+ created " + st.attrib(attrNameIn);

        timer.stop();
        outMsg = "Creating degree view takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of degreeMsg

    /**
    * Writes the arrays that make up the graph to a file.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc writeGraphArraysMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var path = msgArgs.getValueOf("Path");
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var ag = gEntry.graph;

        var timer:stopwatch;
        timer.start();
        // Invoke utils writeGraphArrays() method.
        writeGraphArrays(ag, path);

        // Add new copies of each to the symbol table.
        var repMsg = "";
        repMsg = "written";

        timer.stop();
        outMsg = "Writing graph arrays to files takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of writeGraphArraysMsg

    /**
    * Populates a graph from arrays read in from a file.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc addEdgesFromGraphArraysFileMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var path = msgArgs.getValueOf("Path");
        var graph = new shared SegGraph(0, 0, false, false);

        var timer:stopwatch;
        timer.start();
        // Invoke utils writeGraphArrays() method.
        readGraphArrays(graph, path);

        // Create new object for new graph.
        var graphEntryName = st.nextName();
        var graphSymEntry = new shared GraphSymEntry(graph);
        st.addEntry(graphEntryName, graphSymEntry);
        var repMsg = graph.n_vertices:string + '+ ' + graph.n_edges:string + '+ ' + graph.isDirected():int:string + '+ ' + graph.isWeighted():int:string + '+' + graphEntryName;

        timer.stop();
        outMsg = "Reading graph arrays from file create graph takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addEdgesFromGraphArraysFileMsg

    /**
    * Adds node labels to the nodes of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc addNodeLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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

        // Create array of lists. 
        var node_labels: [nodes_arr.domain] list(string, parSafe=true);

        // Get graph for usage.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        // Extract the revesred node_map to see what each original node value maps to.
        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;

        var timer:stopwatch;
        timer.start();
        // Add label to the array of linked lists for each node. 
        forall i in nodes_arr.domain {
            var labels = labels_arr[i].split();
            for lbl in labels {
                node_labels[node_map_r[nodes_arr[i]]].append(lbl);
            }
        } 

        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(node_labels):GenSymEntry, "NODE_LABELS");
        timer.stop();
        
        var repMsg = "labels added";
        outMsg = "Adding node labels to property graph takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addNodeLabelsMsg

    /**
    * Adds edge relationships to the edges of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc addEdgeRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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
        var node_map_r = toSymEntryAD(graph.getComp("NODE_MAP_R")).a;
        var start_idx = toSymEntry(graph.getComp("START_IDX"), int).a;
        var neighbor = toSymEntry(graph.getComp("NEIGHBOR"), int).a;
        var src_actual = toSymEntry(graph.getComp("SRC"), int).a;
        var dst_actual = toSymEntry(graph.getComp("DST"), int).a;

        // Create array of lists to store relationships and populate it. 
        var relationships: [src_actual.domain] list(string, parSafe=true);

        forall (i,j) in zip(src.domain, dst.domain) with (ref relationships, ref rel_arr){
            var u = node_map_r[src[i]];
            var v = node_map_r[dst[j]];

            var start = start_idx[u];
            var end = start + neighbor[u];

            var neighborhood = dst_actual[start..end-1];
            var ind = bin_search_v(neighborhood, neighborhood.domain.lowBound, neighborhood.domain.highBound, v);

            relationships[ind].append(rel_arr[i]); // or j
        }
        writeln("relationships = ", relationships);
        
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(relationships):GenSymEntry, "RELATIONSHIPS");
        timer.stop();
        var repMsg = "relationships added";
        outMsg = "Adding relationships to property graph takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addEdgeRelationshipsMsg

    /**
    * Adds properties to the nodes of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc addNodePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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
    } // end of addNodePropertiesMsg

    /**
    * Adds properties to the edges of a property graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc addEdgePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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
    } // end of addEdgePropertiesMsg

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
    registerFunction("addEdgesFrom", addEdgesFromMsg, getModuleName());
    registerFunction("edges", edgesMsg, getModuleName());
    registerFunction("nodes", nodesMsg, getModuleName());
    registerFunction("degree", degreeMsg, getModuleName());
    registerFunction("writeGraphArrays", writeGraphArraysMsg, getModuleName());
    registerFunction("addEdgesFromGraphArraysFile", addEdgesFromGraphArraysFileMsg, getModuleName());
    registerFunction("addNodeLabels", addNodeLabelsMsg, getModuleName());
    registerFunction("addEdgeRelationships", addEdgeRelationshipsMsg, getModuleName());
    registerFunction("addNodeProperties", addNodePropertiesMsg, getModuleName());
    registerFunction("addEdgeProperties", addEdgePropertiesMsg, getModuleName());
    registerFunction("subgraphView", subgraphViewMsg, getModuleName());
}