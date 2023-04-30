module Utils {
    // Chapel modules.
    use IO;
    use Map;
    use Sort;
    use List;
    use Set;

    // Arachne modules.
    use GraphArray;

    // Arkouda modules. 
    use Logging;
    use MultiTypeSymEntry;
    use MultiTypeSymbolTable;
    use ServerConfig;
    use ArgSortMsg;
    use AryUtil;

    // Allow graphs to be printed server-side? Defaulted to false. MUST BE MANUALLY CHANGED.
    // TODO: make this a param instead of a set variable?
    var debug_print = false; 

    // Server message logger. 
    private config const logLevel = LogLevel.DEBUG;
    const smLogger = new Logger(logLevel);
    private var outMsg:string;

    /**
    * Set the neighbor and start_i arrays for the graph data structure.
    *
    * lsrc: int array of src vertices
    * lstart_i: int array of start vertex values based off src
    * lneighbor: int array of number of neighbors based off src
    *
    * returns: nothing
    */
    proc set_neighbor(lsrc: [?D1] int, lstart_i: [?D2] int, lneighbor: [?D3] int) { 
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
    proc bin_search_v(ary: [?D] int, l: int, h: int, key: int): int throws {
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
    proc vertex_remap(lsrc: [?D1] int, ldst: [?D2] int, num_v: int, node_mapper: [?D3] int, node_mapper_r: [?D4], ref rev_node_domain: domain): int throws {
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
    proc combine_sort(lsrc: [?D1] int, ldst: [?D2] int, le_weight: [?D3] real, 
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
    proc part_degree_sort(lsrc: [?D1] int, ldst: [?D2] int, lstart_i: [?D3] int, 
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
    proc degree_sort_u(lsrc: [?D1] int, ldst: [?D2] int, lstart_i: [?D3] int,
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
    * Print graph data structure server-side to visualize the raw array data.
    *
    * G: graph we want to print out. 
    *
    * returns: message back to Python.
    */
    proc print_graph_serverside(G: borrowed SegGraph) throws {
        for comp in Component {
            var curr_comp = comp:string;
            if G.hasComp(curr_comp) {
                select curr_comp {
                    when "RELATIONSHIPS", "NODE_LABELS" {
                        var X = toSymEntry(G.getComp(comp:string), list(string, parSafe=true)).a;
                        writeln(comp:string, " = ", X);
                    }
                    when "NODE_PROPS", "EDGE_PROPS" {
                        var X = toSymEntry(G.getComp(comp:string), list((string,string), parSafe=true)).a;
                        writeln(comp:string, " = ", X);
                    }
                    when "EDGE_WEIGHT", "EDGE_WEIGHT_R" {
                        var X = toSymEntry(G.getComp(comp:string), real).a;
                        writeln(comp:string, " = ", X);
                    }
                    when "NODE_MAP_R" {
                        var X = toSymEntryAD(G.getComp(comp:string)).a;
                        writeln(comp:string, " = ", X);
                    }
                    otherwise {
                        var X = toSymEntry(G.getComp(comp:string), int).a;
                        writeln(comp:string, " = ", X);
                    }
                }
            }
        }
    } // end of print_graph_serverside

    /**
    * Read the graph file and store edge information in double-index data structure. 
    *
    * returns: null.
    */
    proc readLinebyLine(src: [?D1] int, dst: [?D2] int, e_weight: [?D3] real, path: string, 
                        comments: string, weighted: bool) throws {
        coforall loc in Locales  {
            on loc {
                var f = open(path, ioMode.r);
                var r = f.reader(kind = ionative);
                var line:string;
                var a,b,c:string;
                var edge_count:int = 0;
                var srclocal = src.localSubdomain();
                var ewlocal = e_weight.localSubdomain();

                while r.readLine(line) {
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
                    if (!weighted) {
                        (a,b) = line.splitMsgToTuple(2);
                    } else {
                        (a,b,c) = line.splitMsgToTuple(3);
                    }

                    // Detect a self loop and write it to the server.
                    if ((a == b) && (debug_print == true)) {
                        smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                        "self loop " + a + "->" + b);
                    }

                    // Place the read edge into the current locale.
                    if (srclocal.contains(edge_count)) {
                        src[edge_count] = (a:int);
                        dst[edge_count] = (b:int);

                        if (weighted) {
                            e_weight[edge_count] = (c:real);
                        }
                    }

                    edge_count += 1;

                    // Do not to write on an out of bounds locale. 
                    if (edge_count > srclocal.highBound) {
                        break;
                    }
                } 
                if (edge_count <= srclocal.highBound) {
                    var myoutMsg = "The input file does not contain enough edges for locale " 
                                    + here.id:string + " current line = " + edge_count:string;
                    smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),myoutMsg);
                }
                r.close();
                f.close();
            }// end on loc
        }//end coforall
    }//end readLinebyLine

    /**
    * Write graph arrays to a file. 
    *
    * returns: null.
    */
    proc writeGraphArrays(G: borrowed SegGraph, filename: string) throws {
        // Create and open an output file with the specified filename in write mode.
        var outfile = open(filename, ioMode.cw);
        var writer = outfile.writer();

        for comp in Component {
            var curr_comp = comp:string;
            if G.hasComp(curr_comp) {
                select curr_comp {
                    when "RELATIONSHIPS", "NODE_LABELS" {
                        var X = toSymEntry(G.getComp(comp:string), list(string, parSafe=true)).a;
                        var n = X.size;
                        writer.writeln(n, " ", comp:string);
                        writer.writeln(X);
                    }
                    when "NODE_PROPS", "EDGE_PROPS" {
                        var X = toSymEntry(G.getComp(comp:string), list((string,string), parSafe=true)).a;
                        var n = X.size;
                        writer.writeln(n, " ", comp:string);
                        writer.writeln(X);
                    }
                    when "EDGE_WEIGHT", "EDGE_WEIGHT_R" {
                        var X = toSymEntry(G.getComp(comp:string), real).a;
                        var n = X.size;
                        writer.writeln(n, " ", comp:string);
                        writer.writeln(X);
                    }
                    when "NODE_MAP_R" {
                        var X = toSymEntryAD(G.getComp(comp:string)).a;
                        var n = X.size;
                        writer.writeln(n, " ", comp:string);
                        writer.writeln(X);
                    }
                    otherwise {
                        var X = toSymEntry(G.getComp(comp:string), int).a;
                        var n = X.size;
                        writer.writeln(n, " ", comp:string);
                        writer.writeln(X);
                    }
                }
            }
        }
        writer.close();
        outfile.close();
    }

    /**
    * Read graph arrays from a file. 
    *
    * returns: a SegGraph.
    */
    proc readGraphArrays(G: borrowed SegGraph, filename: string) throws {
        // Open an input file with the specified filename in read mode.
        var infile = open(filename, ioMode.r);
        var reader = infile.reader(kind = ionative);

        var count = 0;
        var arr_type:string;
        var line:string;
        while reader.readLine(line) {
            count += 1; 

            if (count % 2 != 0) {
                var line_split = line.split();
                arr_type = line_split[1];
                continue;
            } else {
                var X = line.split():int;
                G.withComp(new shared SymEntry(X):GenSymEntry, arr_type);

                if (arr_type == "SRC") {
                    G.n_edges = X.size;
                }
                if (arr_type == "NEIGHBOR") {
                    G.n_vertices = X.size;
                }
                if (arr_type == "SRC_R") {
                    G.directed = false;
                }
                if (arr_type == "EDGE_WEIGHT") {
                    G.directed = true;
                }
            }
        }
        reader.close();
        infile.close();
    }
}