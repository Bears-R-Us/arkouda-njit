module BuildGraphMsg {
    // Chapel modules.
    use Reflection;
    use Set;
    use Time; 
    use Sort; 
    use List;
    use ReplicatedDist;

    // Package modules.
    use CopyAggregation;
    
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

        // Get the symbol table entries for the edge, weight, and node map arrays.
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
    * Read in a matrix market file to pdarrays to eventually build a graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc readMatrixMarketFileMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var pathS = msgArgs.getValueOf("Path");
        var directedS = msgArgs.getValueOf("Directed");

        // Converted parsed messages to the needed data types for Chapel operations.
        var path:string = (pathS:string);

        var directed:bool;
        directedS = directedS.toLower();
        directed = (directedS:bool);

        // Check to see if the file can be opened correctly. 
        try {
            var f = open(path, ioMode.r);
            f.close();
        } catch {
            smLogger.error(getModuleName(),getRoutineName(),getLineNumber(), "Error opening file.");
        }
    
        // Start parsing through the file.
        var f = open(path, ioMode.r);
        var r = f.reader(kind = ionative);
        var line:string;
        var a,b,c:string;

        // Prase through the matrix market file header to get number of rows, columns, and entries.
        while (r.readLine(line)) {
            if (line[0] == "%") {
                continue;
            }
            else {
                var temp = line.split();
                a = temp[0];
                b = temp[1];
                c = temp[2];
                break;
            }
        }
        var rows = a:int;
        var cols = b:int;
        var entries = c:int;

        // Make the src and dst arrays to build the graph out of, they will all be of size entries.
        var src = makeDistArray(entries, int);
        var dst = makeDistArray(entries, int);
        var wgt = makeDistArray(entries, real);
        
        // Read the next line to see if there are three columns, if so the graph is weighted.
        r.readLine(line);
        var temp = line.split();
        var weighted = false;
        var ind = 0;
        if temp.size != 3 {
            src[ind] = temp[0]:int;
            dst[ind] = temp[1]:int;
        } else {
            src[ind] = temp[0]:int;
            dst[ind] = temp[1]:int;
            wgt[ind] = temp[2]:real;
            weighted = true;
        }
        ind += 1;

        // Now, read the rest of the file. The reading will be carried out by the head locale, which
        // will typically be locale0. Therefore, we will create some aggregators for when locale0
        // has to write to remote data.
        var edge_agg = new DstAggregator(int);
        var wgt_agg = new DstAggregator(real);
        while (r.readLine(line)) {
            var temp = line.split();
            if !weighted {
                edge_agg.copy(src[ind], temp[0]:int);
                edge_agg.copy(dst[ind], temp[1]:int);

            } else {
                edge_agg.copy(src[ind], temp[0]:int);
                edge_agg.copy(dst[ind], temp[1]:int);
                wgt_agg.copy(wgt[ind], temp[2]:real);
            }
            ind += 1;
        }
        
        // Add the read arrays into the symbol table.
        var src_name = st.nextName();
        var src_entry = new shared SymEntry(src);
        st.addEntry(src_name, src_entry);

        var dst_name = st.nextName();
        var dst_entry = new shared SymEntry(dst);
        st.addEntry(dst_name, dst_entry);

        var wgt_name = st.nextName();
        var wgt_entry = new shared SymEntry(wgt);
        st.addEntry(wgt_name, wgt_entry);

        // Write the reply message back to Python. 
        var repMsg = "created " + st.attrib(src_name) + "+ created " + st.attrib(dst_name);
        if weighted {
            repMsg += "+ created " + st.attrib(wgt_name);
        } else {
            repMsg += "+ nil";
        }
        
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of readMatrixMarketFileMsg



    use CommandMap;
    registerFunction("addEdgesFrom", addEdgesFromMsg, getModuleName());
    registerFunction("readMatrixMarketFile", readMatrixMarketFileMsg, getModuleName());
}