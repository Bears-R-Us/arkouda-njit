module BuildGraphMsg {
    // Chapel modules.
    use Reflection;
    use Set;
    use Time; 
    use Sort; 
    use List;

    // Package modules.
    use CopyAggregation;
    
    // Arachne Modules.
    use Utils;
    use GraphArray;
    use SegmentedString;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use NumPyDType;
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

    /** Helper function to insert a component.*/
    proc insertComponent(graph, etype, entry, key) throws {
        select etype {
            when DType.Int64 {
                var array = toSymEntry(entry, int).a;
                graph.withComp(createSymEntry(array):GenSymEntry, key);
            }
            when DType.UInt64 {
                var array = toSymEntry(entry, uint).a : int;
                graph.withComp(createSymEntry(array):GenSymEntry, key);
            }
        }
    }

    /**
    * Convert akarrays to a graph object. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc insertComponentsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        var timer:stopwatch;
        timer.start();

        var weighted = if msgArgs.contains("Weighted") 
                       then (msgArgs.getValueOf("Weighted").toLower()):bool else false;
        var directed = if msgArgs.contains("Directed")
                       then (msgArgs.getValueOf("Directed").toLower()):bool else false;
        var num_vertices = if msgArgs.contains("NumVertices") 
                           then (msgArgs.getValueOf("NumVertices")):int else 0;
        var num_edges = if msgArgs.contains("NumEdges")
                        then (msgArgs.getValueOf("NumEdges")):int else 0;
  
        var graph = if !msgArgs.contains("GraphName") 
                    then new shared SegGraph(num_vertices, num_edges, directed, weighted)
                    else getGraphSymEntry(msgArgs.getValueOf("GraphName"), st).graph;

        for key in msgArgs.keys() {
            if key == "EDGE_WEIGHT_SDI" || key == "EDGE_WEIGHT_RDI" then continue;
            var name = msgArgs.getValueOf(key);
            if !st.contains(name) then continue;
            try { getGenericTypedArrayEntry(name, st); }
            catch { continue; }
            var entry = getGenericTypedArrayEntry(name, st);
            var etype = entry.dtype;
            if key == "START_IDX_RDI" || key == "START_IDX_R_RDI" {
                var array = toSymEntry(entry, int).a;
                graph.withComp(createSymEntry(array):GenSymEntry, key);
                continue;
            }
            if !(etype == DType.Int64 || etype == DType.UInt64) {
                var errorMsg = notImplementedError(pn,key+" cannot be type "+dtype2str(etype));
                bgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
                return new MsgTuple(errorMsg, MsgType.ERROR);
            }
            select key {
                when "SRC_SDI" { 
                    insertComponent(graph, etype, entry, key);
                    generateRanges(graph, key, "RANGES_SDI", toSymEntry(graph.getComp("SRC_SDI"),int).a);
                }
                when "DST_SDI" { insertComponent(graph, etype, entry, key); }
                when "SEGMENTS_SDI" { insertComponent(graph, etype, entry, key); }
                when "SRC_R_SDI" { 
                    insertComponent(graph, etype, entry, key);
                    generateRanges(graph, key, "RANGES_R_SDI", toSymEntry(graph.getComp("SRC_R_SDI"),int).a);
                }
                when "DST_R_SDI" { insertComponent(graph, etype, entry, key); }
                when "SEGMENTS_R_SDI" { insertComponent(graph, etype, entry, key); }
                when "VERTEX_MAP_SDI" { insertComponent(graph, etype, entry, key); }
                when "SRC_RDI" { 
                    var array = toSymEntry(entry, int).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                    generateRanges(graph, key, "RANGES_RDI", toSymEntry(graph.getComp("SRC_RDI"),int).a);
                }
                when "DST_RDI" { 
                    var array = toSymEntry(entry, int).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                }
                when "SRC_R_RDI" { 
                    var array = toSymEntry(entry, int).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                    generateRanges(graph, key, "RANGES_R_RDI", toSymEntry(graph.getComp("SRC_R_RDI"),int).a);
                }
                when "DST_R_RDI" { 
                    var array = toSymEntry(entry, int).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                }
                when "NEIGHBOR_RDI" { 
                    var array = toSymEntry(entry, int).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                }
                when "NEIGHBOR_R_RDI" { 
                    var array = toSymEntry(entry, int).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                }
                when "VERTEX_MAP_RDI" { 
                    var array = toSymEntry(entry, int).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                }
            }
        }

        if graph.isWeighted() {
            var key = if msgArgs.contains("EDGE_WEIGHT_SDI") then "EDGE_WEIGHT_SDI" 
                      else "EDGE_WEIGHT_RDI";
            var name = msgArgs.getValueOf(key);
            var entry = getGenericTypedArrayEntry(name, st);
            var etype = entry.dtype;
            select etype {
                when DType.Int64 {
                    var array = toSymEntry(entry, int).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                }
                when DType.UInt64 {
                    var array = toSymEntry(entry, uint).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                }
                when DType.Float64 {
                    var array = toSymEntry(entry, real).a;
                    graph.withComp(createSymEntry(array):GenSymEntry, key);
                }
                otherwise {
                    var errorMsg = notImplementedError(pn,key+" cannot be type "+dtype2str(etype));
                    bgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
                    return new MsgTuple(errorMsg, MsgType.ERROR);
                }
            }
        }

        // Add graph to a specific symbol table entry.
        var graphEntryName = st.nextName();
        var graphSymEntry = new shared GraphSymEntry(graph);
        st.addEntry(graphEntryName, graphSymEntry);
        var repMsg = graphEntryName;
        outMsg = "Inserting components took " + timer.elapsed():string + " sec";
        timer.stop();
        
        // Print out debug information to arkouda server output. 
        bgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);

    }

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
        var commentHeader = msgArgs.getValueOf("CommentHeader");
        commentHeader = commentHeader.strip();

        // Converted parsed messages to the needed data types for Chapel operations.
        var path:string = (pathS:string);

        var directed:bool;
        directedS = directedS.toLower();
        directed = (directedS:bool);

        // Check to see if the file can be opened correctly. 
        try { var f = open(path, ioMode.r); f.close(); } 
        catch { bgmLogger.error(    getModuleName(),
                                    getRoutineName(),
                                    getLineNumber(), 
                                    "Error opening file."); }
    
        // Start parsing through the file.
        var f = open(path, ioMode.r);
        var r = f.reader(locking=false);
        var line:string;
        var a,b,c:string;

        // Parse through the matrix market file header to get number of rows, columns, and entries.
        while (r.readLine(line)) {
            if (line[0] == commentHeader) then continue;
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

        // Read the rest of the file.
        // TODO: Use these aggregators for distributed file reading.
        var src_agg = new DstAggregator(int);
        var dst_agg = new DstAggregator(int);
        var wgt_agg = new DstAggregator(real);
        while (r.readLine(line)) {
            var temp = line.split();
            if !weighted {
                src[ind] = temp[0]:int;
                dst[ind] = temp[1]:int;
            } else {
                src[ind] = temp[0]:int;
                dst[ind] = temp[1]:int;
                wgt[ind] = temp[2]:real;
            }
            ind += 1;
        }
        
        // Add the read arrays into the symbol table.
        var src_name = st.nextName();
        var src_entry = createSymEntry(src);
        st.addEntry(src_name, src_entry);

        var dst_name = st.nextName();
        var dst_entry = createSymEntry(dst);
        st.addEntry(dst_name, dst_entry);

        var wgt_name = st.nextName();
        var wgt_entry = createSymEntry(wgt);
        st.addEntry(wgt_name, wgt_entry);

        // Write the reply message back to Python. 
        var repMsg = "created " + st.attrib(src_name) + "+ created " + st.attrib(dst_name);
        if weighted then repMsg += "+ created " + st.attrib(wgt_name);
        else repMsg += "+ nil";
        
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of readMatrixMarketFileMsg

    /**
    * Read in a .tsv file to pdarrays to eventually build a graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc readTSVFileMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract needed data. 
        var pathS = msgArgs.getValueOf("Path");
        var directedS = msgArgs.getValueOf("Directed");
        var commentHeader = msgArgs.getValueOf("CommentHeader");
        commentHeader = commentHeader.strip();

        // Converted parsed messages to the needed data types for Chapel operations.
        var path:string = (pathS:string);

        var directed:bool;
        directedS = directedS.toLower();
        directed = (directedS:bool);

        // Check to see if the file can be opened correctly. 
        try { var f = open(path, ioMode.r); f.close(); } 
        catch { bgmLogger.error(    getModuleName(),
                                    getRoutineName(),
                                    getLineNumber(), 
                                    "Error opening file."); }
    
        // Start parsing through the file.
        var f = open(path, ioMode.r);
        var r = f.reader(locking=false);
        var line:string;
        var count:int = 0;

        // Read the rest of the file.
        // TODO: How can we make this optimized for disitributed graph loading?
        var srcList = new list(int);
        var dstList = new list(int);
        var wgtList = new list(real);
        while (r.readLine(line)) {
            var temp = line.split();
            for s in temp do s = s.strip();
            if !temp[0].startsWith(commentHeader) {
                if temp.size < 3 {
                    srcList.pushBack(temp[0]:int);
                    dstList.pushBack(temp[1]:int);
                } else {
                    srcList.pushBack(temp[0]:int);
                    dstList.pushBack(temp[1]:int);
                    wgtList.pushBack(temp[2]:real);
                }
                count += 1;
            } else {
                continue;
            }
        }
        var weighted:bool = if wgtList.size > 0 then true else false;

        var src = makeDistArray(count, int);
        var dst = makeDistArray(count, int);
        var wgt = makeDistArray(count, real);

        writeln("$$$$$ we get here 1");
        src = srcList;
        dst = dstList;
        if weighted then wgt = wgtList;
        writeln("$$$$$ we get here 2");
        
        // Add the read arrays into the symbol table.
        var src_name = st.nextName();
        var src_entry = createSymEntry(src);
        st.addEntry(src_name, src_entry);

        var dst_name = st.nextName();
        var dst_entry = createSymEntry(dst);
        st.addEntry(dst_name, dst_entry);

        var wgt_name = st.nextName();
        var wgt_entry = createSymEntry(wgt);
        st.addEntry(wgt_name, wgt_entry);

        // Write the reply message back to Python. 
        var repMsg = "created " + st.attrib(src_name) + "+ created " + st.attrib(dst_name);
        if weighted then repMsg += "+ created " + st.attrib(wgt_name);
        else repMsg += "+ nil";
        
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of readMatrixMarketFileMsg

    use CommandMap;
    registerFunction("insertComponents", insertComponentsMsg, getModuleName());
    registerFunction("readMatrixMarketFile", readMatrixMarketFileMsg, getModuleName());
    registerFunction("readTSVFile", readTSVFileMsg, getModuleName());
}