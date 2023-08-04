module GraphInfoMsg {
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

    use CommandMap;
    registerFunction("edges", edgesMsg, getModuleName());
    registerFunction("nodes", nodesMsg, getModuleName());
    registerFunction("degree", degreeMsg, getModuleName());
}