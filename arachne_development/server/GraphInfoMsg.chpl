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
        var attrEntrySrc = createSymEntry(src); 
        st.addEntry(attrNameSrc, attrEntrySrc);
        repMsg += "created " + st.attrib(attrNameSrc) + "+ ";

        var attrNameDst = st.nextName();
        var attrEntryDst = createSymEntry(dst); 
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
        var attrEntry = createSymEntry(nodes);
        st.addEntry(attrName, attrEntry);
        repMsg += "created " + st.attrib(attrName) + "+ ";

        timer.stop();
        outMsg = "Extracting nodes takes " + timer.elapsed():string;
        
        // Print out debug information to arkouda server output. 
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of nodesMsg

    use CommandMap;
    registerFunction("edges", edgesMsg, getModuleName());
    registerFunction("nodes", nodesMsg, getModuleName());
}
