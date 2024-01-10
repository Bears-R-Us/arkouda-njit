module TriangleCentralityMsg {
    // Chapel modules.
    use Reflection;
    use Time;

    // Arachne modules.
    use GraphArray;
    use TriangleCentrality;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use ServerErrors;
    use ServerErrorStrings;
    use AryUtil;
    use Logging;
    use Message;
    
    private config const logLevel = ServerConfig.logLevel;
    const tcmLogger = new Logger(logLevel);
  
    /**
    Parses message from Python and invokes the kernel to find the triangle centrality for a given
    graph.
    
    cmd: operation to perform. 
    msgArgs: arugments passed to backend. 
    SymTab: symbol table used for storage. 
    
    returns: message back to Python.
    */
    proc triangleCentralityMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        var graphEntryName = msgArgs.getValueOf("GraphName");
        var graphEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
        var graph = graphEntry.graph;

        var repMsg, outMsg: string;
        var triangleCentralities = makeDistArray(graph.n_vertices, real);

        var timer:stopwatch;
        if (!graph.isDirected()) {
            timer.start();
            minimum_search_triangle_centrality(graph, triangleCentralities);
            timer.stop();
            outMsg = "Shared memory minimum search triangle centrality took " + timer.elapsed():string + " sec";
        } else {
            var errorMsg = notImplementedError(pn, "DiGraph");
            tcmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }
        var triangleCentralitiesName = st.nextName();
        var triangleCentralitiesEntry = new shared SymEntry(triangleCentralities);
        st.addEntry(triangleCentralitiesName, triangleCentralitiesEntry);
        repMsg = 'created ' + st.attrib(triangleCentralitiesName);

        tcmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        tcmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }// end of triangleCentralityMsg

    use CommandMap;
    registerFunction("TriangleCentrality", triangleCentralityMsg, getModuleName());
}
