module TrussMsg {
    // Chapel modules.
    use Reflection;
    use Time;

    // Arachne modules.
    use GraphArray;
    use Truss;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use ServerErrors;
    use ServerErrorStrings;
    use AryUtil;
    use Logging;
    use Message;

    private config const logLevel = LogLevel.DEBUG;
    const tmLogger = new Logger(logLevel);
    var outMsg:string;
    

    /**
    Parses message from Python and invokes the kernel to find the truss measures for a given graph.
    
    cmd: operation to perform. 
    msgArgs: arugments passed to backend. 
    SymTab: symbol table used for storage. 
    
    returns: message back to Python.
    */
    proc trussMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        var graphEntryName = msgArgs.getValueOf("GraphName");
        var graphEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
        var graph = graphEntry.graph;

        var repMsg, outMsg: string;

        var timer:stopwatch;
        if (!graph.isDirected()) {
            when 

        } else {
            var errorMsg = notImplementedError(pn, "DiGraph");
            tcmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }
        
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of trussMsg

    use CommandMap;
    registerFunction("Truss", trussMsg);
}
