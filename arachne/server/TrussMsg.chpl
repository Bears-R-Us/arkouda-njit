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

        var trussAlgortihm = msgArgs.getValueOf("TrussAlgorithm"):int;
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var graphEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
        var graph = graphEntry.graph;

        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var repMsg, outMsg : string = "empty";
        var k:int; 

        if msgArgs.contains("K") then k = msgArgs.getValueOf("K"):int;

        var containedEdges = makeDistArray(src.size, bool);

        var timer:stopwatch;
        if (!graph.isDirected()) {
            select trussAlgortihm {
                when 0 {
                    timer.start();
                    k_truss(graph, k, containedEdges);
                    timer.stop();
                    outMsg = "Shared memory k truss took " + timer.elapsed():string + " sec";
                }
                when 1 {
                    timer.start();
                    truss_decomposition(graph, containedEdges);
                    timer.stop();
                    outMsg = "Shared memory truss decomposition took " + timer.elapsed():string + " sec";
                }
                when 2 {
                    timer.start();
                    max_truss(graph, containedEdges);
                    timer.stop();
                    outMsg = "Shared memory max truss took " + timer.elapsed():string + " sec";
                }
            }

        } else {
            var errorMsg = notImplementedError(pn, "DiGraph");
            tmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }
        
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of trussMsg

    use CommandMap;
    registerFunction("Truss", trussMsg);
}
