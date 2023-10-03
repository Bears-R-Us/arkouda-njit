module SquareCountMsg {
    // Chapel modules.
    use Reflection;
    use Time;

    // Arachne modules.
    use GraphArray;
    use SquareCount;

    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use ServerErrors;
    use ServerErrorStrings;
    use AryUtil;
    use Logging;
    use Message;

    // Server message logger. 
    private config const logLevel = ServerConfig.logLevel;
    private config const logChannel = ServerConfig.logChannel;
    const scLogger = new Logger(logLevel, logChannel);
    
    /**
    * Run square count on an undirected and graph. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc segSquareCountMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Info messages to print stuff to the Chapel Server.
        var repMsg:string;
        var outMsg:string;

        // Extract messages send from Python.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var degreeName = msgArgs.getValueOf("DegreeName");

        // Pull out our graph from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
        var g = gEntry.graph;

        // Pull out degree graph from the symbol table.
        var degree_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(degreeName, st);

        // Extract the data for use. 
        var degree_sym = toSymEntry(degree_entry,int);
        var degree = degree_sym.a;

        // Run the square counting.
        var timer:stopwatch;
        timer.start();
        var sc = square_count_sequential_kernel(g, degree);
        timer.stop();
        outMsg = "Sequential square counting took " + timer.elapsed():string + " sec";
        repMsg = sc:string;
        scLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        scLogger.info(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    
    use CommandMap;
    registerFunction("segmentedGraphSquares", segSquareCountMsg, getModuleName());
}