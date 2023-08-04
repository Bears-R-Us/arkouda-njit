module BreadthFirstSearchMsg {
    // Chapel modules.
    use Reflection;
    use Time;
    
    // Arachne modules.
    use GraphArray;
    use Utils;
    use Aggregators;
    use BreadthFirstSearch;
    
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
    const bfsLogger = new Logger(logLevel, logChannel);

    /**
    * Adds the depth array to the symbol table.
    *
    * returns: message to create pdarray at the front-end.
    */
    private proc return_depth(depth: [?D] int, st: borrowed SymTab): string throws{
        var depthName = st.nextName();
        var depthEntry = new shared SymEntry(depth);
        st.addEntry(depthName, depthEntry);

        var depMsg = 'created ' + st.attrib(depthName);
        return depMsg;
    }

    /**
    * Run BFS on a(n) (un)directed and (un)weighted graph. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc segBFSMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        
        // Info messages to print stuff to the Chapel Server.
        var repMsg:string;
        var outMsg:string;

        // Extract messages send from Python.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var rootN = msgArgs.getValueOf("Source");

        // Convert messages to datatypes.
        var root = rootN:int;
       
        // Pull out our graph from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var g = gEntry.graph; 

        // Create empty depth array to return at the end of execution. Initialized here to ensure 
        // the function makes changes to an array reference and does not return a new array at
        // the end of execution.
        var depthName:string;
        var depth = makeDistArray(g.n_vertices, int);
        depth = -1;

        // Run the breacth-first search steps dependent on the hardware. 
        var timer:stopwatch;
        if(!g.directed || g.directed) {
            if(numLocales == 1) {
                var timer:stopwatch;
                timer.start();
                bfs_kernel_und_smem(g, root, depth);
                timer.stop();
                outMsg = "Shared memory breadth-first search took " + timer.elapsed():string + " sec";
            }
            else {
                var timer:stopwatch;
                timer.start();
                bfs_kernel_und_dmem(g, root, depth);
                timer.stop();
                outMsg = "Distributed memory breadth-first search took " + timer.elapsed():string + " sec";
            }
        } else {
            var errorMsg = notImplementedError(pn, "property graph");
            bfsLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }
        repMsg = return_depth(depth, st);
        bfsLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bfsLogger.info(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    use CommandMap;
    registerFunction("segmentedGraphBFS", segBFSMsg, getModuleName());
}