module BenchmarkMsg {
    // Chapel modules.
    use Reflection;
    use Time;
    use CommDiagnostics;

    // Arachne modules.
    use GraphArray;
    use BreadthFirstSearch;
    use BreadthFirstSearchMsg;
    use Utils;

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
    const bmLogger = new Logger(logLevel, logChannel);

    /* Add timing array to symbol table. */
    private proc return_timings(timings: [?D] real, st: borrowed SymTab): string throws{
        var timingsName = st.nextName();
        var timingsEntry = new shared SymEntry(timings);
        st.addEntry(timingsName, timingsEntry);

        var timingsMsg = 'created ' + st.attrib(timingsName);
        return timingsMsg;
    }

    /* Benchmarker for breadth-first search. */
    proc segBFSBenchmarker(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        
        // Info messages to print stuff to the Chapel Server.
        var repMsg:string;
        var outMsg:string;

        // Extract messages send from Python.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var sourceVerticesName = msgArgs.getValueOf("SourceVerticesName");
        var checkComms = (msgArgs.getValueOf("CheckComms").toLower()):bool;
       
        // Pull out our graph from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var g = gEntry.graph;

        // Pull out source vertices to run one-by-one.
        var sourceVerticesEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(sourceVerticesName, st);
        var sourceVertices = toSymEntry(sourceVerticesEntry, int).a;

        // Convert root value to inner mapping.
        var node_map = toSymEntry(g.getComp("VERTEX_MAP_SDI"),int).a;

        // Create empty depth array to return at the end of execution. Initialized here to ensure 
        // the function makes changes to an array reference and does not return a new array at
        // the end of execution.
        var depthName:string;
        var depth = makeDistArray(g.n_vertices, int);
        depth = -1;

        // Run the breadth-first search steps dependent on the number of locales.
        var trials_array = makeDistArray(sourceVertices.size, real);
        if checkComms then startCommDiagnostics();
        if(numLocales == 1) {
            var timer:stopwatch;
            for (i,u) in zip(sourceVertices.domain, sourceVertices) {
                timer.start();
                bfs_kernel_und_smem(g, u, depth);
                timer.stop();
                depth = -1;
                trials_array[i] = timer.elapsed();
            }
            var avg_time = (+ reduce trials_array) / trials_array.size;
            outMsg = "Shared memory breadth-first search took " + avg_time:string + " sec";
        }
        else {
            var timer:stopwatch;
            for (i,u) in zip(sourceVertices.domain, sourceVertices) {
                timer.start();
                bfs_kernel_und_dmem_opt(g, u, depth);
                timer.stop();
                depth = -1;
                trials_array[i] = timer.elapsed();
            }
            var avg_time = (+ reduce trials_array) / trials_array.size;
            outMsg = "Distributed memory breadth-first search took " + avg_time:string + " sec";
        }
        if checkComms {
            stopCommDiagnostics();
            var comms = getCommDiagnostics();
            writeln("\n\n\n\n\n");
            for c in comms {
                writeln(c);
            }
            writeln("\n\n\n\n\n");
            resetCommDiagnostics();
        }
        repMsg = return_timings(trials_array, st);
        bmLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bmLogger.info(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    use CommandMap;
    registerFunction("segmentedGraphBFSBenchmark", segBFSBenchmarker, getModuleName());
}