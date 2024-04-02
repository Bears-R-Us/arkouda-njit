module SubgraphIsomorphismMsg {
    // Chapel modules.
    use Reflection;
    use Map;
    use Time;
    
    // Arachne modules.
    use GraphArray;
    use SubgraphIsomorphism; 
    
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
    const siLogger = new Logger(logLevel, logChannel);

    /**
    Parses message from Python and invokes the kernel to find subgraphs from G that are isomorphic
    to H.
    
    :arg cmd: operation to perform. 
    :type cmd: string
    :arg msgArgs: arguments passed to backend. 
    :type msgArgs: borrowed MessageArgs
    :arg st: symbol table used for storage.
    :type st: borrowed SymTab
    
    :returns: MsgTuple
    */
    proc subgraphIsomorphismMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        var repMsg, outMsg:string;

        // Extract messages sent from Python.
        var graphEntryName = msgArgs.getValueOf("MainGraphName");
        var subgraphEntryName = msgArgs.getValueOf("SubGraphName");
        var semanticCheck = msgArgs.getValueOf("SemanticCheck"):bool;
       
        // Pull out our graph from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var g = gEntry.graph;

        // Pull out our subgraph from the symbol table.
        var hEntry: borrowed GraphSymEntry = getGraphSymEntry(subgraphEntryName, st); 
        var h = hEntry.graph;

        // Execute sequential VF2 subgraph isomorphism.
        var timer:stopwatch;
        if g.isDirected() {
            timer.start();
            var isoArray = runVF2(g,h,semanticCheck,st);
            timer.stop();
            outMsg = "Sequential subgraph isomorphism took " + timer.elapsed():string + " sec";
            
            var isoDistArray = makeDistArray(isoArray.size, int);
            isoDistArray = isoArray;
            var IsoDistArrayName = st.nextName();
            var IsoDistArrayEntry = createSymEntry(isoDistArray);
            st.addEntry(IsoDistArrayName, IsoDistArrayEntry);
            repMsg = 'created ' + st.attrib(IsoDistArrayName);

            siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
            return new MsgTuple(repMsg, MsgType.NORMAL);
        } else {
            var errorMsg = notImplementedError(pn, "subgraph isomorphism for undirected graphs");
            siLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }
    } // end of subgraphIsomorphismMsg

    use CommandMap;
    registerFunction("subgraphIsomorphism", subgraphIsomorphismMsg, getModuleName());
} // end of module