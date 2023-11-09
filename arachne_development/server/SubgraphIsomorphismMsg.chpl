module RSubgraphIsomorphismMsg {
    // Chapel modules.
    use Reflection;
    use Time;
    
    // Arachne modules.
    use GraphArray;
    use RSubgraphIsomorphism;
    
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
    * Run subgraph isomorphism with input graphs G and H, where we search for H inside of G. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc subgraphIsomorphismMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        
        // Info messages to print stuff to the Chapel Server.
        var repMsg:string;
        var outMsg:string;

        // Extract messages send from Python.
        var graphEntryName = msgArgs.getValueOf("MainGraphName");
        var subgraphEntryName = msgArgs.getValueOf("SubGraphName");
        var typeN = msgArgs.getValueOf("Type");
        var graphDegreeName = msgArgs.getValueOf("GraphDegreeName");
        var subGraphDegreeName = msgArgs.getValueOf("SubGraphDegreeName");
        var subGraphInternalVerticesSortedName = msgArgs.getValueOf("SubGraphInternalVerticesSortedName");

        writeln("$$$ graphEntryName = ", graphEntryName);
        writeln("$$$ subgraphEntryName = ", subgraphEntryName);
        writeln("$$$ typeN = ", typeN);
        writeln("$$$ subGraphDegreeName = ", subGraphDegreeName);
        writeln("$$$ subGraphInternalVerticesSortedName = ", subGraphInternalVerticesSortedName);

        var graph_degree_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(graphDegreeName, st);
        var graph_degree_sym = toSymEntry(graph_degree_entry, int);
        var graph_degree = graph_degree_sym.a;
        
        var subgraph_degree_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(subGraphDegreeName, st);
        var subgraph_degree_sym = toSymEntry(subgraph_degree_entry, int);
        var subgraph_degree = subgraph_degree_sym.a;

        var subgraph_internal_vertices_degree_sorted_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(subGraphInternalVerticesSortedName, st);
        var subgraph_internal_vertices_degree_sorted_sym = toSymEntry(subgraph_internal_vertices_degree_sorted_entry, int);
        var subgraph_internal_vertices_degree_sorted = subgraph_internal_vertices_degree_sorted_sym.a;

        writeln("$$$$$ subgraph_degree        = ", subgraph_degree);
        writeln("$$$$$ degree sorted subgraph = ", subgraph_internal_vertices_degree_sorted);
       
        // Pull out our graph from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var g = gEntry.graph;

        // Pull out our subgraph from the symbol table.
        var hEntry: borrowed GraphSymEntry = getGraphSymEntry(subgraphEntryName, st); 
        var h = hEntry.graph;

        var timer:stopwatch;
        timer.start();
        ullmannSubgraphIsomorphism11(g, h, subgraph_internal_vertices_degree_sorted, graph_degree);
        timer.stop();
        outMsg = "Subgraph Isomorphism took " + timer.elapsed():string + " sec";

        var subgraphs = makeDistArray(1, bool); // Temporary for now, should be "array of graphs".
        var subgraphsName = st.nextName();
        var subgraphsEntry = new shared SymEntry(subgraphs);
        st.addEntry(subgraphsName, subgraphsEntry);

        repMsg = 'created ' + st.attrib(subgraphsName);
        siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of subgraphIsomorphismMsg

    use CommandMap;
    registerFunction("RsubgraphIsomorphism", subgraphIsomorphismMsg, getModuleName());
} // end of module
