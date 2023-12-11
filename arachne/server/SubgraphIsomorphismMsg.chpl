module SubgraphIsomorphismMsg {
    // Chapel modules.
    use Reflection;
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
    use SegStringSort;
    use SegmentedString;
    
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

        writeln("$$$$$ graph_degree        = ", graph_degree);
        writeln("$$$$$ subgraph_degree        = ", subgraph_degree);
        writeln("$$$$$ degree sorted subgraph = ", subgraph_internal_vertices_degree_sorted);
       
        // Pull out our graph from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var g = gEntry.graph;

        
        // Pull out our subgraph from the symbol table.
        var hEntry: borrowed GraphSymEntry = getGraphSymEntry(subgraphEntryName, st); 
        var h = hEntry.graph;

        var timer:stopwatch;
        /*
        instead of passing symbol table just extract 
        label_mapper and relationship_mapper in SubgraphIsomorphismMsg.chpl 
        for both G and H. 
        Then create array(s) 
        var label_mapper_G: [0..<label_mapper.size] string; and 
        then populate it with a loop like 
        for i in 0..<label_mapper.size do mapper[i] = label_mapper[i] . 
        And pass 
        label_mapper_G, label_mapper_H, relationship_mapper_G, relationship_mapper_H 
        instead of the symbol table. (edited) 
        */ 

        // Lets extract main graph and subgraph node's labels 
        //Main graph Node Labels
        var nodeLabels_g = toSymEntry(g.getComp("VERTEX_LABELS"), domain(int)).a;
        const ref label_mapper_g_entry = toSegStringSymEntry(g.getComp("VERTEX_LABELS_MAP"));
        var label_mapper_g = assembleSegStringFromParts(label_mapper_g_entry.offsetsEntry, label_mapper_g_entry.bytesEntry, st);
        var Orig_Label_Mapper_G_to_Pass: [0..<label_mapper_g.size] string;

        for i in 0..<label_mapper_g.size {
            Orig_Label_Mapper_G_to_Pass[i] = label_mapper_g[i];          
        } 
        //Subgraph Node Labels
        var nodeLabels_h = toSymEntry(h.getComp("VERTEX_LABELS"), domain(int)).a;
        const ref label_mapper_h_entry = toSegStringSymEntry(h.getComp("VERTEX_LABELS_MAP"));
        var label_mapper_h = assembleSegStringFromParts(label_mapper_h_entry.offsetsEntry, label_mapper_h_entry.bytesEntry, st);
        var Orig_Label_Mapper_H_to_Pass: [0..<label_mapper_h.size] string;
        //map it to pass
        for i in 0..<label_mapper_h.size {
            Orig_Label_Mapper_H_to_Pass[i] = label_mapper_h[i];          
        } 

        // Lets extract main graph and subgraph Edges' labels or as we called them relationships! 
        //Main graph Relationships aka Edge' Label
        var edgeRelationships_g = toSymEntry(g.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        const ref relationship_mapper_g_entry = toSegStringSymEntry(g.getComp("EDGE_RELATIONSHIPS_MAP"));
        var relationship_mapper_g = assembleSegStringFromParts(relationship_mapper_g_entry.offsetsEntry, relationship_mapper_g_entry.bytesEntry, st);                      
        var Orig_Relationships_Mapper_G_to_Pass: [0..<relationship_mapper_g.size] string;

        //map it to pass
        for i in 0..<relationship_mapper_g.size {
            Orig_Relationships_Mapper_G_to_Pass[i] = relationship_mapper_g[i];          
        } 
        //Subgraph Relationships aka Edge' Label
        var edgeRelationships_h = toSymEntry(h.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        const ref relationship_mapper_h_entry = toSegStringSymEntry(h.getComp("EDGE_RELATIONSHIPS_MAP"));
        var relationship_mapper_h = assembleSegStringFromParts(relationship_mapper_h_entry.offsetsEntry, relationship_mapper_h_entry.bytesEntry, st);                      
        var Orig_Relationships_Mapper_H_to_Pass: [0..<relationship_mapper_h.size] string;

        //map it to pass
        for i in 0..<relationship_mapper_h.size {
            Orig_Relationships_Mapper_H_to_Pass[i] = relationship_mapper_h[i];          
        } 
        
        // Create empty depth array to return at the end of execution. Initialized here to ensure 
        // the function makes changes to an array reference and does not return a new array at
        // the end of execution.         

        timer.start();

        //ullmannSubgraphIsomorphism11(g, h, subgraph_internal_vertices_degree_sorted, graph_degree);
        var (isopassd, numberOfIsos) = runUllmann(g, h, subgraph_degree, graph_degree,
                                        Orig_Label_Mapper_G_to_Pass, Orig_Label_Mapper_H_to_Pass, 
                                        Orig_Relationships_Mapper_G_to_Pass, Orig_Relationships_Mapper_H_to_Pass);

        timer.stop();
        outMsg = "Subgraph Isomorphism took " + timer.elapsed():string + " sec";
        writeln(outMsg);
        
        var IsoDistArray = makeDistArray(isopassd.size, int);
        IsoDistArray = isopassd;

        writeln("IsoDistArray = ",IsoDistArray);
        //var subgraphs = makeDistArray(1, bool); // Temporary for now, should be "array of graphs".
        var IsoDistArrayName = st.nextName();
        var IsoDistArrayEntry = new shared SymEntry(IsoDistArray);
        st.addEntry(IsoDistArrayName, IsoDistArrayEntry);

        repMsg = 'created ' + st.attrib(IsoDistArrayName);
        siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of subgraphIsomorphismMsg

    use CommandMap;
    registerFunction("subgraphIsomorphism", subgraphIsomorphismMsg, getModuleName());
} // end of module