module BuildPropertyGraphMsg {
    // Chapel modules.
    use Reflection;
    use Time;
    use Sort;
    use Map;
    use BlockDist;
    
    // Arachne Modules.
    use Utils; 
    use GraphArray;
    use BuildPropertyGraph;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use NumPyDType;
    use ServerConfig;
    use ServerErrors;
    use ServerErrorStrings;
    use AryUtil;
    use Logging;
    use Message;
    
    // Server message logger. 
    private config const logLevel = LogLevel.DEBUG;
    const bpgmLogger = new Logger(logLevel);
    var outMsg:string;

    /**
    * Message parser that calls function to add labels to the vertices of a property graph.
    
    :arg cmd: operation to perform. 
    :type cmd: string
    :arg msgArgs: arguments passed to backend. 
    :type msgArgs: borrowed MessageArgs
    :arg st: symbol table used for storage.
    :type st: borrowed SymTab
    
    :returns: MsgTuple
    */
    proc addNodeLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Parse the message from Python.
        var graphName = msgArgs.getValueOf("GraphName");
        var inputIndicesName = msgArgs.getValueOf("InputIndicesName");
        var columnNames = msgArgs.getValueOf("ColumnNames").split("+");
        var labelArrayNames = msgArgs.getValueOf("LabelArrayNames").split("+");
        var labelMapperNames = msgArgs.getValueOf("LabelMapperNames").split("+");

        // Map to keep track of symbol table id for a label array to the dataframe column name and 
        // its mapper, if applicable.
        var vertexLabels = new map(string, (string, borrowed SegStringSymEntry));
        // NOTE: Map types cannot be generic, therefore, we need a placeholder SegStringSymEntry for 
        //       non-string labels.
        
        // Extract the indices (internal representation of vertices) with labels to be inputted.
        var inputIndicesEntry = getGenericTypedArrayEntry(inputIndicesName, st);
        var inputIndicesSym = toSymEntry(inputIndicesEntry, int);
        var inputIndices = inputIndicesSym.a;

        // Extract the graph we are inputting new data into.
        var graphEntry: borrowed GraphSymEntry = getGraphSymEntry(graphName, st); 
        var graph = graphEntry.graph;
        
        // Extract the vertex domain for the graph, the domain also represents the internal
        // representations of the vertices of the graph.
        var vertexMap = toSymEntry(graph.getComp("VERTEX_MAP"), int).a;
        var vertexDomain = vertexMap.domain;

        // Ensure input indices begin at 0 and end at n-1 and all values within are consecutive, 
        // if not then values are added to a sparse domain based off the original vertex domain.
        var aligned:bool = isAligned(inputIndices);
        var consecutive:bool = isConsecutive(inputIndices);

        // Create sparse domain from the original vertex domain to hold new data to be inputted.
        var sparseVertexDomain: sparse subdomain(vertexDomain);
        if !consecutive then 
            sparseVertexDomain.bulkAddNoPreserveInds(inputIndices, dataSorted=true, isUnique=true);
        if !aligned && consecutive then 
            vertexDomain = blockDist.createDomain(
                {inputIndices[inputIndices.domain.low]..inputIndices[inputIndices.domain.high]}
            ); // Block domains can be created as long as the range is consecutive.

        // NOTE: Temporary restriction to utilizing sparse arrays, for further information look at
        //       the NOTE in module `GraphArray` for class `SparseSymEntry`.
        if !consecutive {
            var errorMsg = notImplementedError(pn, "sparse attributes currently disallowed");
            bpgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }

        // Call helper method that handles attribute insertions regardless of the type of attribute
        // or of the datatype of each attribute.
        var timer:stopwatch;
        timer.start();
        var repMsg:string = insertAttributes(   columnNames, labelArrayNames, vertexLabels, 
                                                consecutive, sparseVertexDomain, inputIndices, st, 
                                                labelMapperNames
        );
        timer.stop();

        // Add the component for the vertex labels for the graph.
        graph.withComp(new shared MapSymEntry(vertexLabels):GenSymEntry, "VERTEX_LABELS");
        timer.stop();
        outMsg = "addNodeLabels took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        bpgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bpgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addNodeLabelsMsg

    /**
    Message parser that calls function to add properties to the vertices of a property graph.
    
    :arg cmd: operation to perform. 
    :type cmd: string
    :arg msgArgs: arguments passed to backend. 
    :type msgArgs: borrowed MessageArgs
    :arg st: symbol table used for storage.
    :type st: borrowed SymTab
    
    :returns: MsgTuple
    */
    proc addNodePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Parse the message from Python to extract needed data. 
        var graphName = msgArgs.getValueOf("GraphName");
        var inputIndicesName = msgArgs.getValueOf("InputIndicesName");
        var columnNames = msgArgs.getValueOf("ColumnNames").split("+");
        var propertyArrayNames = msgArgs.getValueOf("PropertyArrayNames").split("+");

        // Map to keep track of the symbol table id for a property array to the dataframe column
        // name and the label it belongs to, if applicable.
        var vertexProps = new map(string, (string, string));

        // Extract the indices (internal representation of vertices) with properties to be inputted.
        var inputIndicesEntry = getGenericTypedArrayEntry(inputIndicesName, st);
        var inputIndicesSym = toSymEntry(inputIndicesEntry, int);
        var inputIndices = inputIndicesSym.a;

        // Extract the graph we are inputting new data into.
        var graphEntry: borrowed GraphSymEntry = getGraphSymEntry(graphName, st); 
        var graph = graphEntry.graph;

        // Extract the vertex domain for the graph, the domain also represents the internal
        // representations of the vertices of the graph.
        var vertexMap = toSymEntry(graph.getComp("VERTEX_MAP"), int).a;
        var vertexDomain = vertexMap.domain;
        
        // Ensure input indices begin at 0 and end at n-1 and all values within are consecutive, 
        // if not then values are added to a sparse domain based off the original vertex domain.
        var aligned:bool = isAligned(inputIndices);
        var consecutive:bool = isConsecutive(inputIndices);

        // Create sparse domain from the original vertex domain to hold new data to be inputted.
        var sparseVertexDomain: sparse subdomain(vertexDomain);
        if !consecutive then 
            sparseVertexDomain.bulkAddNoPreserveInds(inputIndices, dataSorted=true, isUnique=true);
        if !aligned && consecutive then 
            vertexDomain = blockDist.createDomain(
                {inputIndices[inputIndices.domain.low]..inputIndices[inputIndices.domain.high]}
            ); // Block domains can be created as long as the range is consecutive.

        // NOTE: Temporary restriction to utilizing sparse arrays, for further information look at
        //       the NOTE in module `GraphArray` for class `SparseSymEntry`.
        if !consecutive {
            var errorMsg = notImplementedError(pn, "sparse attributes currently disallowed");
            bpgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }

        // Call helper method that handles attribute insertions regardless of the type of attribute
        // or of the datatype of each attribute.
        var timer:stopwatch;
        timer.start();
        var repMsg:string = insertAttributes(   columnNames, propertyArrayNames, vertexProps, 
                                                consecutive, sparseVertexDomain, inputIndices, st 
        );
        timer.stop();

        // Add the component for the vertex properties for the graph.
        graph.withComp(new shared MapSymEntry(vertexProps):GenSymEntry, "VERTEX_PROPS");
        timer.stop();
        outMsg = "addNodeProperties took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        bpgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bpgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addNodePropertiesMsg

    /**
    Message parser that calls function to add relationships to the edges of a property graph.
    
    :arg cmd: operation to perform. 
    :type cmd: string
    :arg msgArgs: arguments passed to backend. 
    :type msgArgs: borrowed MessageArgs
    :arg st: symbol table used for storage.
    :type st: borrowed SymTab
    
    :returns: MsgTuple
    */
    proc addEdgeRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Parse the message from Python.
        var graphName = msgArgs.getValueOf("GraphName");
        var inputIndicesName = msgArgs.getValueOf("InputIndicesName");
        var columnNames = msgArgs.getValueOf("ColumnNames").split("+");
        var relationshipArrayNames = msgArgs.getValueOf("RelationshipArrayNames").split("+");
        var relationshipMapperNames = msgArgs.getValueOf("RelationshipMapperNames").split("+");

        // Map to keep track of symbol table id for a relationship array to the dataframe column 
        // name and its mapper, if applicable.
        var edgeRelationships = new map(string, (string, borrowed SegStringSymEntry));
        // NOTE: Map types cannot be generic, therefore, we need a placeholder SegStringSymEntry for 
        //       non-string labels.
        
        // Extract the indices (internal representation of edges) with relationships to be inputted.
        var inputIndicesEntry = getGenericTypedArrayEntry(inputIndicesName, st);
        var inputIndicesSym = toSymEntry(inputIndicesEntry, int);
        var inputIndices = inputIndicesSym.a;

        // Extract the graph we are inputting new data into.
        var graphEntry: borrowed GraphSymEntry = getGraphSymEntry(graphName, st); 
        var graph = graphEntry.graph;
        
        // Extract the edge domain for the graph, the domain represents the internal index
        // representations of the edges of the graph.
        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var edgeDomain = src.domain;

        // Ensure input indices begin at 0 and end at n-1 and all values within are consecutive, 
        // if not then values are added to a sparse domain based off the original edge domain.
        var aligned:bool = isAligned(inputIndices);
        var consecutive:bool = isConsecutive(inputIndices);

        // Create sparse domain from the original edge domain to hold new data to be inputted.
        var sparseEdgeDomain: sparse subdomain(edgeDomain);
        if !consecutive then 
            sparseEdgeDomain.bulkAddNoPreserveInds(inputIndices, dataSorted=true, isUnique=true);
        if !aligned && consecutive then 
            edgeDomain = blockDist.createDomain(
                {inputIndices[inputIndices.domain.low]..inputIndices[inputIndices.domain.high]}
            ); // Block domains can be created as long as the range is consecutive.

        // NOTE: Temporary restriction to utilizing sparse arrays, for further information look at
        //       the NOTE in module `GraphArray` for class `SparseSymEntry`.
        if !consecutive {
            var errorMsg = notImplementedError(pn, "sparse attributes currently disallowed");
            bpgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }

        // Call helper method that handles attribute insertions regardless of the type of attribute
        // or of the datatype of each attribute.
        var timer:stopwatch;
        timer.start();
        var repMsg:string = insertAttributes(   columnNames, relationshipArrayNames, 
                                                edgeRelationships, consecutive, sparseEdgeDomain, 
                                                inputIndices, st, relationshipMapperNames
        );
        timer.stop();

        // Add the component for the edge relationships for the graph.
        graph.withComp(new shared MapSymEntry(edgeRelationships):GenSymEntry, "EDGE_RELATIONSHIPS");
        timer.stop();
        outMsg = "addEdgeRelationships took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        bpgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bpgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addEdgeRelationshipsMsg

    /**
    Message parser that calls function to add properties to the edges of a property graph.
    
    :arg cmd: operation to perform. 
    :type cmd: string
    :arg msgArgs: arguments passed to backend. 
    :type msgArgs: borrowed MessageArgs
    :arg st: symbol table used for storage.
    :type st: borrowed SymTab
    
    :returns: MsgTuple
    */
    proc addEdgePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Parse the message from Python to extract needed data. 
        var graphName = msgArgs.getValueOf("GraphName");
        var inputIndicesName = msgArgs.getValueOf("InputIndicesName");
        var columnNames = msgArgs.getValueOf("ColumnNames").split("+");
        var propertyArrayNames = msgArgs.getValueOf("PropertyArrayNames").split("+");

        // Map to keep track of the symbol table id for a property array to the dataframe column
        // name and the label it belongs to, if applicable.
        var edgeProps = new map(string, (string, string));

        // Extract the indices (internal representation of edges) with properties to be inputted.
        var inputIndicesEntry = getGenericTypedArrayEntry(inputIndicesName, st);
        var inputIndicesSym = toSymEntry(inputIndicesEntry, int);
        var inputIndices = inputIndicesSym.a;

        // Extract the graph we are inputting new data into.
        var graphEntry: borrowed GraphSymEntry = getGraphSymEntry(graphName, st); 
        var graph = graphEntry.graph;

        // Extract the edge domain for the graph, the domain represents the internal index
        // representations of the edges of the graph.
        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var edgeDomain = src.domain;

        // Ensure input indices begin at 0 and end at n-1 and all values within are consecutive, 
        // if not then values are added to a sparse domain based off the original edge domain.
        var aligned:bool = isAligned(inputIndices);
        var consecutive:bool = isConsecutive(inputIndices);

        // Create sparse domain from the original edge domain to hold new data to be inputted.
        var sparseEdgeDomain: sparse subdomain(edgeDomain);
        if !consecutive then 
            sparseEdgeDomain.bulkAddNoPreserveInds(inputIndices, dataSorted=true, isUnique=true);
        if !aligned && consecutive then 
            edgeDomain = blockDist.createDomain(
                {inputIndices[inputIndices.domain.low]..inputIndices[inputIndices.domain.high]}
            ); // Block domains can be created as long as the range is consecutive.

        // NOTE: Temporary restriction to utilizing sparse arrays, for further information look at
        //       the NOTE in module `GraphArray` for class `SparseSymEntry`.
        if !consecutive {
            var errorMsg = notImplementedError(pn, "sparse attributes currently disallowed");
            bpgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }

        // Call helper method that handles attribute insertions regardless of the type of attribute
        // or of the datatype of each attribute.
        var timer:stopwatch;
        timer.start();
        var repMsg:string = insertAttributes(   columnNames, propertyArrayNames, edgeProps, 
                                                consecutive, sparseEdgeDomain, inputIndices, st 
        );
        timer.stop();

        // Add the component for the edge properties for the graph.
        graph.withComp(new shared MapSymEntry(edgeProps):GenSymEntry, "EDGE_PROPS");
        timer.stop();
        outMsg = "addEdgeProperties took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        bpgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        bpgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addEdgePropertiesMsg

    use CommandMap;
    registerFunction("addNodeLabels", addNodeLabelsMsg, getModuleName());
    registerFunction("addEdgeRelationships", addEdgeRelationshipsMsg, getModuleName());
    registerFunction("addNodeProperties", addNodePropertiesMsg, getModuleName());
    registerFunction("addEdgeProperties", addEdgePropertiesMsg, getModuleName());
}