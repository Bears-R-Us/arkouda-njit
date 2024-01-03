module BuildPropertyGraphMsg {
    // Chapel modules.
    use Reflection;
    use Time;
    use List;
    use Sort;
    use Map;
    use BlockDist;
    use BlockCycDist;
    use CommDiagnostics;
    
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
    use SegmentedString;
    use ArgSortMsg;
    use AryUtil;
    use Logging;
    use Message;
    use CommAggregation;
    
    // Server message logger. 
    private config const logLevel = LogLevel.DEBUG;
    const pgmLogger = new Logger(logLevel);
    var outMsg:string;

    /**
    * Adds node labels to the nodes of a property graph.
    *
    * :arg cmd: operation to perform. 
    * :type cmd: string
    * :arg msgArgs: arguments passed to backend. 
    * :type msgArgs: borrowed MessageArgs
    * :arg st: symbol table used for storage.
    * :type st: borrowed SymTab
    *
    * :returns: MsgTuple
    */
    proc addNodeLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Parse the message from Python.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var vertexIdsName = msgArgs.getValueOf("VertexIdsName");
        var columnNames = msgArgs.getValueOf("ColumnNames").split("+");
        var vertexLabelArrayNames = msgArgs.getValueOf("VertexLabelArrayNames").split("+");
        var labelMapperArrayNames = msgArgs.getValueOf("LabelMapperNames").split("+");

        // Map to keep track of symbol table id for the label array to the dataframe column and its
        // mapper, if applicable.
        var labelSymTabIdToColumnAndMapper = new map(string, (string, borrowed SegStringSymEntry));
        // NOTE: Map types cannot be generic, so SegStringSymEntry cannot be nil, therefore, we need
        //       a placeholder SegStringSymEntry for the labels that do not have a mapper.
        
        // Extract the vertices with labels to be inputted.
        var vertexIdsEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(vertexIdsName, st);
        var vertexIdsSym = toSymEntry(vertexIdsEntry, int);
        var vertexIds = vertexIdsSym.a;

        // Extract the graph we are operating with from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        // Extract the node_map array to get the domain for the nodes.
        var nodeMap = toSymEntry(graph.getComp("NODE_MAP"), int).a;
        var nodeDomain = nodeMap.domain;

        // Ensure vertexIds begin at 0 and end at n-1 and all values within are consecutive, if not
        // then values are added to a sparse domain based off the original node domain.
        var aligned:bool = isAligned(vertexIds);
        var consecutive:bool = isConsecutive(vertexIds);

        // Create sparse domain to hold data 
        var sparseDataDomain: sparse subdomain(nodeDomain);
        if !consecutive then 
            sparseDataDomain.bulkAddNoPreserveInds(vertexIds, dataSorted = true, isUnique = true);
        if !aligned && consecutive then 
            nodeDomain = blockDist.createDomain({vertexIds[vertexIds.domain.low]..vertexIds[vertexIds.domain.high]});

        // NOTE: Temporary restriction to utilizing sparse arrays. 
        if !consecutive {
            var errorMsg = notImplementedError(pn, "sparse attributes currently disallowed");
            pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }

        // Create the array of domains that will store the labels for our vertices.
        var timer:stopwatch;
        timer.start();
        var repMsg:string = insertArrays(columnNames, vertexLabelArrayNames, labelSymTabIdToColumnAndMapper, consecutive, sparseDataDomain, vertexIds, st, labelMapperArrayNames);
        timer.stop();

        // Add the component for the node labels for the graph.
        graph.withComp(new shared MapSymEntry(labelSymTabIdToColumnAndMapper):GenSymEntry, "VERTEX_LABELS");
        timer.stop();
        outMsg = "addNodeLabels took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addNodeLabelsMsg

    /**
    * Loads node attributes to the internal node representations of a property graph.
    *
    * :arg cmd: operation to perform. 
    * :type cmd: string
    * :arg msgArgs: arguments passed to backend. 
    * :type msgArgs: borrowed MessageArgs
    * :arg st: symbol table used for storage.
    * :type st: borrowed SymTab
    *
    * :returns: MsgTuple
    */
    proc loadNodeAttributesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Map to keep track of stored attributes. The string inside of the tuple is to denote the 
        // relationship that a specific property belongs to.
        var propertyNameToSymTabId = new map(string, (string, string));

        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var columnNames = msgArgs.getValueOf("ColumnNames").split("+");
        var columnIdNames = msgArgs.getValueOf("ColumnIdsName").split("+");
        var internalIndicesName = msgArgs.getValueOf("InternalIndicesName");

        // Extract the graph we are operating with from the symbol table.
        var gEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var edgeDomain = blockDist.createDomain(src.domain);
        var internalIndicesEntry = getGenericTypedArrayEntry(internalIndicesName, st);
        var internalIndices = toSymEntry(internalIndicesEntry, int).a;
        
        // Ensure internalIndices begin at 0 and end at n-1 and all values within are consecutive, if not
        // then values are added to a sparse domain based off the original edge domain.
        var aligned:bool = isAligned(internalIndices);
        var consecutive:bool = isConsecutive(internalIndices);

        // Create sparse domain to hold data 
        var sparseDataDomain: sparse subdomain(edgeDomain);
        if !consecutive then 
            sparseDataDomain.bulkAddNoPreserveInds(internalIndices, dataSorted = true, isUnique = true);
        if !aligned && consecutive then 
            edgeDomain = blockDist.createDomain({internalIndices[internalIndices.domain.low]..internalIndices[internalIndices.domain.high]});

        // NOTE: Temporary restriction to utilizing sparse arrays. 
        if !consecutive {
            var errorMsg = notImplementedError(pn, "sparse attributes currently disallowed");
            pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }

        // Create new arrays for inputted dataframe data incase the original dataframe ever ceases
        // to exist.
        var timer: stopwatch;
        timer.start();
        var repMsg:string = insertArrays(columnNames, columnIdNames, propertyNameToSymTabId, consecutive, sparseDataDomain, internalIndices, st);
        timer.stop();
        graph.withComp(new shared MapSymEntry(propertyNameToSymTabId):GenSymEntry, "VERTEX_PROPS");
        outMsg = "loadNodeProperties took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of loadNodeAttributesMsg

    /**
    * Adds edge relationships to the edges of a property graph.
    *
    * :arg cmd: operation to perform. 
    * :type cmd: string
    * :arg msgArgs: arguments passed to backend. 
    * :type msgArgs: borrowed MessageArgs
    * :arg st: symbol table used for storage.
    * :type st: borrowed SymTab
    *
    * :returns: MsgTuple
    */
    proc addEdgeRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Parse the message from Python.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var edgeIdsName = msgArgs.getValueOf("InternalEdgeIndicesName");
        var columnNames = msgArgs.getValueOf("ColumnNames").split("+");
        var edgeRelationshipArrayNames = msgArgs.getValueOf("EdgeRelationshipArrayNames").split("+");
        var relationshipMapperArrayNames = msgArgs.getValueOf("RelationshipMapperNames").split("+");

        // Map to keep track of symbol table id for the relationship array to the dataframe column 
        // and its mapper, if applicable.
        var relationshipSymTabIdToColumnAndMapper = new map(string, (string, borrowed SegStringSymEntry));
        // NOTE: Map types cannot be generic, so SegStringSymEntry cannot be nil, therefore, we need
        //       a placeholder SegStringSymEntry for the labels that do not have a mapper.
        
        // Extract the edges with relationships to be inputted.
        var edgeIdsEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(edgeIdsName, st);
        var edgeIdsSym = toSymEntry(edgeIdsEntry, int);
        var edgeIds = edgeIdsSym.a;

        // Extract the graph we are operating with from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        // Extract the src array to get the domain for the edges.
        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var edgeDomain = src.domain;

        // Ensure edgeIds begin at 0 and end at n-1 and all values within are consecutive, if not
        // then values are added to a sparse domain based off the original edge domain.
        var aligned:bool = isAligned(edgeIds);
        var consecutive:bool = isConsecutive(edgeIds);

        writeln("\n\n\n\n\n\n");
        writeln("aligned = ", aligned);
        writeln("consecutive = ", consecutive);
        writeln("edgeIds = ", edgeIds);
        writeln("\n\n\n\n\n\n");

        // Create sparse domain to hold data 
        var sparseDataDomain: sparse subdomain(edgeDomain);
        if !consecutive then 
            sparseDataDomain.bulkAddNoPreserveInds(edgeIds, dataSorted = true, isUnique = true);
        if !aligned && consecutive then 
            edgeDomain = blockDist.createDomain({edgeIds[edgeIds.domain.low]..edgeIds[edgeIds.domain.high]});

        // NOTE: Temporary restriction to utilizing sparse arrays. 
        if !consecutive {
            var errorMsg = notImplementedError(pn, "sparse attributes currently disallowed");
            pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }

        // Create the array of domains that will store the labels for our vertices.
        var timer:stopwatch;
        timer.start();
        var repMsg:string = insertArrays(columnNames, edgeRelationshipArrayNames, relationshipSymTabIdToColumnAndMapper, consecutive, sparseDataDomain, edgeIds, st, relationshipMapperArrayNames);
        timer.stop();

        // Add the component for the node labels for the graph.
        graph.withComp(new shared MapSymEntry(relationshipSymTabIdToColumnAndMapper):GenSymEntry, "EDGE_RELATIONSHIPS");
        timer.stop();
        outMsg = "addEdgeRelationships took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addEdgeRelationshipsMsg

    /**
    * Loads edge attributes to the internal edges of a property graph.
    *
    * :arg cmd: operation to perform. 
    * :type cmd: string
    * :arg msgArgs: arguments passed to backend. 
    * :type msgArgs: borrowed MessageArgs
    * :arg st: symbol table used for storage.
    * :type st: borrowed SymTab
    *
    * :returns: MsgTuple
    */
    proc loadEdgeAttributesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Map to keep track of stored attributes. The string inside of the tuple is to denote the 
        // relationship that a specific property belongs to.
        var propertyNameToSymTabId = new map(string, (string, string));

        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var columnNames = msgArgs.getValueOf("ColumnNames").split("+");
        var columnIdNames = msgArgs.getValueOf("ColumnIdsName").split("+");
        var internalIndicesName = msgArgs.getValueOf("InternalIndicesName");

        // Extract the graph we are operating with from the symbol table.
        var gEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var edgeDomain = blockDist.createDomain(src.domain);
        var internalIndicesEntry = getGenericTypedArrayEntry(internalIndicesName, st);
        var internalIndices = toSymEntry(internalIndicesEntry, int).a;
        
        // Ensure internalIndices begin at 0 and end at n-1 and all values within are consecutive, if not
        // then values are added to a sparse domain based off the original edge domain.
        var aligned:bool = isAligned(internalIndices);
        var consecutive:bool = isConsecutive(internalIndices);

        // Create sparse domain to hold data 
        var sparseDataDomain: sparse subdomain(edgeDomain);
        if !consecutive then 
            sparseDataDomain.bulkAddNoPreserveInds(internalIndices, dataSorted = true, isUnique = true);
        if !aligned && consecutive then 
            edgeDomain = blockDist.createDomain({internalIndices[internalIndices.domain.low]..internalIndices[internalIndices.domain.high]});

        // NOTE: Temporary restriction to utilizing sparse arrays. 
        if !consecutive {
            var errorMsg = notImplementedError(pn, "sparse attributes currently disallowed");
            pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }

        // Create new arrays for inputted dataframe data incase the original dataframe ever ceases
        // to exist.
        var timer: stopwatch;
        timer.start();
        var repMsg:string = insertArrays(columnNames, columnIdNames, propertyNameToSymTabId, consecutive, sparseDataDomain, internalIndices, st);
        timer.stop();
        graph.withComp(new shared MapSymEntry(propertyNameToSymTabId):GenSymEntry, "EDGE_PROPS");
        outMsg = "loadEdgeProperties took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of loadEdgeAttributesMsg

    use CommandMap;
    registerFunction("addNodeLabels", addNodeLabelsMsg, getModuleName());
    registerFunction("addEdgeRelationships", addEdgeRelationshipsMsg, getModuleName());
    registerFunction("loadNodeAttributes", loadNodeAttributesMsg, getModuleName());
    registerFunction("loadEdgeAttributes", loadEdgeAttributesMsg, getModuleName());
}