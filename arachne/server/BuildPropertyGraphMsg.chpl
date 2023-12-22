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

        // Map to keep track of symbol table id for the the label array to the dataframe column 
        // and its mapper, if applicable.
        var labelSymTabIdToColumnAndMapper = new map(string, (string, borrowed SegStringSymEntry));
        
        // Extract the vertices with labels to be inputted.
        var vertexIdsEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(vertexIdsName, st);
        var vertexIdsSym = toSymEntry(vertexIdsEntry, int);
        var vertexIds = vertexIdsSym.a;

        // Extract the graph we are operating with from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        // Extract the node_map array to get the internal vertex values for our graph.
        var nodeMap = toSymEntry(graph.getComp("NODE_MAP"), int).a;
        var nodeDomain = nodeMap.domain;

        // Ensure vertexIds begin at 0 and end at n-1 and all values within are consecutive, if not
        // then values are added to a sparse domain based off the original edge domain.
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

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addNodeLabelsMsg

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
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var internalEdgeIndicesName = msgArgs.getValueOf("InternalEdgeIndicesName");
        var edgeRelationshipsName = msgArgs.getValueOf("EdgeRelationshipsName");
        var relationshipMapperName = msgArgs.getValueOf("RelationshipMapperName");
        
        // Extract the actual arrays for internal edge indices and relationships.
        var internalEdgeIndicesEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(internalEdgeIndicesName, st);
        var internalEdgeIndicesSym = toSymEntry(internalEdgeIndicesEntry, int);
        var internalEdgeIndices = internalEdgeIndicesSym.a;

        var edgeRelationshipsEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(edgeRelationshipsName, st);
        var edgeRelationshipsSym = toSymEntry(edgeRelationshipsEntry, int);
        var edgeRelationships = edgeRelationshipsSym.a;

        var relationshipMapper:SegString = getSegString(relationshipMapperName, st);

        // Get graph for usage and needed arrays.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var srcActual = toSymEntry(graph.getComp("SRC"), int).a;

        // Create array of lists to store relationships and populate it.
        var timer:stopwatch;
        timer.start();
        var relationships = blockDist.createArray(srcActual.domain, domain(int));
        forall (e,rel) in zip(internalEdgeIndices,edgeRelationships) do relationships[e] += rel;
        timer.stop();
        
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(relationships):GenSymEntry, "EDGE_RELATIONSHIPS");
        var repMsg = "edge relationships added";
        outMsg = "addEdgeRelationships took " + timer.elapsed():string + " sec";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
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
        var columnNames = msgArgs.getValueOf("ColumnNames");
        var columnIdsName = msgArgs.getValueOf("ColumnIdsName");
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

        // Extract property mappers from message, the first one contains column names in their
        // regular order, the second contains the internal mapping for the property names.
        var columns:SegString = getSegString(columnNames, st);
        var columnIds:SegString = getSegString(columnIdsName, st);

        // Create new arrays for inputted dataframe data incase the original dataframe ever ceases
        // to exist.
        var timer: stopwatch;
        timer.start();
        var repMsg:string = insertArrays(columns, columnIds, propertyNameToSymTabId, consecutive, sparseDataDomain, internalIndices, st);
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
    registerFunction("loadEdgeAttributes", loadEdgeAttributesMsg, getModuleName());
}