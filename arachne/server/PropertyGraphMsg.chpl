module PropertyGraphMsg {
    // Chapel modules.
    use Reflection;
    use Time; 
    use Sort;
    use Map;
    use BlockDist;
    use BlockCycDist;
    use CommDiagnostics;
    
    // Arachne Modules.
    use Utils; 
    use GraphArray;
    
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

    proc insertData(consecutive:bool, ref originalData, ref newData, ref internalIndices, type t) {
        if consecutive {
            forall (i,j) in zip(internalIndices, internalIndices.domain) 
                do newData[i] = originalData[j];
        } else {
            forall (i,j) in zip(internalIndices, internalIndices.domain) 
                with (var agg = new DstAggregator(t)) 
                do agg.copy(newData[i], originalData[j]);
        }
    }

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
        // Parse the message from Python.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var vertexIdsName = msgArgs.getValueOf("VertexIdsName");
        var vertexLabelsName = msgArgs.getValueOf("VertexLabelsName");
        var labelMapperName = msgArgs.getValueOf("LabelMapperName");
        
        // Extract the vertices with labels to be inputted.
        var vertexIdsEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(vertexIdsName, st);
        var vertexIdsSym = toSymEntry(vertexIdsEntry, int);
        var vertexIds = vertexIdsSym.a;

        // Extract the labels to be inputted for each of the vertices.
        var vertexLabelsEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(vertexLabelsName, st);
        var vertexLabelsSym = toSymEntry(vertexLabelsEntry, int);
        var vertexLabels = vertexLabelsSym.a;

        // Extract the label mapper to be sent to each locale.
        var labelMapper:SegString = getSegString(labelMapperName, st);

        // Extract the graph we are operating with from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        // Extract the node_map array to get the internal vertex values for our graph.
        var nodeMap = toSymEntry(graph.getComp("NODE_MAP"), int).a;

        // Create the array of domains that will store the labels for our vertices.
        var timer:stopwatch;
        timer.start();
        var labels = blockDist.createArray(nodeMap.domain, domain(int));
        forall (u,lbl) in zip(vertexIds,vertexLabels) do labels[u] += lbl;
        timer.stop();

        // Add the component for the node labels for the graph.
        graph.withComp(new shared SymEntry(labels):GenSymEntry, "VERTEX_LABELS");
        graph.withComp(new shared SegStringSymEntry(labelMapper.offsets, labelMapper.values, string):GenSymEntry, "VERTEX_LABELS_MAP");
        var repMsg = "labels added";
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
        graph.withComp(new shared SegStringSymEntry(relationshipMapper.offsets, relationshipMapper.values, string):GenSymEntry, "EDGE_RELATIONSHIPS_MAP"); 
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
        var propertyNameToSymTabId = new map((string,int), string); // map to keep track of stored properties
        proc addSparseArrayToSymbolTable(newData, columnName): string throws {
            var attrName = st.nextName();
            var attrEntry = new shared SymEntryAS(newData);
            st.addEntry(attrName, attrEntry);
            var repMsg = "created " + st.attrib(attrName) + "+ ";
            propertyNameToSymTabId.add((columnName, -1), attrName); // NOTE: -1 is the identifier for "belongs to all relationships."
            return repMsg;
        }

        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var columnNames = msgArgs.getValueOf("ColumnNames");
        var columnIdsName = msgArgs.getValueOf("ColumnIdsName");
        var internalIndicesName = msgArgs.getValueOf("InternalIndicesName");

        // Extract the graph we are operating with from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var edgeDomain = src.domain;
        var internalIndicesEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(internalIndicesName, st);
        var internalIndices = toSymEntry(internalIndicesEntry, int).a;
        
        // Ensure internalIndices begin at 0 and end at n-1 and all values within are consecutive, if not
        // then values are added to a sparse domain based off the original edge domain.
        var consecutive:bool = true;
        if src.size != internalIndices.size then consecutive = false;
        else {
            if internalIndices[0] != 0 then consecutive = false;
            else if internalIndices[internalIndices.domain.high] != src.domain.high 
                 then consecutive = false;
            else forall (v,d) in zip(internalIndices, internalIndices.domain) with (ref consecutive) 
                 do if v != d then consecutive = false;
        }
        var sparseDataDomain: sparse subdomain(edgeDomain);
        if !consecutive then sparseDataDomain.bulkAddNoPreserveInds(internalIndices, dataSorted = true, isUnique = true);

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
        var repMsg = "";
        var timer: stopwatch;
        timer.start();
        for i in 0..<columnIds.size {
            var columnName = columns[i];
            var dataArraySymbolTableIdentifier = columnIds[i];
            var dataArrayEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(dataArraySymbolTableIdentifier, st);
            var etype = dataArrayEntry.dtype;
            select etype {
                when (DType.Int64) {
                    if consecutive {
                        propertyNameToSymTabId.add((columnName, -1), dataArraySymbolTableIdentifier); // NOTE: -1 is the identifier for "belongs to all relationships."
                    } else {
                        var originalData = toSymEntry(dataArrayEntry, int).a;
                        var newData: [sparseDataDomain] int;
                        insertData(consecutive, originalData, newData, internalIndices, int);
                        repMsg += addSparseArrayToSymbolTable(newData, columnName);
                    }
                }
                when (DType.UInt64) {
                    if consecutive {
                        propertyNameToSymTabId.add((columnName, -1), dataArraySymbolTableIdentifier); // NOTE: -1 is the identifier for "belongs to all relationships."
                    } else {
                        var originalData = toSymEntry(dataArrayEntry, uint).a;
                        var newData: [sparseDataDomain] uint;
                        insertData(consecutive, originalData, newData, internalIndices, uint);
                        repMsg += addSparseArrayToSymbolTable(newData, columnName);
                    }
                }
                when (DType.Float64) {
                    if consecutive {
                        propertyNameToSymTabId.add((columnName, -1), dataArraySymbolTableIdentifier); // NOTE: -1 is the identifier for "belongs to all relationships."
                    } else {
                        var originalData = toSymEntry(dataArrayEntry, uint).a;
                        var newData: [sparseDataDomain] real;
                        insertData(consecutive, originalData, newData, internalIndices, real);
                        repMsg += addSparseArrayToSymbolTable(newData, columnName);
                    }
                }
                when (DType.Bool) {
                    if consecutive {
                        propertyNameToSymTabId.add((columnName, -1), dataArraySymbolTableIdentifier); // NOTE: -1 is the identifier for "belongs to all relationships."
                    } else {
                        var originalData = toSymEntry(dataArrayEntry, bool).a;
                        var newData: [sparseDataDomain] bool;
                        insertData(consecutive, originalData, newData, internalIndices, bool);
                        repMsg += addSparseArrayToSymbolTable(newData, columnName);
                    }
                }
                when (DType.Strings) {
                    if consecutive {
                        propertyNameToSymTabId.add((columnName, -1), dataArraySymbolTableIdentifier); // NOTE: -1 is the identifier for "belongs to all relationships."
                    } else {
                        // We extract the entries that represent strings in a SegStringSymEntry.
                        var dataArraySegStringSymEntry = toSegStringSymEntry(dataArrayEntry);
                        var offsetsEntry = dataArraySegStringSymEntry.offsetsEntry;
                        var bytesEntry = dataArraySegStringSymEntry.bytesEntry;

                        // We make deep copies of the offsets and bytes to ensure changes to the
                        // dataframe in Python are not reflected here.
                        var newOffsetsEntry = createSymEntry(offsetsEntry.a);
                        var newBytesEntry = createSymEntry(bytesEntry.a);
                        
                        // In this case, newData is different than for the other datatypes, its domain
                        // and values will actually be the same and store the indices explicilty. 
                        var newData: [sparseDataDomain] int;
                        forall (e,d) in zip(newData, newData.domain) do e = d;
                        var indicesEntry = new shared SymEntryAS(newData);

                        // Create new object that is a wrapper to the Arkouda SegStringSymEntry class.
                        var sparsePropertySegStringSymEntry = new shared SparsePropertySegStringSymEntry(   
                            newOffsetsEntry, 
                            newBytesEntry, 
                            indicesEntry,
                            string 
                        );
                        
                        // Add the new object to the symbol table so we can extract this data at another
                        // time. 
                        var attrName = st.nextName();
                        st.addEntry(attrName, sparsePropertySegStringSymEntry);
                        propertyNameToSymTabId.add((columnName, -1), attrName); // NOTE: -1 is the identifier for "belongs to all relationships."
                        repMsg += attrName;
                    }
                }
            }
        }
        timer.stop();
        graph.withComp(new shared MapSymEntry(propertyNameToSymTabId):GenSymEntry, "EDGE_PROPS_TO_SYM_TAB_ID");
        graph.withComp(new shared SegStringSymEntry(columns.offsets, columns.values, string):GenSymEntry, "EDGE_PROPS_COL_MAP");
        outMsg = "loadEdgeProperties took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        if repMsg.size == 0 then repMsg = "no arrays created";
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of loadEdgePropertiesMsg

    use CommandMap;
    registerFunction("loadEdgeAttributes", loadEdgeAttributesMsg, getModuleName());
    registerFunction("addNodeLabels", addNodeLabelsMsg, getModuleName());
    registerFunction("addEdgeRelationships", addEdgeRelationshipsMsg, getModuleName());
}