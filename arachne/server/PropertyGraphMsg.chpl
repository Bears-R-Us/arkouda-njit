module DipSLLPropertyGraphMsg {
    // Chapel modules.
    use Reflection;
    use Time; 
    use Sort;
    use Map;
    use BlockDist;
    use CommDiagnostics;
    
    // Arachne Modules.
    use Utils; 
    use GraphArray;
    use SymEntry2D;
    
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
    
    // Server message logger. 
    private config const logLevel = LogLevel.DEBUG;
    const pgmLogger = new Logger(logLevel);
    var outMsg:string;

    /* Wrapper concrete class for generic class. */
    class GenProperty {
        var dataType: int;
    }

    /* Wrapped generic class to hold arrays of variable size and type. */
    class Property: GenProperty {
        type etype;
        var propertyIdentifier: domain(int);
        var propertyValue: [propertyIdentifier] etype;
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
        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var arrays = msgArgs.getValueOf("Arrays");

        // Extract the names of the arrays storing the vertices and their labels.
        var arrays_list = arrays.split();
        var input_vertices_name = arrays_list[0];
        var input_labels_name = arrays_list[1];
        var label_mapper_name = arrays_list[2];
        
        // Extract the vertices containing labels to be inputted.
        var input_vertices_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(input_vertices_name, st);
        var input_vertices_sym = toSymEntry(input_vertices_entry, int);
        var input_vertices = input_vertices_sym.a;

        // Extract the labels to be inputted for each of the vertices.
        var input_labels_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(input_labels_name, st);
        var input_labels_sym = toSymEntry(input_labels_entry, int);
        var input_labels = input_labels_sym.a;

        // Extract the label mapper to be sent to each locale.
        var label_mapper:SegString = getSegString(label_mapper_name, st);

        // Extract the graph we are operating with from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        
        // Extract the node_map array to get the internal vertex values for our graph.
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;

        // Create the array of domains that will store the labels for our vertices.
        var vertex_labels: [node_map.domain] domain(int);

        var timer:stopwatch;
        timer.start();
        forall i in input_vertices.domain { // for each input vertex, update its label list. 
            var lbl = input_labels[i]; // local
            var u = input_vertices[i]; // local
            vertex_labels[u] += lbl; // remote
        }
        timer.stop();

        // Add the component for the node labels for the graph.
        graph.withComp(new shared SymEntry(vertex_labels):GenSymEntry, "VERTEX_LABELS");
        graph.withComp(new shared SegStringSymEntry(label_mapper.offsets, label_mapper.values, string):GenSymEntry, "VERTEX_LABELS_MAP");
        var repMsg = "labels added";
        outMsg = "DipSLLaddNodeLabels took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addNodeLabelsMsg

    /**
    * Adds node properties to the nodes of a property graph.
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
    proc addNodePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();

        // Parse the message from Python to extract needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var vertexIdsName = msgArgs.getValueOf("VertexIdsName");
        var propertyMapperName = msgArgs.getValueOf("PropertyMapperName");
        var dataArrayNames = msgArgs.getValueOf("DataArrayNames");

        // Extract the graph we are operating with from the symbol table.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var node_map = toSymEntry(graph.getComp("NODE_MAP"), int).a;

        // Extract the vertices containing labels to be inputted.
        var inputVerticesEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(vertexIdsName, st);
        var inputVerticesSym = toSymEntry(inputVerticesEntry, int);
        var inputVertices = inputVerticesSym.a;

        // Extract property mappers from message, the first one contains column names in their
        // regular order, the second contains the internal mapping for the property names.
        var columns:SegString = getSegString(propertyMapperName, st);

        // Create map of column name to its datatype.
        var col2dtype = new map(string, string);

        // Extract the data array names and the data types for those arrays.
        var dataArrays = getSegString(dataArrayNames, st);
        var dataTypeSet: domain(string);
        for i in 0..<dataArrays.size {
            var dataType = dtype2str(getGenericTypedArrayEntry(dataArrays[i], st).dtype);
            col2dtype.add(columns[i], dataType);
            select dataType {
                when "uint8" {
                    var errorMsg = notImplementedError(pn, dataType);
                    pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
                    return new MsgTuple(errorMsg, MsgType.ERROR);
                }
                when "bigint" {
                    var errorMsg = notImplementedError(pn, dataType);
                    pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
                    return new MsgTuple(errorMsg, MsgType.ERROR);
                }
                when "UNDEF" {
                    var errorMsg = notImplementedError(pn, dataType);
                    pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
                    return new MsgTuple(errorMsg, MsgType.ERROR);
                }
            }
            dataTypeSet += dataType;
        }

        // Create a mapping for the string names of the data types to their integer identifier.
        var dataTypeMapStrToInt: [dataTypeSet] int;
        var ind = 0;
        for val in dataTypeMapStrToInt { val = ind; ind += 1; } 

        // Create a mapping for the interger identifier values to their string representation.
        var dataTypeMapIntToStr: [0..<ind] string;
        for (key,val) in zip(dataTypeMapStrToInt.domain,dataTypeMapStrToInt) do dataTypeMapIntToStr[val] = key;

        var timer:stopwatch;
        timer.start();
        /** Create block distributed two-dimensional array where the row indices correspond to the vertex
        * being stored and the column indices to the datatype being stored. Each element of the array 
        * is to store an object of class Property that contains an associative array where the domain
        * is an integer identifier for the name of the property (column) being stored and the element 
        * is the value for that vertex in that column. */
        var vertex_props = blockDist.createArray({0..<node_map.size, 0..<dataTypeSet.size}, shared GenProperty?);
        forall (v,d) in vertex_props.domain {
            var datatype:string = dataTypeMapIntToStr[d];
            select datatype {
                when "int64", "int" {
                    var newDom: domain(int);
                    var newArr: [newDom] int;
                    vertex_props[v,d] = new shared Property(d, int, newDom, newArr);
                }
                when "uint64", "uint" {
                    var newDom: domain(int);
                    var newArr: [newDom] uint;
                    vertex_props[v,d] = new shared Property(d, uint, newDom, newArr);
                }
                when "float64" {
                    var newDom: domain(int);
                    var newArr: [newDom] real;
                    vertex_props[v,d] = new shared Property(d, real, newDom, newArr);
                }
                when "bool" {
                    var newDom: domain(int);
                    var newArr: [newDom] bool;
                    vertex_props[v,d] = new shared Property(d, bool, newDom, newArr);
                }
                when "str" {
                    var newDom: domain(int);
                    var newArr: [newDom] string;
                    vertex_props[v,d] = new shared Property(d, string, newDom, newArr);
                }
            }
        }

        /** Sequentially process each data array, where each array itself is picked apart in
        * parallel and its values are stored in the appropriate locations of vertex_props. Due to 
        * Chapel being a statically-typed language, processing each datatype must be done 
        * separately. */
        for i in 0..<dataArrays.size {
            var dataArrayEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(dataArrays[i], st);
            var etype = dataArrayEntry.dtype;
            var etypeStr = dtype2str(etype);
            select etype {
                when (DType.Int64) {
                    var dataArraySym = toSymEntry(dataArrayEntry, int);
                    var dataArray = dataArraySym.a;
                    var etypeInd = dataTypeMapStrToInt[etypeStr];
                    forall (v,j) in zip(inputVertices,inputVertices.domain) {
                        var currentProperty = (vertex_props[v,etypeInd].borrow():(borrowed Property(int)));
                        currentProperty!.dataType = etypeInd;
                        currentProperty!.propertyIdentifier += i;
                        currentProperty!.propertyValue[i] = dataArray[j];
                    }
                }
                when (DType.UInt64) {
                    var dataArraySym = toSymEntry(dataArrayEntry, uint);
                    var dataArray = dataArraySym.a;
                    var etypeInd = dataTypeMapStrToInt[etypeStr];
                    forall (v,j) in zip(inputVertices,inputVertices.domain) {
                        var currentProperty = (vertex_props[v,etypeInd].borrow():(borrowed Property(uint)));
                        currentProperty!.dataType = etypeInd;
                        currentProperty!.propertyIdentifier += i;
                        currentProperty!.propertyValue[i] = dataArray[j];
                    }
                }
                when (DType.Float64) {
                    var dataArraySym = toSymEntry(dataArrayEntry, real);
                    var dataArray = dataArraySym.a;
                    var etypeInd = dataTypeMapStrToInt[etypeStr];
                    forall (v,j) in zip(inputVertices,inputVertices.domain) {
                        var currentProperty = (vertex_props[v,etypeInd].borrow():(borrowed Property(real)));
                        currentProperty!.dataType = etypeInd;
                        currentProperty!.propertyIdentifier += i;
                        currentProperty!.propertyValue[i] = dataArray[j];
                    }
                }
                when (DType.Bool) {
                    var dataArraySym = toSymEntry(dataArrayEntry, bool);
                    var dataArray = dataArraySym.a;
                    var etypeInd = dataTypeMapStrToInt[etypeStr];
                    forall (v,j) in zip(inputVertices,inputVertices.domain) {
                        var currentProperty = (vertex_props[v,etypeInd].borrow():(borrowed Property(bool)));
                        currentProperty!.dataType = etypeInd;
                        currentProperty!.propertyIdentifier += i;
                        currentProperty!.propertyValue[i] = dataArray[j];
                    }
                }
                when (DType.Strings) {
                    var dataArraySym = toSegStringSymEntry(dataArrayEntry);
                    var dataArray = getSegString(dataArraySym.name, st);
                    var etypeInd = dataTypeMapStrToInt[etypeStr];
                    forall (v,j) in zip(inputVertices,inputVertices.domain) {
                        var currentProperty = (vertex_props[v,etypeInd].borrow():(borrowed Property(string)));
                        currentProperty!.dataType = etypeInd;
                        currentProperty!.propertyIdentifier += i;
                        currentProperty!.propertyValue[i] = dataArray[j];
                    }
                }
            }
        }
        timer.stop();

        // Add the component for the node labels for the graph.
        graph.withComp(new shared SymEntry2D(vertex_props):GenSymEntry, "VERTEX_PROPS");
        graph.withComp(new shared SegStringSymEntry(columns.offsets, columns.values, string):GenSymEntry, "VERTEX_PROPS_COL_MAP");
        graph.withComp(new shared SymEntry(dataTypeMapIntToStr):GenSymEntry, "VERTEX_PROPS_DTYPE_MAP");
        graph.withComp(new shared MapSymEntry(col2dtype):GenSymEntry, "VERTEX_PROPS_COL2DTYPE");
        var repMsg = "node properties added";
        outMsg = "addNodeProperties took " + timer.elapsed():string + " sec ";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addNodePropertiesMsg

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
        var arrays = msgArgs.getValueOf("Arrays");

        // Extract the names of the arrays passed to the function.
        var arrays_list = arrays.split();
        var input_internal_edge_indices_name = arrays_list[0];
        var input_relationships_name = arrays_list[1];
        var relationship_mapper_name = arrays_list[2];
        
        // Extract the actual arrays for each of the names above.
        var input_internal_edge_indices_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(input_internal_edge_indices_name, st);
        var input_internal_edge_indices_sym = toSymEntry(input_internal_edge_indices_entry, int);
        var input_internal_edge_indices = input_internal_edge_indices_sym.a;

        var input_relationships_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(input_relationships_name, st);
        var input_relationships_sym = toSymEntry(input_relationships_entry, int);
        var input_relationships = input_relationships_sym.a;

        var relationship_mapper:SegString = getSegString(relationship_mapper_name, st);

        // Get graph for usage and needed arrays.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var src_actual = toSymEntry(graph.getComp("SRC"), int).a;
        var dst_actual = toSymEntry(graph.getComp("DST"), int).a;
        var segments = toSymEntry(graph.getComp("SEGMENTS"), int).a;

        // Create array of lists to store relationships and populate it. 
        var edge_relationships: [src_actual.domain] domain(int);
        
        var timer:stopwatch;
        timer.start();
        forall i in input_internal_edge_indices.domain {
            var rel = input_relationships[i];
            var ind = input_internal_edge_indices[i];
            edge_relationships[ind] += rel;
        }
        
        // Add the component for the node labels for the graph. 
        graph.withComp(new shared SymEntry(edge_relationships):GenSymEntry, "EDGE_RELATIONSHIPS");
        graph.withComp(new shared SegStringSymEntry(relationship_mapper.offsets, relationship_mapper.values, string):GenSymEntry, "EDGE_RELATIONSHIPS_MAP");
        timer.stop();
        var repMsg = "edge relationships added";
        outMsg = "DipSLLaddEdgeRelationships took " + timer.elapsed():string + " sec";
        
        // Print out debug information to arkouda server output. 
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of addEdgeRelationshipsMsg

    /**
    * Gets node labels of the property graph.
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
    proc getNodeLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract the needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");

        // Get graph for usage and the node label mapper. 
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        const ref label_mapper_entry = toSegStringSymEntry(graph.getComp("VERTEX_LABELS_MAP"));

        // Add new copies of each to the symbol table.
        var label_mapper = assembleSegStringFromParts(label_mapper_entry.offsetsEntry, label_mapper_entry.bytesEntry, st);
        var repMsg = 'created ' + st.attrib(label_mapper.name) + '+created bytes.size %t'.format(label_mapper.nBytes);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of getNodeLabelsMsg

    /**
    * Message parser for getting node properties of the property graph.
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
    proc getNodePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract the needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");

        // Get graph for usage and the node label mapper. 
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        const ref property_mapper_entry = toSegStringSymEntry(graph.getComp("VERTEX_PROPS_COL_MAP"));

        // Add new copies of each to the symbol table.
        var property_mapper = assembleSegStringFromParts(property_mapper_entry.offsetsEntry, property_mapper_entry.bytesEntry, st);
        var repMsg = 'created ' + st.attrib(property_mapper.name) + '+created bytes.size %t'.format(property_mapper.nBytes);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of getNodePropertiesMsg

    /**
    * Gets edge relationships of the property graph.
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
    proc getEdgeRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        // Parse the message from Python to extract the needed data. 
        var graphEntryName = msgArgs.getValueOf("GraphName");

        // Get graph for usage and the edge relationship mapper. 
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        const ref relationship_mapper_entry = toSegStringSymEntry(graph.getComp("EDGE_RELATIONSHIPS_MAP"));

        // Add new copies of each to the symbol table.
        var relationship_mapper = assembleSegStringFromParts(relationship_mapper_entry.offsetsEntry, relationship_mapper_entry.bytesEntry, st);
        var repMsg = 'created ' + st.attrib(relationship_mapper.name) + '+created bytes.size %t'.format(relationship_mapper.nBytes);

        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of getEdgeRelationshipsMsg

    /**
    * Queries the property graph and returns a boolean array indicating which nodes contain the 
    * given labels.
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
    proc queryLabelsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        
        // Parse the message from Python to extract needed data.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var labelsToFindName = msgArgs.getValueOf("LabelsToFindName");
        var op = msgArgs.getValueOf("Op");

        // Extract graph data for usage in this function.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var node_labels = toSymEntry(graph.getComp("VERTEX_LABELS"), domain(int)).a;

        // Extract the array that contains the labels we are looking for.
        var labels_to_find_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(labelsToFindName, st);
        var labels_to_find_sym = toSymEntry(labels_to_find_entry, int);
        var labels_to_find = labels_to_find_sym.a;

        // Convert array to associative domain to maintain the labels to find.
        var labels_to_find_set : domain(int);
        forall lbl_id in labels_to_find with (ref labels_to_find_set) do labels_to_find_set += lbl_id;
        var return_array : [node_labels.domain] bool;

        // Distribute the labels_to_find_set to each locale.
        var labels_to_find_set_dist = makeDistArray(numLocales, domain(int));
        coforall loc in Locales do on loc {
            labels_to_find_set_dist[here.id] = labels_to_find_set;
        }

        // Search in parallel for the nodes that have the labels to find.
        var timer:stopwatch;
        timer.start();
        select op {
            when "or" {
                forall (u, u_label_set) in zip(node_labels.domain, node_labels) with (ref return_array) {
                    if u_label_set.size > 0 {
                        var label_set_here = labels_to_find_set_dist[here.id];
                        var intersection = u_label_set & label_set_here;
                        if intersection.size > 0 then return_array[u] = true;
                    }
                }
            }
            when "and" {
                forall (u, u_label_set) in zip(node_labels.domain, node_labels) with (ref return_array) {
                    var label_set_here = labels_to_find_set_dist[here.id];
                    if u_label_set.size > 0 {
                        if u_label_set.contains(label_set_here) {
                            return_array[u] = true;
                        }
                    }
                }
            }
            otherwise {
                var errorMsg = notImplementedError(pn, op);
                pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
                return new MsgTuple(errorMsg, MsgType.ERROR);
            }
        }
        timer.stop();
        var time_msg = "label query DIP-SLL took " + timer.elapsed():string + " sec";
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);

        var retName = st.nextName();
        var retEntry = new shared SymEntry(return_array);
        st.addEntry(retName, retEntry);
        var repMsg = 'created ' + st.attrib(retName);

        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } //end of queryLabelsMsg

    /**
    * Queries the property graph and returns a boolean array indicating which nodes match the query
    * operation.
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
    proc queryNodePropertiesMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        
        // Parse the message from Python to extract needed data.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var column = msgArgs.getValueOf("Column");
        var value = msgArgs.getValueOf("Value");
        var op = msgArgs.getValueOf("Op");

        // Extract graph data for usage in this function.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var vertex_props = toSymEntry2D(graph.getComp("VERTEX_PROPS"), shared GenProperty?).a;
        const ref entry = toSegStringSymEntry(graph.getComp("VERTEX_PROPS_COL_MAP"));
        var vertex_props_col_map = assembleSegStringFromParts(entry.offsetsEntry, entry.bytesEntry, st);
        var vertex_props_dtype_map = toSymEntry(graph.getComp("VERTEX_PROPS_DTYPE_MAP"), string).a;
        var vertex_props_col2dtype = toMapSymEntry(graph.getComp("VERTEX_PROPS_COL2DTYPE")).stored_map;
        var return_array : [makeDistDom(graph.n_vertices)] bool;
        var dtype = vertex_props_col2dtype[column];

        var colId = 0;
        for i in 0..<vertex_props_col_map.size do if vertex_props_col_map[i] == column then colId = i;
        var dtypeId = 0; 
        for i in 0..<vertex_props_dtype_map.size do if vertex_props_dtype_map[i] == dtype then dtypeId = i;
        
        writeln("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");
        for vertex in vertex_props {
            writeln(vertex);
        }
        writeln("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");
        writeln("querying ", column, " with id ", colId, " datatype ", dtype, " which has id ", dtypeId, " with op ", op, " ", value);
        writeln("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");

        // Perform the querying operation in parallel.
        var timer:stopwatch;
        timer.start();
        select dtype {
            when "float64" {
                select op {
                    when ">" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(real));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] > value:real then return_array[u] = true; 
                            }
                        }
                    }
                    when "<" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(real));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] < value:real then return_array[u] = true; 
                            }
                        }
                    }
                    when "<=" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(real));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] <= value:real then return_array[u] = true; 
                            }
                        }
                    }
                    when ">=" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(real));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] >= value:real then return_array[u] = true; 
                            }
                        }
                    }
                    when "==" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(real));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] == value:real then return_array[u] = true; 
                            }
                        }
                    }
                    when "<>" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(real));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] != value:real then return_array[u] = true; 
                            }
                        }
                    }
                }
            }
            when "int64" {
                select op {
                    when ">" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(int));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] > value:int then return_array[u] = true; 
                            }
                        }
                    }
                    when "<" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(int));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] < value:int then return_array[u] = true; 
                            }
                        }
                    }
                    when "<=" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(int));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] <= value:int then return_array[u] = true; 
                            }
                        }
                    }
                    when ">=" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(int));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] >= value:int then return_array[u] = true; 
                            }
                        }
                    }
                    when "==" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(int));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] == value:int then return_array[u] = true; 
                            }
                        }
                    }
                    when "<>" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(int));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] != value:int then return_array[u] = true; 
                            }
                        }
                    }
                }
            }
            when "uint64" {
                select op {
                    when ">" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(uint));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] > value:uint then return_array[u] = true; 
                            }
                        }
                    }
                    when "<" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(uint));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] < value:uint then return_array[u] = true;
                            }
                        }
                    }
                    when "<=" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(uint));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] <= value:uint then return_array[u] = true;
                            }
                        }
                    }
                    when ">=" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(uint));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] >= value:uint then return_array[u] = true;
                            }
                        }
                    }
                    when "==" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(uint));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] == value:uint then return_array[u] = true; 
                            }
                        }
                    }
                    when "<>" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(uint));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] != value:uint then return_array[u] = true;
                            }
                        }
                    }
                }
            }
            when "bool" {
                var value = value.toLower():bool;
                select op {
                    when "==" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(bool));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] == value:bool then return_array[u] = true;
                            }
                        }
                    }
                    when "<>" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(bool));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId] != value:bool then return_array[u] = true;
                            }
                        }
                    }
                }
            }
            when "str" {
                select op {
                    when "contains" {
                        forall (u,d) in vertex_props.domain[.., dtypeId..dtypeId] with (ref return_array, ref dtypeId, ref colId) {
                            var currentProperty = vertex_props[u,d].borrow():(borrowed Property(string));
                            if currentProperty.propertyValue.size > 0 {
                                if currentProperty.propertyValue[colId].find(value:string) != -1 then return_array[u] = true;
                            }
                        }
                    }
                }
            }
        }
        timer.stop();
        var time_msg = "node properties query took " + timer.elapsed():string + " sec";
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);

        var retName = st.nextName();
        var retEntry = new shared SymEntry(return_array);
        st.addEntry(retName, retEntry);
        var repMsg = 'created ' + st.attrib(retName);

        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } //end of queryLabelsMsg

    /**
    * Queries the property graph and returns a boolean array indicating which edges contain the 
    * given relationships.
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
    proc queryRelationshipsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        
        // Parse the message from Python to extract needed data.
        var graphEntryName = msgArgs.getValueOf("GraphName");
        var relationshipsToFindName = msgArgs.getValueOf("RelationshipsToFindName");
        var op = msgArgs.getValueOf("Op");

        // Extract graph data for usage in this function.
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var graph = gEntry.graph;
        var edge_relationships = toSymEntry(graph.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;

        // Extract the array that contains the relationships we are looking for.
        var relationships_to_find_entry: borrowed GenSymEntry = getGenericTypedArrayEntry(relationshipsToFindName, st);
        var relationships_to_find_sym = toSymEntry(relationships_to_find_entry, int);
        var relationships_to_find = relationships_to_find_sym.a;

        // Convert array to associative domain to maintain the relationships to find.
        var relationships_to_find_set : domain(int);
        forall rel_id in relationships_to_find with (ref relationships_to_find_set) do relationships_to_find_set += rel_id;
        var return_array : [edge_relationships.domain] bool;

        // Distribute the relationships_to_find_set to each locale.
        var relationships_to_find_set_dist = makeDistArray(numLocales, domain(int));
        coforall loc in Locales do on loc {
            relationships_to_find_set_dist[here.id] = relationships_to_find_set;
        }
        
        // Search in parallel for the nodes that have the labesl to find.
        var timer:stopwatch;
        timer.start();
        select op {
            when "or" {
                forall (u, u_relationship_set) in zip(edge_relationships.domain, edge_relationships) with (ref return_array) {
                    if u_relationship_set.size != 0 {
                        var relationship_set_here = relationships_to_find_set_dist[here.id];
                        var intersection = u_relationship_set & relationship_set_here;
                        if intersection.size > 0 then return_array[u] = true;
                    }
                }
            }
            when "and" {
                forall (u, u_relationship_set) in zip(edge_relationships.domain, edge_relationships) with (ref return_array) {
                    var relationship_set_here = relationships_to_find_set_dist[here.id];
                    if u_relationship_set.size > 0 {
                        if u_relationship_set.contains(relationship_set_here) {
                            return_array[u] = true;
                        }
                    }
                }
            }
            otherwise {
                var errorMsg = notImplementedError(pn, op);
                pgmLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
                return new MsgTuple(errorMsg, MsgType.ERROR);
            }
        }
        timer.stop();
        var time_msg = "relationship query DIP-SLL took " + timer.elapsed():string + " sec";
        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),time_msg);

        var retName = st.nextName();
        var retEntry = new shared SymEntry(return_array);
        st.addEntry(retName, retEntry);
        var repMsg = 'created ' + st.attrib(retName);

        pgmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } //end of queryRelationshipsMsg

    use CommandMap;
    registerFunction("addNodeLabels", addNodeLabelsMsg, getModuleName());
    registerFunction("addNodeProperties", addNodePropertiesMsg, getModuleName());
    registerFunction("addEdgeRelationships", addEdgeRelationshipsMsg, getModuleName());
    registerFunction("getNodeLabels", getNodeLabelsMsg, getModuleName());
    registerFunction("getNodeProperties", getNodePropertiesMsg, getModuleName());
    registerFunction("getEdgeRelationships", getEdgeRelationshipsMsg, getModuleName());
    registerFunction("queryLabels", queryLabelsMsg, getModuleName());
    registerFunction("queryNodeProperties", queryNodePropertiesMsg, getModuleName());
    registerFunction("queryRelationships", queryRelationshipsMsg, getModuleName());
}