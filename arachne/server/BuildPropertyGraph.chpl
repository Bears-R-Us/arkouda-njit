module BuildPropertyGraph {
    // Chapel modules.
    use Map;
    use BlockDist;
    
    // Arachne Modules.
    use GraphArray;
    
    // Arkouda modules.
    use CommAggregation;
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use MultiTypeRegEntry;
    use NumPyDType;
    use RegistrationMsg;
    use SegmentedString;

    /* Given the indices of a dense array, stores the values from the original dense array into the
    corresponding indices of the new sparse array.
    
    :arg originalArray: original array with data.
    :type originalArray: ref [?D] ?t
    :arg newSparseArray: sparse array created from originalArray. 
    :type newSparseArray: ref [?D] ?t
    :arg internalIndices: indices of dense array to transfer to sparse array.
    :type internalIndices: ref [?D] ?t
    :arg t: type of originalArray and newSparseArray.
    :type t: type
    
    :returns: void
    */
    proc insertDataToSparseArray(ref originalArray, ref newSparseArray, ref internalIndices, type t) {
        forall (i,j) in zip(internalIndices, internalIndices.domain) 
            with (var agg = new DstAggregator(t)) 
            do agg.copy(newSparseArray[i], originalArray[j]);
    }

    /* Adds a sparse array into the symbol table.

    :arg newSparseArray: sparse array to add into symbol table.
    :type newSparseArray: [?D] ?t
    :arg st: symbol table.
    :type st: borrowed SymTab

    :returns: void
    */
    proc addSparseArrayToSymbolTable(newSparseArray, st): (string,string) throws {
        var attrName = st.nextName();
        var attrEntry = new shared SparseSymEntry(newSparseArray);
        st.addEntry(attrName, attrEntry);
        var repMsg = "created " + st.attrib(attrName) + "+ ";
        return (repMsg, attrName);
    }

    /* Checks to see if an array is consecutive.

    :arg array: array to check.
    :type array: [?D] ?t

    :returns: bool
    */
    proc isConsecutive(array: [?D]) {
        var consecutive:bool = true;
        forall (v,d) in zip(array[D.low+1..D.high], D[D.low+1..D.high]) 
            with (ref consecutive) 
            do if v != array[d-1] + 1 then consecutive = false;
        return consecutive;
    }

    /* Checks to see if an array is aligned, i.e. the element value in the first position of the
    array is equal to the first value of the index set and the same for the last value.

    :arg array: array to check.
    :type array: [?D] ?t

    :returns: bool
    */
    proc isAligned(array: [?D]) {
        var aligned:bool = true;
        if array[D.low] != D.low then aligned = false;
        if array[D.high] != D.high then aligned = false;
        return aligned;
    }

    /* Inserts multiple attributes into the property graph data structure by updating the argument
    `attributeMap`. Symbol table identifiers and `SegStringSymEntry` objects are stored inside of
    `attributeMap` dependent on the type of attribute being stored varying between vertex labels, 
    edge relationships, vertex properties, or edge properties. 

    Populates and adds in sparse arrays if only a subset of the edge or vertex sets are owned by 
    the attribute being inserted.

    :arg attributes: array of strings containing the names of the attributes (columns) to insert.
    :type attributes: [?D] string
    :arg attributeSymTabIds: symbol table ids that correspond to the array for each attribute.
    :type attributeSymTabIds: [?D] string
    :arg attributeMap: will store symbol table id with tuple containing column name and object type.
    :type attributeMap: ref map(?)
    :arg consecutive: is the data consecutive?
    :type consecutive: bool
    :arg sparseDataDomain: new domain for sparse data if it is found data is not consecutive.
    :type sparseDataDomain: ?D
    :arg internalIndices: indices whose data from original to sparse is to be transferred.
    :type internalIndices: [?D] int
    :arg st: symbol table.
    :type st: borrowed SymTab
    :arg mapper: if applicable, mapper exists for string relationships or labels.
    :type mapper: [?D] ?t

    :returns: string

    */
    proc insertAttributes(  attributes, attributeSymTabIds, attributeTypes,
                            ref attributeMap: map(?), 
                            consecutive:bool, 
                            sparseDataDomain, 
                            ref internalIndices, 
                            st:borrowed SymTab):string throws {
        var repMsg = "";
        for i in attributes.domain {
            var attributeName = attributes[i];
            var dataArraySymTabId = attributeSymTabIds[i];
            var dataArrayType = attributeTypes[i];

            select dataArrayType {
                when "Strings", "pdarray" {
                    var dataArrayEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(dataArraySymTabId, st);
                    var etype = dataArrayEntry.dtype;
                    select etype {
                        when (DType.Int64) {
                            if consecutive {
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(dataArraySymTabId, (attributeName, dataArrayType));
                            } else {
                                var originalData = toSymEntry(dataArrayEntry, int).a;
                                var newData: [sparseDataDomain] int;
                                insertDataToSparseArray(originalData, newData, internalIndices, int);
                                var (reply, attrName) = addSparseArrayToSymbolTable(newData, st);
                                repMsg += reply;
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(attrName, (attributeName, dataArrayType));
                            }
                        }
                        when (DType.UInt64) {
                            if consecutive {
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(dataArraySymTabId, (attributeName, dataArrayType));
                            } else {
                                var originalData = toSymEntry(dataArrayEntry, uint).a;
                                var newData: [sparseDataDomain] uint;
                                insertDataToSparseArray(originalData, newData, internalIndices, uint);
                                var (reply, attrName) = addSparseArrayToSymbolTable(newData, st);
                                repMsg += reply;
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(attrName, (attributeName, dataArrayType));
                            }
                        }
                        when (DType.Float64) {
                            if consecutive {
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(dataArraySymTabId, (attributeName, dataArrayType));
                            } else {
                                var originalData = toSymEntry(dataArrayEntry, real).a;
                                var newData: [sparseDataDomain] real;
                                insertDataToSparseArray(originalData, newData, internalIndices, real);
                                var (reply, attrName) = addSparseArrayToSymbolTable(newData, st);
                                repMsg += reply;
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(attrName, (attributeName, dataArrayType));
                            }
                        }
                        when (DType.Bool) {
                            if consecutive {
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(dataArraySymTabId, (attributeName, dataArrayType));
                            } else {
                                var originalData = toSymEntry(dataArrayEntry, bool).a;
                                var newData: [sparseDataDomain] bool;
                                insertDataToSparseArray(originalData, newData, internalIndices, bool);
                                var (reply, attrName) = addSparseArrayToSymbolTable(newData, st);
                                repMsg += reply;
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(attrName, (attributeName, dataArrayType));
                            }
                        }
                        when (DType.Strings) {
                            if consecutive {
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(dataArraySymTabId, (attributeName, dataArrayType));
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
                                var indicesEntry = new shared SparseSymEntry(newData);

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
                                if attributeMap.valType == (string,string) then
                                    attributeMap.add(attrName, (attributeName, dataArrayType));
                                repMsg += "created " + st.attrib(attrName) + "+ ";
                            }
                        }
                    }
                }
                when "Categorical" {
                    if consecutive {
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(dataArraySymTabId, (attributeName, dataArrayType));
                    } else {
                        // TODO: Future work, handle nonconsecutive arrays.
                        var temp = blockDist.createArray({0..1}, int);
                        var dataArrayRegEntry = (st.registry.tab(dataArraySymTabId)):shared CategoricalRegEntry;
                        var categories = getSegString(dataArrayRegEntry.categories, st);
                        var codes = toSymEntry(getGenericTypedArrayEntry(dataArrayRegEntry.codes, st), int).a;
                        var permutation = if dataArrayRegEntry.permutation != "" then toSymEntry(getGenericTypedArrayEntry(dataArrayRegEntry.permutation, st), int).a else temp;
                        var segments = if dataArrayRegEntry.permutation != "" then toSymEntry(getGenericTypedArrayEntry(dataArrayRegEntry.segments, st), int).a else temp;
                        var na = dataArrayRegEntry.naCode;
                    }
                }
            }
        }
        return repMsg;
    }
}