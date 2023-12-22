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
    use NumPyDType;

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

    proc addSparseArrayToSymbolTable(newData, st): (string,string) throws {
        var attrName = st.nextName();
        var attrEntry = new shared SymEntryAS(newData);
        st.addEntry(attrName, attrEntry);
        var repMsg = "created " + st.attrib(attrName) + "+ ";
        return (repMsg, attrName);
    }

    proc isConsecutive(array: [?D]) {
        var consecutive:bool = true;
        forall (v,d) in zip(array[D.low+1..D.high], D[D.low+1..D.high]) 
            with (ref consecutive) 
            do if v != array[d-1] + 1 then consecutive = false;
        return consecutive;
    }

    proc isAligned(array: [?D]) {
        var aligned:bool = true;
        if array[D.low] != D.low then aligned = false;
        if array[D.high] != D.high then aligned = false;
        return aligned;
    }

    proc insertArrays (attributes, attributeSymTabIds, ref attributeMap: map(?), consecutive:bool, sparseDataDomain, ref internalIndices, st:borrowed SymTab, mapper: [?D] string = blockDist.createArray({0..0}, string)) throws {
        var repMsg = "";
        for i in 0..<attributeSymTabIds.size {
            var attributeName = attributes[i];
            var dataArraySymTabId = attributeSymTabIds[i];
            var dataArrayEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(dataArraySymTabId, st);
            var etype = dataArrayEntry.dtype;
            select etype {
                when (DType.Int64) {
                    if consecutive {
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(dataArraySymTabId, (attributeName, ""));
                        else 
                            attributeMap.add(dataArraySymTabId, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                    } else {
                        var originalData = toSymEntry(dataArrayEntry, int).a;
                        var newData: [sparseDataDomain] int;
                        insertData(consecutive, originalData, newData, internalIndices, int);
                        var (reply, attrName) = addSparseArrayToSymbolTable(newData, st);
                        repMsg += reply;
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(attrName, (attributeName, ""));
                        else
                            attributeMap.add(attrName, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                    }
                }
                when (DType.UInt64) {
                    if consecutive {
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(dataArraySymTabId, (attributeName, ""));
                        else 
                            attributeMap.add(dataArraySymTabId, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                    } else {
                        var originalData = toSymEntry(dataArrayEntry, uint).a;
                        var newData: [sparseDataDomain] uint;
                        insertData(consecutive, originalData, newData, internalIndices, uint);
                        var (reply, attrName) = addSparseArrayToSymbolTable(newData, st);
                        repMsg += reply;
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(attrName, (attributeName, ""));
                        else
                            attributeMap.add(attrName, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                    }
                }
                when (DType.Float64) {
                    if consecutive {
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(dataArraySymTabId, (attributeName, ""));
                        else 
                            attributeMap.add(dataArraySymTabId, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                    } else {
                        var originalData = toSymEntry(dataArrayEntry, real).a;
                        var newData: [sparseDataDomain] real;
                        insertData(consecutive, originalData, newData, internalIndices, real);
                        var (reply, attrName) = addSparseArrayToSymbolTable(newData, st);
                        repMsg += reply;
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(attrName, (attributeName, ""));
                        else
                            attributeMap.add(attrName, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                    }
                }
                when (DType.Bool) {
                    if consecutive {
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(dataArraySymTabId, (attributeName, ""));
                        else 
                            attributeMap.add(dataArraySymTabId, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                    } else {
                        var originalData = toSymEntry(dataArrayEntry, bool).a;
                        var newData: [sparseDataDomain] bool;
                        insertData(consecutive, originalData, newData, internalIndices, bool);
                        var (reply, attrName) = addSparseArrayToSymbolTable(newData, st);
                        repMsg += reply;
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(attrName, (attributeName, ""));
                        else
                            attributeMap.add(attrName, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                    }
                }
                when (DType.Strings) {
                    if consecutive {
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(dataArraySymTabId, (attributeName, ""));
                        else 
                            attributeMap.add(dataArraySymTabId, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
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
                        if attributeMap.valType == (string,string) then
                            attributeMap.add(attrName, (attributeName, ""));
                        else
                            attributeMap.add(attrName, (attributeName, toSegStringSymEntry(st.lookup(mapper[i]))));
                        repMsg += "created " + st.attrib(attrName) + "+ ";
                    }
                }
            }
        }
        return repMsg;
    }
}