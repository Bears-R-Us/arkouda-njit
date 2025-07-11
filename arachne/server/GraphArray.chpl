module GraphArray {
    // Chapel modules.
    use Map;
    use Set;
    use Reflection;
    use Utils;
    use ReplicatedDist;
    
    // Arkouda modules.
    use Logging;
    use AryUtil;
    use MultiTypeSymEntry;
    use MultiTypeSymbolTable;
    use SegmentedString;

    // Server message logger.
    private config const logLevel = LogLevel.DEBUG;
    const graphLogger = new Logger(logLevel);

    // Component key names to be stored stored in the components map for future retrieval
    enum Component {        
        // Symmetrical Double-Index (SDI) Components (and Property Graph Components)
        SRC_SDI,            // int array with source vertices for each edge
        DST_SDI,            // int array with destination vertices for each edge
        SEGMENTS_SDI,       // int array segmenting neighborhoods in DST_SDI
        NEIGHBORS_SET_SDI,  // helper set for WCC -- array of sets for each vertex i
        SRC_R_SDI,          // int array with source vertices for each edge, swapped with DST_SDI
        DST_R_SDI,          // int array with destination vertices for each edge, swapped with SRC_SDI
        SEGMENTS_R_SDI,     // int array segmenting neighborhoods in DST_R_SDI
        EDGE_WEIGHT_SDI,    // int, real, int, or bool array with edge weights
        VERTEX_MAP_SDI,     // int array where VERTEX_MAP_SDI[u] gives the original value of u
        RANGES_SDI,         // int array with tuple of low values per locale of SRC_SDI
        RANGES_R_SDI,       // int array with tuple of low values per locale of SRC_R_SDI
        
        // The key is the attribute (column) name and the value is a tuple of symbol table
        // identifier and data type.
        VERTEX_LABELS,      // map of type (string, (string,string))
        EDGE_RELATIONSHIPS, // map of type (string, (string,string))
        VERTEX_PROPERTIES,  // map of type (string, (string,string))
        EDGE_PROPERTIES,    // map of type (string, (string,string))

        // Reverse Double-Index (RDI) Components
        SRC_RDI,           // int array with source vertices for each edge
        DST_RDI,           // int array with destination vertices for each edge
        SRC_R_RDI,         // int array with source vertices for each edge, swapped with DST_RDI
        DST_R_RDI,         // int array with destination vertices for each edge, swapped with SRC_RDI
        START_IDX_RDI,     // int array with starting indices for each vertex point in SRC_RDI
        START_IDX_R_RDI,   // int array with starting indices for each vertex point in SRC_R_RDI
        NEIGHBOR_RDI,      // int array with the number of neighbors for each vertex based off DST_RDI
        NEIGHBOR_R_RDI,    // int array with the number of neighbors for each vertex based off DST_R_RDI
        EDGE_WEIGHT_RDI,   // uint, real, int, or bool array with edge weights; must search index in SRC_RDI and DST_RDI
        VERTEX_MAP_RDI,    // int array where VERTEX_MAP_RDI[u] gives the original value of u
        RANGES_RDI,        // uint array with tuple of low values per locale of SRC_RDI
        RANGES_R_RDI,      // uint array with tuple of low values per locale of SRC_R_RDI
    }

    /**
    * We use several arrays and integers to represent a graph.
    * Instances are ephemeral, not stored in the symbol table. Instead, attributes
    * of this class refer to symbol table entries that persist. This class is a
    * convenience for bundling those persistent objects and defining graph-relevant
    * operations.
    */
    class SegGraph {
        // Map to the hold various components of our Graph; use enum Component values as map keys
        var components = new map(Component, shared GenSymEntry, parSafe=false);

        // Total number of vertices
        var n_vertices : int;

        // Total number of edges
        var n_edges : int;

        // The graph is directed (true) or undirected (false)
        var directed : bool;

        // The graph is weighted (true) or unweighted (false)
        var weighted: bool;

        /**
        * Init the basic graph object, we'll compose the pieces using the withComp method.
        */
        proc init(num_v:int, num_e:int, directed:bool, weighted:bool) {
            this.n_vertices = num_v;
            this.n_edges = num_e;
            this.directed = directed;
            this.weighted = weighted;
        }

        proc isDirected():bool throws { return this.directed; }
        proc isWeighted():bool throws { return this.weighted; }
        proc isPropertied():bool throws { return this.hasComp("VERTEX_LABELS") ||
                                          this.hasComp("EDGE_RELATIONSHIPS") ||
                                          this.hasComp("VERTEX_PROPERTIES") ||
                                          this.hasComp("EDGE_PROPERTIES"); }
        proc isReversed():bool throws { return this.hasComp("SRC_RDI"); }

        proc withComp(a:shared GenSymEntry, atrname:string):SegGraph throws { components.add(atrname:Component, a); return this; }
        proc hasComp(atrname:string):bool throws { return components.contains(atrname:Component); }
        proc getComp(atrname:string):GenSymEntry throws { return components[atrname:Component]; }

        proc getNodeAttributes() throws {
            var attributes = new map(string, (string, string));
            var emptyMap = new map(string, (string, string));

            ref labels = if this.hasComp("VERTEX_LABELS") then 
                            (this.getComp("VERTEX_LABELS"):(borrowed MapSymEntry(
                                string, (string, string)
                            ))).stored_map else emptyMap;

            ref properties = if this.hasComp("VERTEX_PROPERTIES") then 
                                (this.getComp("VERTEX_PROPERTIES"):(borrowed MapSymEntry(
                                    string, (string, string)
                                ))).stored_map else emptyMap;

            attributes.extend(labels);
            attributes.extend(properties);

            return attributes;
        }

        proc getEdgeAttributes() throws {
            var attributes = new map(string, (string, string));
            var emptyMap = new map(string, (string, string));

            ref relationships = if this.hasComp("EDGE_RELATIONSHIPS") then 
                                    (this.getComp("EDGE_RELATIONSHIPS"):(borrowed MapSymEntry(
                                        string, (string, string)
                                    ))).stored_map else emptyMap;

            ref properties = if this.hasComp("EDGE_PROPERTIES") then 
                                (this.getComp("EDGE_PROPERTIES"):(borrowed MapSymEntry(
                                    string, (string, string)
                                ))).stored_map else emptyMap;

            attributes.extend(relationships);
            attributes.extend(properties);

            return attributes;
        }

        proc ref generateNeighborsAsSet(st: borrowed SymTab) throws {
            const ref src = toSymEntry(getComp("SRC_SDI"), int).a;
            const ref dst = toSymEntry(getComp("DST_SDI"), int).a;
            const ref seg = toSymEntry(getComp("SEGMENTS_SDI"), int).a;
            var neighborsSet = makeDistArray(seg.size-1, set(int));

            forall u in 0..seg.size-2 {
                var start = seg[u];
                var end = seg[u+1]-1;
                const ref neighbors = dst[start..end];
                for v in neighbors do neighborsSet[u].add(v);
            }
            withComp(createSymEntry(neighborsSet):GenSymEntry, "NEIGHBORS_SET_SDI");
        }
    }

    /**
    * GraphSymEntry is the wrapper class around SegGraph so it may be stored in 
    * the Symbol Table (SymTab).
    */
    class GraphSymEntry : CompositeSymEntry {
        var graph: shared SegGraph;

        proc init(segGraph: shared SegGraph) {
            super.init();
            this.entryType = SymbolEntryType.CompositeSymEntry;
            assignableTypes.add(this.entryType);
            this.graph = segGraph;
        }
        override proc getSizeEstimate(): int {
            return 1;
        }
    }

    /**
    * Allows storage of associative arrays in the Symbol Table (SymTab).
    */
    class AssociativeSymEntry : GenSymEntry {
        var aD: domain(int);
        var a: [aD] int;
        
        proc init(associative_array: [?associative_domain] int) {
            super.init(int);
            this.aD = associative_domain;
            this.a = associative_array;
        }
    }

    /* Allows storage of sparse arrays in the symbol table. */
    class SparseArraySymEntry : GenSymEntry {
        var a;
        proc etype type do return a.eltType;

        proc init(in a: []) where a.isSparse() { 
            super.init(a.eltType);
            this.a = a; 
        }
    }

    class ReplicatedSymEntry : GenSymEntry {
        var a;
        proc etype type do return a.eltType;

        proc init(in a: []) where isReplicatedArr(a) {
            super.init(a.eltType);
            this.a = a; 
        }
    }

    class MapSymEntry : GenSymEntry {
        type left;
        type right;
        var stored_map: map(left, right);
        
        proc init(ref map_to_store: map(?left, ?right)) {
            super.init(string);
            this.left = left;
            this.right = right;
            this.stored_map = map_to_store;
        }
    }

    proc toMapSymEntry(e) {
        return try! e : borrowed MapSymEntry(?);
    }

    proc toAssociativeSymEntry(e) {
        return try! e : borrowed AssociativeSymEntry();
    }

    proc toSparseArraySymEntry(e) {
        return try! e : borrowed SparseArraySymEntry();
    }

    proc toReplicatedSymEntry(e) {
        return try! e : borrowed ReplicatedSymEntry();
    }

    /**
    * Convenience proc to retrieve GraphSymEntry from SymTab.
    * Performs conversion from AbstractySymEntry to GraphSymEntry.
    */
    proc getGraphSymEntry(name:string, st: borrowed SymTab): borrowed GraphSymEntry throws {
        var abstractEntry:borrowed AbstractSymEntry = st.lookup(name);
        if !abstractEntry.isAssignableTo(SymbolEntryType.CompositeSymEntry) {
            var errorMsg = "Error: SymbolEntryType %s is not assignable to CompositeSymEntry".format(abstractEntry.entryType);
            graphLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            throw new Error(errorMsg);
        }
        return (abstractEntry: borrowed GraphSymEntry);
    }

    /**
    * Helper proc to cast AbstractSymEntry to GraphSymEntry.
    */
    proc toGraphSymEntry(entry: borrowed AbstractSymEntry): borrowed GraphSymEntry throws {
        return (entry: borrowed GraphSymEntry);
    }

    class PropertySegStringSymEntry : SegStringSymEntry(?) {
        var indicesEntry: shared SymEntry(int);

        proc init(offsetsSymEntry: shared SymEntry(int), bytesSymEntry: shared SymEntry(uint(8)), indicesSymEntry: shared SymEntry(int), type etype) {
            super.init(offsetsSymEntry, bytesSymEntry, etype);
            this.indicesEntry = indicesSymEntry;
        }
    }

    proc toPropertySegStringSymEntry(entry: borrowed AbstractSymEntry) throws {
        return (entry: borrowed PropertySegStringSymEntry);
    }

    class SparsePropertySegStringSymEntry : SegStringSymEntry(?) {
        var indicesEntry: shared SparseArraySymEntry(?);

        proc init(offsetsSymEntry: shared SymEntry(int), bytesSymEntry: shared SymEntry(uint(8)), indicesSymEntry: shared SparseArraySymEntry(?), type etype) {
            super.init(offsetsSymEntry, bytesSymEntry, etype);
            this.indicesEntry = indicesSymEntry;
        }
    }

    proc toSparsePropertySegStringSymEntry(entry: borrowed AbstractSymEntry) throws {
        return (entry: borrowed SparsePropertySegStringSymEntry);
    }
}