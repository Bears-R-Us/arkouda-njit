module GraphArray {
    // Chapel modules.
    use Map;
    use Reflection;
    use Utils;
    use ReplicatedDist;
    
    // Arkouda modules.
    use Logging;
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
        SRC_R_SDI,          // int array with source vertices for each edge, swapped with DST_SDI
        DST_R_SDI,          // int array with destination vertices for each edge, swapped with SRC_SDI
        SEGMENTS_R_SDI,     // int array segmenting neighborhoods in DST_R_SDI
        EDGE_WEIGHT_SDI,    // int, real, int, or bool array with edge weights
        VERTEX_MAP_SDI,     // int array where VERTEX_MAP_SDI[u] gives the original value of u
        RANGES_SDI,         // int array with tuple of low values per locale of SRC_SDI
        RANGES_R_SDI,       // int array with tuple of low values per locale of SRC_R_SDI
        VERTEX_LABELS,      // map of type (string, (string,SegStringSymEntry))
        EDGE_RELATIONSHIPS, // map of type (string, (string,SegStringSymEntry))
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

        proc isDirected():bool { return this.directed; }
        proc isWeighted():bool { return this.weighted; }
        proc isPropertied():bool { return this.hasComp("VERTEX_LABELS") ||
                                          this.hasComp("EDGE_RELATIONSHIPS") ||
                                          this.hasComp("VERTEX_PROPERTIES") ||
                                          this.hasComp("EDGE_PROPERTIES"); }
        proc isReversed():bool { return this.hasComp("SRC_RDI"); }

        proc withComp(a:shared GenSymEntry, atrname:string):SegGraph throws { components.add(atrname:Component, a); return this; }
        proc hasComp(atrname:string):bool throws { return components.contains(atrname:Component); }
        proc getComp(atrname:string):GenSymEntry throws { return components[atrname:Component]; }
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

    /**
    * Allows storage of sparse arrays in the Symbol Table (SymTab).
    * NOTE: Currently returns an error since assignment of an inputted sparse subdomain to an 
    *       already-created sparse subdomain is not allowed. Workaround is incoming.
    */
    class SparseSymEntry : GenSymEntry {
        type etype;
        var bD: makeDistDom(1).type;
        var sD: sparse subdomain(bD);
        var a: [sD] etype;
        
        // TODO: fix error with sparse_subdomain assignment not being allowed.
        proc init(in sparse_array: [?sparse_subdomain] ?etype) {
            super.init(etype);
            this.etype = etype;
            this.sD = sparse_subdomain;
            this.a = sparse_array;
        }
    }

    class ReplicatedSymEntry : GenSymEntry {
        type etype;
        var rD = {0..0} dmapped replicatedDist();
        var a: [rD] etype;

        proc init(in replicated_array: [?replicated_domain] ?etype) {
            super.init(etype);
            this.etype = etype;
            this.rD = replicated_domain;
            this.a = replicated_array;
            var home = here.id;
            // TODO: Somehow once the array is stored in the symbol table, all replicands
            //       disappear.
            coforall loc in Locales do on loc {
                this.a.replicand(Locales[loc.id]) = this.a.replicand(Locales[home]);
            }
            // for loc in Locales do on loc {
            //     writeln("this.a = ", this.a.replicand(Locales[loc.id]));
            // }
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

    proc toSparseSymEntry(e) {
        return try! e : borrowed SparseSymEntry();
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
        var indicesEntry: shared SparseSymEntry(int);

        proc init(offsetsSymEntry: shared SymEntry(int), bytesSymEntry: shared SymEntry(uint(8)), indicesSymEntry: shared SparseSymEntry(int), type etype) {
            super.init(offsetsSymEntry, bytesSymEntry, etype);
            this.indicesEntry = indicesSymEntry;
        }
    }

    proc toSparsePropertySegStringSymEntry(entry: borrowed AbstractSymEntry) throws {
        return (entry: borrowed SparsePropertySegStringSymEntry);
    }
}