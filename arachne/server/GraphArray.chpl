module GraphArray {
    // Chapel modules.
    use Map;
    use Reflection;
    use Utils;
    
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
        SRC,                      // Array holding the source vertices of an edge
        DST,                      // Array holding the destination vertices of an edge
        SEGMENTS,                 // Array giving the segments of a neighborhood in DST
        EDGE_WEIGHT,              // Array giving the edge weights of the graph
        NODE_MAP,                 // Array where NODE_MAP[u] gives the original value of u
        RANGES,                   // Replicated array of the low vertex value in SRC per locale
        VERTEX_LABELS,            // Map of type (string, (string,SegStringSymEntry)
        EDGE_RELATIONSHIPS,       // Map of type (string, (string,SegStringSymEntry)
        VERTEX_PROPS,             // Map of type (string, (string,string))
        EDGE_PROPS,               // Map of type (string, (string,string))

        // For directed graphs we also want to maintain reversed edge arrays to easily find the
        // in-neighbors for each vertex. We will use the SRC_R and DST_R components below to 
        // signify the reversed edge arrays as well as a SEGMENTS_R array defined here. 
        SEGMENTS_R,

        // TEMPORARY COMPONENTS BELOW FOR UNDIRECTED GRAPHS TO ENSURE COMPATIBILTIY WITH OLD CODE.
        // We want to phase out the need for reversed arrays in undirected graph algorithms.
        // Includes: connected components, triangle counting, k-truss, and triangle centrality.
        SRC_R,                  // DST array
        DST_R,                  // SRC array
        START_IDX,              // Starting indices of vertices in SRC
        START_IDX_R,            // Starting indices of vertices in SRC_R
        NEIGHBOR,               // Number of neighbors for a given vertex based off SRC and DST
        NEIGHBOR_R,             // Number of neighbors for a given vertex based off SRC_R and DST_R
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

        // The graph is a property graph (true) or not (false)
        var propertied: bool;

        // The graph is a multigraph (true) or not (false)
        var multied: bool = false;

        // Undirected graphs are in the old format (true) or not (false)
        var reversed: bool = false;

        /**
        * Init the basic graph object, we'll compose the pieces using the withComp method.
        */
        proc init(num_v:int, num_e:int, directed:bool, weighted:bool, propertied:bool, multied:bool) {
            this.n_vertices = num_v;
            this.n_edges = num_e;
            this.directed = directed;
            this.weighted = weighted;
            this.propertied = propertied;
            this.multied = multied;
        }

        proc isDirected():bool { return this.directed; }
        proc isWeighted():bool { return this.weighted; }
        proc isPropertied():bool { return this.propertied; }
        proc isMultied():bool { return this.multied; }
        proc isReversed():bool { return this.reversed; }

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

    class SymEntryAD : GenSymEntry {
        var aD: domain(int);
        var a: [aD] int;
        
        proc init(associative_array: [?associative_domain] int) {
            super.init(int);
            this.aD = associative_domain;
            this.a = associative_array;
        }
    }

    class SymEntryAS : GenSymEntry {
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

    proc toSymEntryAD(e) {
        return try! e : borrowed SymEntryAD();
    }

    proc toSymEntryAS(e) {
        return try! e : borrowed SymEntryAS();
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
        var indicesEntry: shared SymEntryAS(int);

        proc init(offsetsSymEntry: shared SymEntry(int), bytesSymEntry: shared SymEntry(uint(8)), indicesSymEntry: shared SymEntryAS(int), type etype) {
            super.init(offsetsSymEntry, bytesSymEntry, etype);
            this.indicesEntry = indicesSymEntry;
        }
    }

    proc toSparsePropertySegStringSymEntry(entry: borrowed AbstractSymEntry) throws {
        return (entry: borrowed SparsePropertySegStringSymEntry);
    }
}