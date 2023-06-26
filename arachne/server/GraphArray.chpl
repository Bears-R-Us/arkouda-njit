module GraphArray {
    // Chapel modules.
    use Map;
    use Reflection;
    use Utils;
    
    // Arkouda modules.
    use Logging;
    use MultiTypeSymEntry;
    use MultiTypeSymbolTable;

    // Server message logger.
    private config const logLevel = LogLevel.DEBUG;
    const graphLogger = new Logger(logLevel);

    class Node {
        var data : string;
        var vertex : int;
        var prev : borrowed Node?;
        var next : shared Node?;

        proc init() {
            data = "";
            vertex = -1;
            prev = nil; 
            next = nil;
        }

        proc init(value: string, v: int) {
            data = value; 
            vertex = v;
            prev = nil; 
            next = nil;
        }

        proc append(node: shared Node) {
            this.next = node;
            node.prev = this;
        }

        override proc writeThis(f) throws {
            if(prev == nil) {
                f.write("{ data = ", data, ", vertex = ", vertex, ", prev = nil",            ", loc = ", this.locale.id, " }");
            } else {
                f.write("{ data = ", data, ", vertex = ", vertex, ", prev = ", prev!.vertex, ", loc = ", this.locale.id, " }");
            }
        }
    }

    var last_label_tracker = new map(string, shared Node/*, parSafe=true*/);

    // Component key names to be stored stored in the components map for future retrieval
    enum Component {
        SRC,            // The source of every edge in the graph, array
        SRC_R,          // Reverse of SRC (created from DST)
        DST,            // The destination of every edge in the graph, array
        DST_R,          // Reverse of DST (created from SRC)
        START_IDX,      // The starting index of every vertex in src and dst
        START_IDX_R,    // Reverse of START_IDX
        NEIGHBOR,       // Number of neighbors for a vertex  
        NEIGHBOR_R,     // Number of neighbors for a vertex based on the reversed arrays
        EDGE_WEIGHT,    // Edge weights
        EDGE_WEIGHT_R,  // Edge weights reversed for undirected graphs
        NODE_MAP,       // Index of remapped arrow pointing to original node value
        NODE_MAP_R,     // Original node value as key pointing to index in the stored graph
        RELATIONSHIPS,  // The relationships that belong to specific edges
        NODE_LABELS,    // Any labels that belong to a specific node
        NODE_PROPS,     // Any properties that belong to a specific node
        EDGE_PROPS,     // Any properties that belong to a specific edge
        DIP_SLL_RELATIONSHIPS,  // The relationships that belong to specific edges
        DIP_SLL_NODE_LABELS,    // Any labels that belong to a specific node
        DIP_SLL_NODE_PROPS,     // Any properties that belong to a specific node
        DIP_SLL_EDGE_PROPS,     // Any properties that belong to a specific edge
        DIP_DLL_RELATIONSHIPS,  // The relationships that belong to specific edges
        DIP_DLL_NODE_LABELS,    // Any labels that belong to a specific node
        DIP_DLL_NODE_PROPS,     // Any properties that belong to a specific node
        DIP_DLL_EDGE_PROPS,     // Any properties that belong to a specific edge
        DIP_ARR_RELATIONSHIPS,  // The relationships that belong to specific edges
        DIP_ARR_NODE_LABELS,    // Any labels that belong to a specific node
        DIP_ARR_NODE_PROPS,     // Any properties that belong to a specific node
        DIP_ARR_EDGE_PROPS,     // Any properties that belong to a specific edge
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

        // The graph is directed (True) or undirected (False)
        var directed : bool;

        // The graph is weighted (True) or unweighted (False)
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

    proc toSymEntryAD(e) {
        return try! e : borrowed SymEntryAD();
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
}