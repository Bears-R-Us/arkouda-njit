module GraphArray {

    use AryUtil;
    use MultiTypeSymEntry;
    use MultiTypeSymbolTable;
    use ServerConfig;
    use Reflection;
    use Logging;
    use ServerErrors;
    use NumPyDType;
    use Map;

    private config const logLevel = LogLevel.DEBUG;
    const graphLogger = new Logger(logLevel);

    // These are the component Key names stored in our components map
    enum Component {
        SRC,          // The source of every edge in the graph,array value
        SRC_R,        // Reverse of SRC
        DST,          // The destination of every vertex in the graph,array value
        DST_R,        // Reverse of DST
        START_IDX,    // The starting index of every vertex in src and dst
        START_IDX_R,  // Reverse of START_IDX
        NEIGHBOR,     // Numer of neighbors for a vertex  
        NEIGHBOR_R,   // Numer of neighbors for a vertex based on the reverse array
        A_START_IDX,    // The starting index of every vertex in src and dst, aligned array based on src
        A_START_IDX_R,  // Reverse of START_IDX, aligned array based on src
        A_NEIGHBOR,     // Numer of neighbors for a vertex, aligned array based on src  
        A_NEIGHBOR_R,   // Numer of neighbors for a vertex based on the reverse array, aligned array based on src
        A_SRC_R,        // Reverse of SRC, aligned array based on srcR
        A_DST_R,        // Reverse of DST, aligned array based on dstR
        EDGE_WEIGHT,  // Edge weight
        VERTEX_WEIGHT // Vertex weight
    }

    pragma "default intent is ref"
    record DomArray {
         var DO = {0..0};
         var A : [DO] int;
         proc new_dom(new_d : domain(1)) {
             this.DO = new_d;
         }
    }


    /**
    * We use several arrays and intgers to represent a graph 
    * Instances are ephemeral, not stored in the symbol table. Instead, attributes
    * of this class refer to symbol table entries that persist. This class is a
    * convenience for bundling those persistent objects and defining graph-relevant
    * operations.
    * Now we  copy from SegSArray, we need change more in the future to fit a graph
    */
    class SegGraph {

        /* Map to hold various components of our Graph; use enum Component values as map keys */
        var components = new map(Component, shared GenSymEntry, parSafe=false);

        var acomponents = new map(Component, shared CompositeSymEntry, parSafe=false);


        /* Total number of vertices */
        var n_vertices : int;

        /* Total number of edges */
        var n_edges : int;

        /* The graph is directed (True) or undirected (False)*/
        var directed : bool;

        /**
        * Init the basic graph object, we'll compose the pieces in
        * using the withCOMPONENT methods.
        */
        proc init(num_v:int, num_e:int, directed:bool) {
            this.n_vertices = num_v;
            this.n_edges = num_e;
            this.directed = directed;
        }

        proc isDirected():bool { return this.directed; }

        /* Use the withCOMPONENT methods to compose the graph object */
        proc withSRC(a:shared GenSymEntry):SegGraph { components.add(Component.SRC, a); return this; }
        proc withSRC_R(a:shared GenSymEntry):SegGraph { components.add(Component.SRC_R, a); return this; }
        
        proc withDST(a:shared GenSymEntry):SegGraph { components.add(Component.DST, a); return this; }
        proc withDST_R(a:shared GenSymEntry):SegGraph { components.add(Component.DST_R, a); return this; }
        
        proc withSTART_IDX(a:shared GenSymEntry):SegGraph { components.add(Component.START_IDX, a); return this; }
        proc withSTART_IDX_R(a:shared GenSymEntry):SegGraph { components.add(Component.START_IDX_R, a); return this; }

        proc withNEIGHBOR(a:shared GenSymEntry):SegGraph { components.add(Component.NEIGHBOR, a); return this; }
        proc withNEIGHBOR_R(a:GenSymEntry):SegGraph { components.add(Component.NEIGHBOR_R, a); return this; }

        proc withEDGE_WEIGHT(a:shared GenSymEntry):SegGraph { components.add(Component.EDGE_WEIGHT, a); return this; }
        proc withVERTEX_WEIGHT(a:shared GenSymEntry):SegGraph { components.add(Component.VERTEX_WEIGHT, a); return this; }

        proc withA_SRC_R(a:shared CompositeSymEntry):SegGraph { acomponents.add(Component.A_SRC_R, a); return this; }
        proc withA_DST_R(a:shared CompositeSymEntry):SegGraph { acomponents.add(Component.A_DST_R, a); return this; }
        proc withA_START_IDX(a:shared CompositeSymEntry):SegGraph {acomponents.add(Component.A_START_IDX, a);return this; }
        proc withA_START_IDX_R(a:shared CompositeSymEntry):SegGraph {acomponents.add(Component.A_START_IDX_R, a);return this; }
        proc withA_NEIGHBOR(a:shared CompositeSymEntry):SegGraph { acomponents.add(Component.A_NEIGHBOR, a); return this; }
        proc withA_NEIGHBOR_R(a:shared CompositeSymEntry):SegGraph {acomponents.add(Component.A_NEIGHBOR_R, a);return this;}


        proc hasSRC():bool { return components.contains(Component.SRC); }
        proc hasSRC_R():bool { return components.contains(Component.SRC_R); }
        proc hasDST():bool { return components.contains(Component.DST); }
        proc hasDST_R():bool { return components.contains(Component.DST_R); }
        proc hasSTART_IDX():bool { return components.contains(Component.START_IDX); }
        proc hasSTART_IDX_R():bool { return components.contains(Component.START_IDX_R); }
        proc hasNEIGHBOR():bool { return components.contains(Component.NEIGHBOR); }
        proc hasNEIGHBOR_R():bool { return components.contains(Component.NEIGHBOR_R); }
        proc hasEDGE_WEIGHT():bool { return components.contains(Component.EDGE_WEIGHT); }
        proc hasVERTEX_WEIGHT():bool { return components.contains(Component.VERTEX_WEIGHT); }

        proc hasA_SRC_R():bool { return acomponents.contains(Component.A_SRC_R); }
        proc hasA_DST_R():bool { return acomponents.contains(Component.A_DST_R); }
        proc hasA_START_IDX():bool { return acomponents.contains(Component.A_START_IDX); }
        proc hasA_START_IDX_R():bool { return acomponents.contains(Component.A_START_IDX_R); }
        proc hasA_NEIGHBOR():bool { return acomponents.contains(Component.A_NEIGHBOR); }
        proc hasA_NEIGHBOR_R():bool { return acomponents.contains(Component.A_NEIGHBOR_R); }
        
        proc getSRC() { return components.getBorrowed(Component.SRC); }
        proc getSRC_R() { return components.getBorrowed(Component.SRC_R); }
        proc getDST() { return components.getBorrowed(Component.DST); }
        proc getDST_R() { return components.getBorrowed(Component.DST_R); }
        proc getSTART_IDX() { return components.getBorrowed(Component.START_IDX); }
        proc getSTART_IDX_R() { return components.getBorrowed(Component.START_IDX_R); }
        proc getNEIGHBOR() { return components.getBorrowed(Component.NEIGHBOR); }
        proc getNEIGHBOR_R() { return components.getBorrowed(Component.NEIGHBOR_R); }
        proc getEDGE_WEIGHT() { return components.getBorrowed(Component.EDGE_WEIGHT); }
        proc getVERTEX_WEIGHT() { return components.getBorrowed(Component.VERTEX_WEIGHT); }
        proc getA_SRC_R() { return acomponents.getBorrowed(Component.A_SRC_R); }
        proc getA_DST_R() { return acomponents.getBorrowed(Component.A_DST_R); }
        proc getA_START_IDX() { return acomponents.getBorrowed(Component.A_START_IDX); }
        proc getA_START_IDX_R() { return acomponents.getBorrowed(Component.A_START_IDX_R); }
        proc getA_NEIGHBOR() { return acomponents.getBorrowed(Component.A_NEIGHBOR); }
        proc getA_NEIGHBOR_R() { return acomponents.getBorrowed(Component.A_NEIGHBOR_R); }

    }

    /**
    * DomArraySymEntry is the wrapper class around DomArray record
    * so it may be stored in the Symbol Table (SymTab)
    */
    class DomArraySymEntry:CompositeSymEntry {
        var dtype = NumPyDType.DType.UNDEF;
        var domary =makeDistArray(numLocales,DomArray);

        proc init(disArray :[?aD] DomArray) {
            super.init();
            this.entryType = SymbolEntryType.CompositeSymEntry;
            assignableTypes.add(this.entryType);
            this.domary = disArray;
        }
    }

    /**
    * GraphSymEntry is the wrapper class around SegGraph
    * so it may be stored in the Symbol Table (SymTab)
    */
    class GraphSymEntry:CompositeSymEntry {
        var dtype = NumPyDType.DType.UNDEF;
        var graph: shared SegGraph;

        proc init(segGraph: shared SegGraph) {
            super.init();
            this.entryType = SymbolEntryType.CompositeSymEntry;
            assignableTypes.add(this.entryType);
            this.graph = segGraph;
        }
    }

    /**
     * Convenience proc to retrieve GraphSymEntry from SymTab
     * Performs conversion from AbstractySymEntry to GraphSymEntry
     */
    proc getGraphSymEntry(name:string, st: borrowed SymTab): borrowed GraphSymEntry throws {
        var abstractEntry:borrowed AbstractSymEntry = st.lookup(name);
        if ! abstractEntry.isAssignableTo(SymbolEntryType.CompositeSymEntry) {
            var errorMsg = "Error: SymbolEntryType %s is not assignable to CompositeSymEntry".format(abstractEntry.entryType);
            graphLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            throw new Error(errorMsg);
        }
        return (abstractEntry: borrowed GraphSymEntry);
    }

    /**
    * Helper proc to cat AbstractSymEntry to DomArraySymEntry
    */
    proc toDomArraySymEntry(entry: borrowed AbstractSymEntry): borrowed DomArraySymEntry throws {
        return (entry: borrowed DomArraySymEntry);
    }

    /**
    * Helper proc to cat AbstractSymEntry to GraphSymEntry
    */
    proc toGraphSymEntry(entry: borrowed AbstractSymEntry): borrowed GraphSymEntry throws {
        return (entry: borrowed GraphSymEntry);
    }


}
