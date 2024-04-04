module GraphArray {

    // Chapel modules.
    use Map;
    use Reflection;
    use Utils;

    // Arkouda modules.
    use Logging;
    use MultiTypeSymEntry;
    use MultiTypeSymbolTable;

    use AryUtil;
    use ServerConfig;
    use Reflection;
    use ServerErrors;
    use NumPyDType;
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





        SRC,                    // The source array of every edge in the graph
        DST,                    // The destination array of every edge in the graph
        SEGMENTS,               // The segments of adjacency lists for each vertex in DST
        RANGES,                 // Keeps the range of the vertices the edge list stores per locale
        EDGE_WEIGHT,            // Stores the edge weights of the graph, if applicable
        NODE_MAP,               // Doing an index of NODE_MAP[u] gives you the original value of u
        VERTEX_LABELS_MAP,      // Sorted array of vertex labels to integer id (array index)
        EDGE_RELATIONSHIPS_MAP, // Sorted array of edge relationships to integer id (array index)
        VERTEX_PROPS_COL_MAP,   // Sorted array of vertex property to integer id (array index)
        VERTEX_PROPS_DTYPE_MAP, // Sorted array of column datatype to integer id (array index)
        VERTEX_PROPS_COL2DTYPE, // Map of column names to the datatype of the column
        EDGE_PROPS_COL_MAP,     // Sorted array of edge property to integer id (array index)
        EDGE_PROPS_DTYPE_MAP,   // Sorted array of column datatype to integer id (array index)
        EDGE_PROPS_COL2DTYPE,   // Map of column names to the datatype of the column

        // TEMPORARY COMPONENTS BELOW FOR UNDIRECTED GRAPHS TO ENSURE COMPATIBILTIY WITH OLD CODE.
        // We want to phase out the need for reversed arrays in undirected graph algorithms.
        // Includes: connected components, triangle counting, k-truss, and triangle centrality.
        SRC_R,                  // DST array
        DST_R,                  // SRC array
        START_IDX,              // Starting indices of vertices in SRC
        START_IDX_R,            // Starting indices of vertices in SRC_R
        NEIGHBOR,               // Number of neighbors for a given vertex based off SRC and DST
        NEIGHBOR_R,             // Number of neighbors for a given vertex based off SRC_R and DST_R
        VERTEX_WEIGHT, // Vertex weight



        A_SRC_R,        // Reverse of SRC, aligned array based on srcR
        A_DST_R,        // Reverse of DST, aligned array based on dstR
        A_START_IDX,              // Starting indices of vertices in SRC
        A_START_IDX_R,            // Starting indices of vertices in SRC_R
        A_NEIGHBOR,               // Number of neighbors for a given vertex based off SRC and DST
        A_NEIGHBOR_R,             // Number of neighbors for a given vertex based off SRC_R and DST_R
        A_VERTEX_WEIGHT, // Vertex weight
        VTrack,        // track the vertex ID from the normalized ID to the original ID
        VP1,        // The first vertex property
        VP2,        // The second vertex property
        EP1,        // The first edge property
        EP2         // The second edge property
    }

    pragma "default intent is ref"
    record DomArray {
         var DO = {0..0};
         var A : [DO] int;
         proc ref new_dom(ref new_d : domain(1)) {
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


        // The graph is directed (true) or undirected (false)
        var directed : bool;

        // The graph is weighted (true) or unweighted (false)
        var weighted: bool;



        /**
        * Init the basic graph object, we'll compose the pieces using the withComp method.
        */
        proc init(num_v:int, num_e:int, directed:bool) {
            this.n_vertices = num_v;
            this.n_edges = num_e;
            this.directed = directed;
            this.weighted = false;
        }
        proc init(num_v:int, num_e:int, directed:bool, weighted:bool ) {
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






        /* Use the withCOMPONENT methods to compose the graph object */
        proc withEnumCom(a:shared GenSymEntry, atrname:Component):SegGraph { components.add(atrname, a); return this; }
        proc hasEnumCom( atrname:Component):bool {return components.contains(atrname); } 
        proc getEnumCom( atrname:Component){return components[getBorrowed(atrname)]; } 
        proc withATR(a:shared GenSymEntry, atrname:int):SegGraph { 
                    components.add(atrname, a); 
            return this; 
        }
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
        

        proc getSRC() throws { return components[(Component.SRC)]; }
        proc getSRC_R()  throws{ return components[(Component.SRC_R)]; }
        proc getDST() throws { return components[Component.DST]; }
        proc getDST_R() throws { return components[Component.DST_R]; }
        proc getSTART_IDX() throws { return components[Component.START_IDX]; }
        proc getSTART_IDX_R() throws { return components[Component.START_IDX_R]; }
        proc getNEIGHBOR() throws { return components[Component.NEIGHBOR]; }
        proc getNEIGHBOR_R() throws { return components[Component.NEIGHBOR_R]; }
        proc getEDGE_WEIGHT() throws { return components[Component.EDGE_WEIGHT]; }
        proc getVERTEX_WEIGHT() throws { return components[Component.VERTEX_WEIGHT]; }
        proc getA_SRC_R() throws { return acomponents[Component.A_SRC_R]; }
        proc getA_DST_R() throws { return acomponents[Component.A_DST_R]; }
        proc getA_START_IDX() throws { return acomponents[Component.A_START_IDX]; }
        proc getA_START_IDX_R() throws { return acomponents[Component.A_START_IDX_R]; }
        proc getA_NEIGHBOR() throws { return acomponents[Component.A_NEIGHBOR]; }
        proc getA_NEIGHBOR_R() throws { return acomponents[Component.A_NEIGHBOR_R]; }

        proc withVP1(a:shared GenSymEntry):SegGraph { components.add(Component.VP1, a); return this; }
        proc withVP2(a:shared GenSymEntry):SegGraph { components.add(Component.VP2, a); return this; }
        proc withEP1(a:shared GenSymEntry):SegGraph { components.add(Component.EP1, a); return this; }
        proc withEP2(a:shared GenSymEntry):SegGraph { components.add(Component.EP2, a); return this; }
        proc hasVP1():bool { return components.contains(Component.VP1); }
        proc hasVP2():bool { return components.contains(Component.VP2); }
        proc hasEP1():bool { return components.contains(Component.EP1); }
        proc hasEP2():bool { return components.contains(Component.EP2); }
        proc getVP1() throws { return components[Component.VP1]; }
        proc getVP2() throws { return components[Component.VP2]; }
        proc getEP1() throws { return components[Component.EP1]; }
        proc getEP2() throws { return components[Component.EP2]; }


        proc withVTrack(a:shared GenSymEntry):SegGraph { components.add(Component.VTrack, a); return this; }
        proc hasVTrack():bool { return components.contains(Component.VTrack); }
        proc getVTrack() throws { return components[Component.VTrack]; }
    }

    /**
    * DomArraySymEntry is the wrapper class around DomArray record
    * so it may be stored in the Symbol Table (SymTab)
    */
    class DomArraySymEntry:CompositeSymEntry {
        var domary =makeDistArray(numLocales,DomArray);
        proc init(disArray :[?aD] DomArray) {
            super.init(0);
            //super.init(DomArray,0);
            this.entryType = SymbolEntryType.CompositeSymEntry;
            assignableTypes.add(this.entryType);
            this.domary = disArray;
        }

        override proc getSizeEstimate(): int {
            return 1;
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
    class SparseSymEntry : GenSymEntry {
        var a;
        proc etype type do return a.eltType;

        proc init(in a: []) where a.isSparse() { this.a = a; }
    }



    class ReplicatedSymEntry : GenSymEntry {
        var a;
        proc etype type do return a.eltType;

        proc init(in a: []) where isReplicatedArr(a) { this.a = a; }
    }

    class MapSymEntry : GenSymEntry {
        type left;
        type right;
        var stored_map: map(left, right);

        proc init(ref map_to_store: map(?left, ?right)) {
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
        var indicesEntry: shared SparseSymEntry(?);

        proc init(offsetsSymEntry: shared SymEntry(int), bytesSymEntry: shared SymEntry(uint(8)), indicesSymEntry: shared SparseSymEntry(?), type etype) {
            super.init(offsetsSymEntry, bytesSymEntry, etype);
            this.indicesEntry = indicesSymEntry;
        }
    }

    proc toSparsePropertySegStringSymEntry(entry: borrowed AbstractSymEntry) throws {
        return (entry: borrowed SparsePropertySegStringSymEntry);
    }





    /**
     * Convenience proc to retrieve DomArraySymEntry from SymTab
     * Performs conversion from AbstractySymEntry to DomArraySymEntry
     */
    proc getDomArraySymEntry(name:string, st: borrowed SymTab): borrowed DomArraySymEntry throws {
        var abstractEntry:borrowed AbstractSymEntry = st.lookup(name);
        if ! abstractEntry.isAssignableTo(SymbolEntryType.CompositeSymEntry) {
            var errorMsg = "Error: SymbolEntryType %s is not assignable to CompositeSymEntry".format(abstractEntry.entryType);
            graphLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            throw new Error(errorMsg);
        }
        return (abstractEntry: borrowed DomArraySymEntry);
    }

    /**
    * Helper proc to cat AbstractSymEntry to DomArraySymEntry
    */
    proc toDomArraySymEntry(entry: borrowed AbstractSymEntry): borrowed DomArraySymEntry throws {
        return (entry: borrowed DomArraySymEntry);
    }


}
