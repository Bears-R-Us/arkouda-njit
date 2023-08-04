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

    // Component key names to be stored stored in the components map for future retrieval
    enum Component {
        BI_SRC,         // Combined source of every edge
        BI_DST,         // Combined destination of every edge
        ROW_INDEX,      // Row index array of CSR


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
    }

    /**
    * We use several arrays and integers to represent a graph.
    * Instances are ephemeral, not stored in the symbol table. Instead, attributes
    * of this class refer to symbol table entries that persist. This class is a
    * convenience for bundling those persistent objects and defining graph-relevant
    * operations.
    */


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

        /* The graph is weighted (True) or unweighted (False)*/
        //var weighted : bool;




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


        /* Use the withCOMPONENT methods to compose the graph object */
        proc withEnumCom(a:shared GenSymEntry, atrname:Component):SegGraph { components.add(atrname, a); return this; }
        proc hasEnumCom( atrname:Component):bool {return components.contains(atrname); } 
        proc getEnumCom( atrname:Component){return components.getBorrowed(atrname); } 
        
    }

    /**
    * DomArraySymEntry is the wrapper class around DomArray record
    * so it may be stored in the Symbol Table (SymTab)
    */
    class DomArraySymEntry:CompositeSymEntry {
        //var dtype = NumPyDType.DType.UNDEF;
        //type etype = int;
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

    /**
    * Helper proc to cat AbstractSymEntry to GraphSymEntry
    */
    proc toGraphSymEntry(entry: borrowed AbstractSymEntry): borrowed GraphSymEntry throws {
        return (entry: borrowed GraphSymEntry);
    }


}
