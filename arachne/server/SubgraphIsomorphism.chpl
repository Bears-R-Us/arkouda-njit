module SubgraphIsomorphism {
    // Chapel modules.
    use Reflection;
    use List;
    use Random;
    use List;
    use IO;
    use Time;
    use Set;
    use Map;
    use Sort;

    // Arachne modules.
    use GraphArray;
    use Utils;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use AryUtil;
    use SegStringSort;
    use SegmentedString;

    /** Keeps track of the isomorphic mapping state during the execution process of VF2.*/
    record State {
        var n1: int; // size of main graph
        var n2: int; // size of subgraph
    
        var D_core: domain(1) = {0..<n2};
        var core: [0..<n2] int;
        
        var Tin1: domain(int); // in-neighbors of current state for main graph
        var Tout1: domain(int); // out-neighbors of current state for main graph

        var Tin2: domain(int); // in-neighbors of current state for subgraph
        var Tout2: domain(int); // out-neighbors of current state for subgraph
        
        var depth:int; // recursion depth, when depth == n2 then all vertices are mapped.

        /** State initializer.*/
        proc init(n1: int, n2: int) {
            this.n1 = n1;
            this.n2 = n2;
            
            this.D_core = {0..<n2};
            this.core = -1;
            
            this.Tin1 = {1..0};
            this.Tout1 = {1..0};
            
            this.Tin2 = {1..0};
            this.Tout2 = {1..0};
            
            this.depth = 0;
        }
        
        /** Reset vectors during backtracking.*/
        proc reset() {
            this.D_core = {0..1};
            this.core = -1;

            this.Tin1  =  {1..0};
            this.Tout1 =  {1..0};

            this.Tin2  =  {1..0};
            this.Tout2 =  {1..0};

            this.depth = 0;
        }
        
        /** Method to create a copy of the instance.*/
        proc clone(): State throws {
            var newState = new State(this.n1, this.n2);
            newState.core = this.core;

            newState.Tin1 = this.Tin1;
            newState.Tout1 = this.Tout1;
            
            newState.Tin2 = this.Tin2;
            newState.Tout2 = this.Tout2;
            
            newState.depth = this.depth;

            return newState;
        }

        /** Check if a given node is mapped in g1.*/
        proc isMappedn1(n1: int): bool {
            var Mapflag: bool = false;
            for i in D_core do if this.core[i] == n1 then Mapflag = true;
            return Mapflag;
        }
        
        /** Check if a given node is mapped in g2.*/
        proc isMappedn2(n2: int): bool {
            return (this.core[n2] != -1);
        }

    } // end of State class 
    
    // Define a sync variable to control access to the stack
    var stackMutex: sync bool = false;

    class ThreadSafeStack {
    var stack: list(State);
    var lock: sync bool;

    proc init() {
        writeln("ThreadSafeStack.init()");
        this.stack = new list(State);
        this.lock = true; // Initialize the sync variable to empty
    }

    proc pushBack(state: State) {
        writeln("ThreadSafeStack.pushBack()");

        this.lock.writeEF(false); // Ensure exclusive access
        this.stack.pushBack(state);
        this.lock.writeXF(true); // Release exclusive access
    }

    proc popBack(): State {
        writeln("ThreadSafeStack.popBack()");

        this.lock.writeEF(false); // Ensure exclusive access
        var state = this.stack.popBack();
        this.lock.writeXF(true); // Release exclusive access
        return state;
    }

    proc size(): int {
        writeln("ThreadSafeStack.size()");

        this.lock.readFE(); // Ensure exclusive access
        var size = this.stack.size;
        this.lock = true; // Release the lock
        return size;
    }

    proc isEmpty(): bool {
        writeln("ThreadSafeStack.isEmpty()");

        this.lock.readFE(); // Ensure exclusive access
        var isEmpty = this.stack.size == 0;
        this.lock = true; // Release the lock
        return isEmpty;
    }
    }
    /** Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
    searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
    array that maps the isomorphic vertices of `g1` to those of `g2`.*/
    proc runVF2 (g1: SegGraph, g2: SegGraph, st: borrowed SymTab):[] int throws {
        var TimerArrNew:[0..30] real(64) = 0.0;
        var numIso: int = 0;

        // Extract the g1/G/g information from the SegGraph data structure.
        var srcNodesG1Dist = toSymEntry(g1.getComp("SRC"), int).a;
        var dstNodesG1Dist = toSymEntry(g1.getComp("DST"), int).a;
        var segGraphG1Dist = toSymEntry(g1.getComp("SEGMENTS"), int).a;
        var srcRG1Dist = toSymEntry(g1.getComp("SRC_R"), int).a;
        var dstRG1Dist = toSymEntry(g1.getComp("DST_R"), int).a;
        var segRG1Dist = toSymEntry(g1.getComp("SEGMENTS_R"), int).a;
        var nodeMapGraphG1Dist = toSymEntry(g1.getComp("VERTEX_MAP"), int).a;

        // Extract the g2/H/h information from the SegGraph data structure.
        var srcNodesG2Dist = toSymEntry(g2.getComp("SRC"), int).a;
        var dstNodesG2Dist = toSymEntry(g2.getComp("DST"), int).a;
        var segGraphG2Dist = toSymEntry(g2.getComp("SEGMENTS"), int).a;
        var srcRG2Dist = toSymEntry(g2.getComp("SRC_R"), int).a;
        var dstRG2Dist = toSymEntry(g2.getComp("DST_R"), int).a;
        var segRG2Dist = toSymEntry(g2.getComp("SEGMENTS_R"), int).a;
        var nodeMapGraphG2Dist = toSymEntry(g2.getComp("VERTEX_MAP"), int).a;

        // Get the number of vertices and edges for each graph.
        var nG1 = nodeMapGraphG1Dist.size;
        var mG1 = srcNodesG1Dist.size;
        var nG2 = nodeMapGraphG2Dist.size;
        var mG2 = srcNodesG2Dist.size;

        //******************************************************************************************
        //******************************************************************************************
        // OLIVER NOTE: 
        // Relabeled node labels and edge relationships id values so those of H match those of G to 
        // speed up semantic checks. 
        // 
        // In the SegGraph data structure for property graphs, there could be many different types 
        // of labels and relationships. Therefore, we will do some preprocessing here to relabel
        // all labels and relationships and place them into sets for quick intersections.
        //
        // This assumes that all labels and relationships are strings BUT some labels and 
        // relationships can be unsigned or regular integers. If this is the case then borrowed 
        // SegStringSymEntry below would be empty. We currently do not do a check for this since all
        // of our test data has string labels and relationships BUT we should fix this in the 
        // future. 
        //
        // All of the code contained between the //**** comments (roughly ~100 lines) should
        // probably eventually be a function that lives where SegGraph is defined to perform a 
        // globalized relabeling and creating arrays of sets to speed up comparing the labels and
        // relationships of two or more different graphs.
        var edgeRelationshipsGraphG1 = (g1.getComp("EDGE_RELATIONSHIPS"):(borrowed MapSymEntry(
                                            string, (string, borrowed SegStringSymEntry)
                                        ))).stored_map;
        var nodeLabelsGraphG1 = (g1.getComp("VERTEX_LABELS"):(borrowed MapSymEntry(
                                            string, (string, borrowed SegStringSymEntry)
                                        ))).stored_map;

        var edgeRelationshipsGraphG2 = (g2.getComp("EDGE_RELATIONSHIPS"):(borrowed MapSymEntry(
                                            string, (string, borrowed SegStringSymEntry)
                                        ))).stored_map;
        var nodeLabelsGraphG2 = (g2.getComp("VERTEX_LABELS"):(borrowed MapSymEntry(
                                            string, (string, borrowed SegStringSymEntry)
                                        ))).stored_map;

        var relationshipStringToInt, labelStringToInt = new map(string, int);

        // Create global relationship mapper for G1 and G2.
        var id = 0;
        for k in edgeRelationshipsGraphG1.keys() {
            var segString = getSegString(edgeRelationshipsGraphG1[k][1].name, st);
            for i in 0..segString.size-1 {
                var val = segString[i];
                if !relationshipStringToInt.contains(val) {
                    relationshipStringToInt.add(val, id);
                    id += 1;
                }
            }
        }
        for k in edgeRelationshipsGraphG2.keys() {
            var segString = getSegString(edgeRelationshipsGraphG2[k][1].name, st);
            for i in 0..edgeRelationshipsGraphG2[k][1].size-1 {
                var val = segString[i];
                if !relationshipStringToInt.contains(val) {
                    relationshipStringToInt.add(val, id);
                    id += 1;
                }
            }
        }
        
        // Create global label mapper for G1 and G2.
        id = 0;
        for k in nodeLabelsGraphG1.keys() {
            var segString = getSegString(nodeLabelsGraphG1[k][1].name, st);
            for i in 0..nodeLabelsGraphG1[k][1].size-1 {
                var val = segString[i];
                if !labelStringToInt.contains(val) {
                    labelStringToInt.add(val, id);
                    id += 1;
                }
            }
        }
        for k in nodeLabelsGraphG2.keys() {
            var segString = getSegString(nodeLabelsGraphG2[k][1].name, st);
            for i in 0..nodeLabelsGraphG2[k][1].size-1 {
                var val = segString[i];
                if !labelStringToInt.contains(val) {
                    labelStringToInt.add(val, id);
                    id += 1;
                }
            }
        }

        // Create new "arrays of sets" to make semantic checks quicker by allowing usage of Chapel's
        // internal hash table intersections via sets.
        var convertedRelationshipsG1Dist = makeDistArray(g1.n_edges, domain(int));
        var convertedRelationshipsG2Dist = makeDistArray(g2.n_edges, domain(int));
        var convertedLabelsG1Dist = makeDistArray(g1.n_vertices, domain(int));
        var convertedLabelsG2Dist = makeDistArray(g2.n_vertices, domain(int));

        for (k,v) in zip(edgeRelationshipsGraphG1.keys(), edgeRelationshipsGraphG1.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedRelationshipsG1Dist[i].add(relationshipStringToInt[mapper[x]]);
        }

        for (k,v) in zip(edgeRelationshipsGraphG2.keys(), edgeRelationshipsGraphG2.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do
                convertedRelationshipsG2Dist[i].add(relationshipStringToInt[mapper[x]]);
        }

        for (k,v) in zip(nodeLabelsGraphG1.keys(), nodeLabelsGraphG1.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedLabelsG1Dist[i].add(labelStringToInt[mapper[x]]);
        }

        for (k,v) in zip(nodeLabelsGraphG2.keys(), nodeLabelsGraphG2.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedLabelsG2Dist[i].add(labelStringToInt[mapper[x]]);
        }
        //******************************************************************************************
        //******************************************************************************************

        //************************************LOCALIZATION******************************************
        var srcNodesG1: [0..<mG1] int = srcNodesG1Dist;
        var dstNodesG1: [0..<mG1] int = dstNodesG1Dist;
        var segGraphG1: [0..<nG1+1] int = segGraphG1Dist;
        var srcRG1: [0..<mG1] int = srcRG1Dist;
        var dstRG1: [0..<mG1] int = dstRG1Dist;
        var segRG1: [0..<nG1+1] int = segRG1Dist;
        var nodeMapGraphG1: [0..<nG1] int = nodeMapGraphG1Dist;
        var convertedRelationshipsG1: [0..<mG1] domain(int) = convertedRelationshipsG1Dist;
        var convertedLabelsG1: [0..<nG1] domain(int) = convertedLabelsG1Dist;

        var srcNodesG2: [0..<mG2] int = srcNodesG2Dist;
        var dstNodesG2: [0..<mG2] int = dstNodesG2Dist;
        var segGraphG2: [0..<nG2+1] int = segGraphG2Dist;
        var srcRG2: [0..<mG2] int = srcRG2Dist;
        var dstRG2: [0..<mG2] int = dstRG2Dist;
        var segRG2: [0..<nG2+1] int = segRG2Dist;
        var nodeMapGraphG2: [0..<nG2] int = nodeMapGraphG2Dist;
        var convertedRelationshipsG2: [0..<mG2] domain(int) = convertedRelationshipsG2Dist;
        var convertedLabelsG2: [0..<nG2] domain(int) = convertedLabelsG2Dist;
        //******************************************************************************************
        //writeln("srcNodesG1 = ", srcNodesG1);
        //writeln("dstNodesG1 = ", dstNodesG1); 
        
        //writeln("\nsegGraphG1 = ", segGraphG1);
        
        //writeln("\nsrcRG1 = ", srcRG1); 
        //writeln("dstRG1 = ", dstRG1);

        //writeln("\nsegRG1 = ", segRG1);
        /*
        var candidatesStru = new set((int, int), parSafe = true);
        var timer2:stopwatch;
        timer2.start();

         

        forall v in 0..<g1.n_vertices with(ref candidatesStru){
            var inNeighborsg1 = dstRG1[segRG1[v]..<segRG1[v+1]];            
            var outNeighborsg1 = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];


            if (inNeighborsg1.size >= 1) && (outNeighborsg1.size >= 2){
                //writeln("\nCandidate found = ", v);
                candidatesStru.add((v, 1));
            }
        }
        timer2.stop();
        writeln(" timer2 = ", timer2.elapsed());
        */
        writeln("runVF2 after loading everything\n\n");
         
        //var ffcandidates = findOutEdges();
        //var ffcandidates = findOutWedgesLight();
        //var ffstates = CandidToState(ffcandidates);
        var IsoArrtemp = vf2(g1, g2);
        /*
        //writeln("IsoArrtemp Divisiblity test = ", IsoArrtemp.size/4);
        
        for i in 0..g1.n_vertices {
            if !(IsoArrtemp[i] > -1 && IsoArrtemp[i] < g1.n_vertices+1){
                writeln("There is an out of range ", IsoArrtemp[i]);
            }
        }
        */
        var IsoArr = nodeMapGraphG1[IsoArrtemp]; // Map vertices back to original values.
        
        //writeln("\nIsoArr Divisiblity test = ", IsoArr.size/4);

        //writeln("IsoArr     = ", IsoArr);
        writeln("\n_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*");
        
        //writeln("\nDomain check = ", IsoArrtemp.domain == IsoArr.domain );
        //writeln("\nEquality check = ",IsoArrtemp.equals(IsoArr));
/////////////////////////////State Injection//////////////////////////////////////////
        proc CandidToState(ffcandidates) throws{
            //var StateList: list(owned State) = new list(owned State);
            var StateList: list(owned State);
            forall n1Arr in ffcandidates with (ref StateList) {
                
                var newState = addToTinToutArray(n1Arr);
                //writeln("state added: ", newState );

                StateList.pushBack(newState);
            }
            return (StateList);
        }
        
        proc findOutWedgesLight()throws {
            var outWedges: list(int, parSafe=true);
            
            var inNeighborsg2 = dstRG2[segRG2[0]..<segRG2[1]];            
            var outNeighborsg2 = dstNodesG2[segGraphG2[0]..<segGraphG2[1]];
            
            writeln("Index 0 in G2 has ",inNeighborsg2.size, " inNeighbors" );
            writeln("Index 0 in G2 has ",outNeighborsg2.size, " outNeighbors" );
            // Iterate over each node and its out-neighbors
            forall u in 0..g1.n_vertices-1 with (ref outWedges) {
            //for u in 0..g1.n_vertices-1 {
                var outNeighborsg1 = dstNodesG1.localSlice(segGraphG1[u]..<segGraphG1[u+1]);
                var inNeighborsg1 = dstRG1[segRG1[u]..<segRG1[u+1]];

                if outNeighborsg1.size >= outNeighborsg2.size & inNeighborsg1.size >= inNeighborsg2.size{
                    outWedges.pushBack(u); 
                }
            }
            writeln("/////////////////////////////State Injection//////////////////////////////////////////");
            writeln("g1 num vertices is : ",g1.n_vertices );
            writeln("outWedges size is: ", outWedges.size);
            return(outWedges);
        }
/////////////////////////////End of State Injection///////////////////////////////////
        
//////////////////////////RI///////////////////////////////////////////////////
        proc SortSubGraphbyDegree():[] int throws{
            var NodeDegree:[0..<g2.n_vertices] int = 0;
            writeln("inNeighborsg2 dstRG2 = ", dstRG2);
            writeln("segRG2 = ", segRG2);
            
            
            writeln("\n\noutNeighborsg2 dstNodesG2 = ", dstNodesG2);
            writeln("segGraphG2 = ", segGraphG2);

            for v in 0..<g2.n_vertices{
                var inNeighborsg2 = dstRG2[segRG2[v]..<segRG2[v+1]];            
                var outNeighborsg2 = dstNodesG2[segGraphG2[v]..<segGraphG2[v+1]];
                writeln("v = ", v);
                writeln("inNeighbors = ", inNeighborsg2);
                writeln("outNeighbors = ", outNeighborsg2);

                NodeDegree[v]= inNeighborsg2.size + outNeighborsg2.size;
            }

            // Create an array of tuples (value, original index)
            var zipped: [NodeDegree.domain] (int, int);

            // Populate the zipped array
            for i in NodeDegree.domain {
                zipped[i] = (NodeDegree[i], i);
            }
            // Define a custom comparator for sorting tuples
            record Comparator { 
                proc compare(a: (int, int), b: (int, int)) {
                    // Return the difference between the first elements of the tuples
                    return b(0) - a(0);
                }
            }

            var TupleComparator: Comparator;

            // Sort the zipped array using a lambda function as the comparator
            sort(zipped, comparator=TupleComparator);

            // Extract the sorted array and the indices
            var sortedArray: [NodeDegree.domain] int;
            var sortedIndices: [NodeDegree.domain] int;
            for i in NodeDegree.domain{
                sortedArray[i] = zipped[i](0);
                sortedIndices[i] = zipped[i](1);
            }

            // Print the results
            writeln("Sorted array: ", sortedArray);
            writeln("Original indices of sorted elements: ", sortedIndices);
            return (sortedIndices);
        }      
        //SortSubGraphbyDegree();
        
        
        proc GreatestConstraintFirst() throws {
            var u_0: int = -1;
            var V: set(int);
            for i in 0..<g2.n_vertices{
                V.add(i);
            }    

            var Visited: [0..<g2.n_vertices] bool = false; 
            var Miu:list(int) ; 
            var ParentMiu:list(int) ; 
            var step: int = 0;
            var uRank: [0..2] int;
            var u_m: int = -1;


            var sortedIndices = SortSubGraphbyDegree();

            u_0 = sortedIndices[0]; //Vertex u0 in the subgraph is the maximum (in + out degree) 
            writeln("u_0 = ", u_0);
            Miu.pushBack(u_0);
            writeln("Miu = ", Miu);

            Visited(u_0) = true;
            writeln("Visited = ", Visited);

            ParentMiu.pushBack(-1);
            uRank = (-1, -1, -1);

            V.remove(u_0);
            writeln("V after removing u_0 = ", V);
            writeln("Begining of the while");
            //var counter =10;
            while(V.size > 0 ) {
                var m = Miu.size;
                writeln("m is = ", m);


                for u in 0..<g2.n_vertices {
                    var V_u_vis :int = 0;
                    var V_u_neig :int = 0;
                    var V_u_unvis :int = 0;
                    
                    writeln("\nbegingig of the for With u = ", u);
                    var inNeighborsg2_u = dstRG2[segRG2[u]..<segRG2[u+1]];            
                    var outNeighborsg2_u = dstNodesG2[segGraphG2[u]..<segGraphG2[u+1]];
                    //writeln("inNeighborsg2_u = ", inNeighborsg2_u);
                    //writeln("outNeighborsg2_u = ", outNeighborsg2_u);

                    if(Visited[u] == false) {
                       writeln("Visited = ", Visited);
                       writeln("u = ",u," is not visited");
                       writeln("before loop Miu = ",Miu);

                        //V_{u, vis}
                        
                        for MiuVal in Miu {
                            writeln("here V_{u, vis} = ", MiuVal);
                            //writeln("inNeighborsg2_u.find(MiuVal) = ", inNeighborsg2_u.find(MiuVal));
                            //writeln("outNeighborsg2_u .find(MiuVal) = ", outNeighborsg2_u .find(MiuVal));
                            if inNeighborsg2_u.find(MiuVal)!= -1 || outNeighborsg2_u .find(MiuVal) != -1{
                            V_u_vis += 1 ;
                            writeln("V_u_vis =", V_u_vis);
                            }
                        }
                        //V_{u, neig}
                        writeln("******************end of V_u_vis***************************\n");

                        for MiuVal in Miu {
                            writeln("here V_{u, neig} ", MiuVal);

                            var inNeighborsg2_MiuVal = dstRG2[segRG2[MiuVal]..<segRG2[MiuVal+1]];            
                            var outNeighborsg2_MiuVal = dstNodesG2[segGraphG2[MiuVal]..<segGraphG2[MiuVal+1]];
                            
                            var combinedSet_MiuVal: set(int);
                            // Add elements of in-neigh to the set
                            for elem in inNeighborsg2_MiuVal {
                                combinedSet_MiuVal.add(elem);
                            }

                            // Add elements of out-neigh to the set
                            for elem in outNeighborsg2_MiuVal {
                                combinedSet_MiuVal.add(elem);
                            }
                            writeln("combinedSet_MiuVal = ", combinedSet_MiuVal);
                            var combinedSet_u: set(int);
                            
                            // Add elements of arr1 to the set
                            for elem in inNeighborsg2_u {
                                combinedSet_u.add(elem);
                            }

                            // Add elements of arr2 to the set
                            for elem in outNeighborsg2_u {
                                combinedSet_u.add(elem);
                            }
                            writeln("combinedSet_u = ", combinedSet_u);

                            // Find the intersection of the two sets
                            var intersection = combinedSet_MiuVal & combinedSet_u;
                            writeln("intersection = ", intersection);

                            for elem in intersection {
                                if Visited[elem] == false{
                                    V_u_neig += 1;
                                }
                            }
                            writeln("V_u_neig = ",V_u_neig );
                            writeln("******************end of V_u_neig***************************\n");
                        }
                        //V_{u, unvis}
                        var setMiu: set(int);
                        for elem in Miu {
                            setMiu.add(elem);
                            var inNeighborsg2_MiuVal = dstRG2[segRG2[elem]..<segRG2[elem+1]];            
                            var outNeighborsg2_MiuVal = dstNodesG2[segGraphG2[elem]..<segGraphG2[elem+1]];
                            for elem in inNeighborsg2_MiuVal {
                                setMiu.add(elem);
                            }                            
                            
                            for elem in outNeighborsg2_MiuVal {
                                setMiu.add(elem);
                            }
                        }

                        for i in 0..<g2.n_vertices {
                            if Visited[i] == false{
                                for elem in inNeighborsg2_u {
                                    if !setMiu.contains(elem) {
                                        V_u_unvis += 1;
                                    }
                                }
                                for elem in outNeighborsg2_u {
                                    if !setMiu.contains(elem) {
                                        V_u_unvis += 1;
                                    }
                                }
                            }
                        }
                        writeln("V_u_unvis = ", V_u_unvis);
                            writeln("******************end of V_u_unvis***************************\n");

                    }

                    if(V_u_vis > uRank[0]) {
                        writeln("Here 1 checked");
                        u_m = u;
                        uRank[0] = V_u_vis;
                        uRank[1] = V_u_neig;
                        uRank[2] = V_u_unvis;
                        writeln("Now u_m = " , u_m, " uRank changed to = ", uRank);
                    }
                    else if(V_u_vis == uRank[0]) {
                        if(V_u_neig > uRank[1]) {
                            writeln("Here 2 checked");

                            u_m = u;
                            uRank[0] = V_u_vis;
                            uRank[1] = V_u_neig;
                            uRank[2] = V_u_unvis;
                        writeln("Now u_m = " , u_m, "uRank changed to = ", uRank);

                        }
                        else if(V_u_neig == uRank[1]) {
                            if(V_u_unvis > uRank[2]) {
                               writeln("Here 3 checked");

                                u_m = u;
                                uRank[0] = V_u_vis;
                                uRank[1] = V_u_neig;
                                uRank[2] = V_u_unvis;
                        writeln("Now u_m = " , u_m, "uRank changed to = ", uRank);

                            }
                        }
                    }


                }
                //writeln("uRank = ", uRank);
                writeln("////////////////////////////lets update/////////////////////////////////////////\n\n");
                var inNeighborsg2_u_m = dstRG2[segRG2[u_m]..<segRG2[u_m+1]];            
                var outNeighborsg2_u_m = dstNodesG2[segGraphG2[u_m]..<segGraphG2[u_m+1]];
                
                var combinedSet_u_m: set(int);
                // Add elements of in-neigh to the set
                for elem in inNeighborsg2_u_m {
                    combinedSet_u_m.add(elem);
                }
                
                for elem in outNeighborsg2_u_m {
                    combinedSet_u_m.add(elem);
                }

                writeln("u_m = ", u_m);
                writeln("combinedSet_u_m = ", combinedSet_u_m);
                var minIndex = -1;
                
                for elem in combinedSet_u_m{
                    if Visited[elem] == true {
                        if minIndex <= elem then minIndex = elem;
                    }
                }
                writeln("minIndex = ", minIndex);
                Miu.pushBack(u_m);
                ParentMiu.pushBack(minIndex);
                Visited(u_m) = true;


                writeln("\n Updateing V , Miu, ParentMiu: ---------------");
                writeln("V = ", V);
                writeln("Miu = ", Miu);
                writeln("ParentMiu = ", ParentMiu);
                V.remove(u_m);
                writeln("u_m removed now V = ", V);

                writeln("V.size = ", V.size);

            }// end While
            writeln("end of the while");

            writeln("Miu = ", Miu);
            writeln("ParentMiu = ", ParentMiu);

            return(Miu, ParentMiu);
        }// end of GreatestConstraintFirst
        //GreatestConstraintFirst();
////////////////////////////////////////////////////////////////////////////////////
        /** Generate in-neighbors and out-neighbors for a given subgraph state.*/
        proc addToTinTout (u: int, v: int, ref state: State) {
            state.core[v] = u; // v from g2 to a u from g1
            state.depth += 1; // a pair of vertices were mapped therefore increment depth by 1

            var inNeighbors = dstRG1[segRG1[u]..<segRG1[u+1]];
            var outNeighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];

            state.Tin1.remove(u);
            state.Tout1.remove(u);
    
            for n1 in inNeighbors do if !state.isMappedn1(n1) then state.Tin1.add(n1);
            for n1 in outNeighbors do if !state.isMappedn1(n1) then state.Tout1.add(n1);
  
            var inNeighborsg2 = dstRG2[segRG2[v]..<segRG2[v+1]];            
            var outNeighborsg2 = dstNodesG2[segGraphG2[v]..<segGraphG2[v+1]];

            state.Tin2.remove(v);
            state.Tout2.remove(v);

            for n2 in inNeighborsg2 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
            for n2 in outNeighborsg2 do if !state.isMappedn2(n2) then state.Tout2.add(n2);
        } // end of addToTinTout

        /** Check to see if the mapping of n1 from g1 to n2 from g2 is feasible.*/
        proc isFeasible(n1: int, n2: int, state: State) throws {
            var termout1, termout2, termin1, termin2, new1, new2 : int = 0;
            
            // Process the out-neighbors of g2.
            var getOutN2 = dstNodesG2[segGraphG2[n2]..<segGraphG2[n2+1]];
            for Out2 in getOutN2 {
                if state.core(Out2) != -1 {
                    var Out1 = state.core(Out2);
                    var eid1 = getEdgeId(n1, Out1, dstNodesG1, segGraphG1);
                    var eid2 = getEdgeId(n2, Out2, dstNodesG2, segGraphG2);

                    if eid1 == -1 || eid2 == -1 then return false;

                    var relationshipsG1eid1 = convertedRelationshipsG1[eid1];
                    var relationshipsG2eid2 = convertedRelationshipsG2[eid2];

                    // TODO: Add better relationship matching function.
                    if relationshipsG1eid1 != relationshipsG2eid2 then return false;
                } 
                else {
                    if state.Tin2.contains(Out2) then termin2 += 1;
                    if state.Tout2.contains(Out2) then termout2 += 1;
                    if !state.Tin2.contains(Out2) && !state.Tout2.contains(Out2) then new2 += 1;
                }
            }
                
            // Process the in-neighbors of g2. 
            var getInN2 = dstRG2[segRG2[n2]..<segRG2[n2+1]];
            for In2 in getInN2 {
                if state.core[In2] != -1 {
                    var In1 = state.core(In2);
                    var eid1 = getEdgeId(In1, n1, dstNodesG1, segGraphG1);
                    var eid2 = getEdgeId(In2, n2, dstNodesG2, segGraphG2);

                    if eid1 == -1 || eid2 == -1 then return false;

                    var relationshipsG1eid1 = convertedRelationshipsG1[eid1];
                    var relationshipsG2eid2 = convertedRelationshipsG2[eid2];

                    if relationshipsG1eid1 != relationshipsG2eid2 then return false;
                }
                else {
                    if state.Tin2.contains(In2) then termin2 += 1;
                    if state.Tout2.contains(In2) then termout2 += 1;
                    if !state.Tin2.contains(In2) && !state.Tout2.contains(In2) then new2 += 1;
                }
            }
                
            // Process the out-neighbors of g1. 
            var getOutN1 = dstNodesG1[segGraphG1[n1]..<segGraphG1[n1+1]];
            for Out1 in getOutN1 {
                if !state.isMappedn1(Out1) {
                    if state.Tin1.contains(Out1) then termin1 += 1;
                    if state.Tout1.contains(Out1) then termout1 += 1;
                    if !state.Tin1.contains(Out1) && !state.Tout1.contains(Out1) then new1 += 1;
                }
            }
                
            // Process the in-neighbors of g2.
            var getInN1 = dstRG1[segRG1[n1]..<segRG1[n1+1]];
            for In1 in getInN1 {
                if !state.isMappedn1(In1) {
                    if state.Tin1.contains(In1) then termin1 += 1;
                    if state.Tout1.contains(In1) then termout1 += 1;
                    if !state.Tin1.contains(In1) && !state.Tout1.contains(In1) then new1 += 1;
                }
            }

            if !(termin2 <= termin1 && termout2 <= termout1 && 
                    (termin2 + termout2 + new2) <= (termin1 + termout1 + new1)
                ) then return false;

            if !nodesLabelCompatible(n1, n2) then return false;

            return true;
        } // end of isFeasible

        /** Return the unmapped vertices for g1 and g2. */
        proc getBothUnmappedNodes(state: State): ([0..<state.n1]int, int) throws {
            var UnMapG1: [0..<state.n1] int = -1;
            var UnMapG2: int = -1;

            for i in state.D_core by -1{
                if state.core[i] == -1 then UnMapG2 = i; // Node i in G2 is mapped
                else UnMapG1[state.core[i]] = 0; // Corresponding node in G1 is mapped
            }
            
            return (UnMapG1, UnMapG2);
        } // end of getBothUnmappedNodes
       
        /** Create candidates based on current state and retuns a set of pairs.*/
        proc getCandidatePairsOpti(state: State): set((int, int)) throws {
            var candidates = new set((int, int), parSafe = true);

            if state.Tout1.size > 0 && state.Tout2.size > 0 {
                var minTout2: int;
                for elem in state.Tout2{
                    minTout2 = elem;
                    break;
                }    
                for n1 in state.Tout1 do candidates.add((n1, minTout2));          
            } else {
                if state.Tin1.size > 0 && state.Tin2.size > 0 {
                    var minTin2: int;
                    for elem in state.Tin2{
                        minTin2 = elem;
                        break;
                    }
                    for n1 in state.Tin1 do candidates.add((n1, minTin2));

                } else { 
                    var (unmappedG1, unmappedG2) = getBothUnmappedNodes(state);
                    //var flagunmappedG2 = false;
                    //var minUnmapped2 : int;

                    if unmappedG2 != -1 {
                        for i in 0..<state.n1 {
                            if unmappedG1[i] == -1 then candidates.add((i,unmappedG2));
                        } 
                    }
                } 
            }   
            return candidates;
        } // end of getCandidatePairsOpti
            
        /** Creates an initial, empty state.*/
        proc createInitialState(n1: int, n2: int): State throws {
            var state = new State(n1,n2);
            //state.init(n1,n2);
            return state;
        } // end of createInitialState

        /** Check that node labels are the same.*/
        proc nodesLabelCompatible(n1: int, n2: int): bool throws {
            var labelsG1n1 = convertedLabelsG1[n1];
            var labelsG2n2 = convertedLabelsG2[n2];

            if labelsG1n1 != labelsG2n2 then return false;

            return true;
        } // end of nodesLabelCompatible

        /** Perform the vf2 recursive steps returning all found isomorphisms.*/
        proc vf2Helper(state: State, depth: int): list(int) throws {
            var allmappings: list(int, parSafe=true);
            var stack: list(State, parSafe=true); // stack for backtracking
            //var stack = new ThreadSafeStack(); // Use the custom thread-safe stack

            //writeln("Pushed to stacked");
            stack.pushBack(state); // Initialize stack.
            //writeln("state", state);
            //writeln("at the begining stack size is = ", stack.size);
            //writeln("at the begining stack size is = ", stack.size());
            while stack.size > 0 {
            //while !stack.isEmpty() {
                //writeln("**************************************");
                //writeln("stack size inside the while = ", stack.size);
                //writeln("stack size is = ", stack.size());


                var Poped_state = stack.popBack();  // Critical section?

                //writeln("Poped_state.depth = ", Poped_state.depth);
                // Base case: check if a complete mapping is found
                if Poped_state.depth == g2.n_vertices {
                    //writeln("///////////////depth == g2.n_vertices/////////////////");
                    //writeln("Isos found = ", Poped_state.core);
                    // Process the found solution
                    for elem in  Poped_state.core do allmappings.pushBack(elem);
                    //writeln("allmappings = ", allmappings);
                    //writeln("////////////////////////////////");

                    //return allmappings;
                }
                // Generate candidate pairs (n1, n2) for mapping
                var candidatePairs = getCandidatePairsOpti(Poped_state);

                //writeln("state is :", Poped_state);
                //writeln("candidatePairs is :", candidatePairs);
                //writeln("/////////////FORALL////////////////////");
                // Iterate in parallel over candidate pairs
                var tid: atomic int;
                //forall (n1, n2) in candidatePairs with (const myTid = tid.fetchAdd(1), ref stack) {
                forall (n1, n2) in candidatePairs with (ref stack){

                    //writeln("current tid = ",myTid);
                    if isFeasible(n1, n2, Poped_state) {
                        //writeln("isFeasible TRUE for n1 = ", n1, " n2 = ", n2);
                        var newState = Poped_state.clone();
                        //writeln("newState generated: ");
                        // Update state with the new mapping
                        addToTinTout(n1, n2, newState);
                        //writeln("addToTinTout completed: ");


                   // Acquire the lock before pushing the new state onto the stack
                    //stackMutex.writeEF(true);  // Wait until we can acquire the lock
                        stack.pushBack(newState); // Critical section: push the new state onto the stack
                        //writeln("stack pushed Back: ");
                    //stackMutex.writeFE(false);  // Release the lock

                    }
                }
            } 
            


            return allmappings;
        }
        
        /** Main procedure that invokes all of the vf2 steps using the graph data that is
            initialized by `runVF2`.*/
        proc vf2(g1: SegGraph, g2: SegGraph): [] int throws {
            //writeln("---------vf2 started----------");

            var initial = createInitialState(g1.n_vertices, g2.n_vertices);
            var solutions = vf2Helper(initial, 0);
            var subIsoArrToReturn: [0..#solutions.size](int);

            for i in 0..#solutions.size do subIsoArrToReturn[i] = solutions(i);
            return(subIsoArrToReturn);
        } // end of vf2
        
        return IsoArr;
    } //end of runVF2
} // end of SubgraphIsomorphism module