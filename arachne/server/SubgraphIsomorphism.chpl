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
    class State {
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
        proc clone(): owned State throws {
            var newState = new owned State(this.n1, this.n2);
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

    /** Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
    searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
    array that maps the isomorphic vertices of `g1` to those of `g2`.*/
    proc runVF2 (g1: SegGraph, g2: SegGraph, st: borrowed SymTab):[] int throws {
        var TimerArrNew:[0..30] real(64) = 0.0;
        var numIso: int = 0;

        // Extract the g1/G/g information from the SegGraph data structure.
        var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
        var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
        var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
        var srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
        var dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
        var segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
        var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;

        // Extract the g2/H/h information from the SegGraph data structure.
        var srcNodesG2 = toSymEntry(g2.getComp("SRC_SDI"), int).a;
        var dstNodesG2 = toSymEntry(g2.getComp("DST_SDI"), int).a;
        var segGraphG2 = toSymEntry(g2.getComp("SEGMENTS_SDI"), int).a;
        var srcRG2 = toSymEntry(g2.getComp("SRC_R_SDI"), int).a;
        var dstRG2 = toSymEntry(g2.getComp("DST_R_SDI"), int).a;
        var segRG2 = toSymEntry(g2.getComp("SEGMENTS_R_SDI"), int).a;
        var nodeMapGraphG2 = toSymEntry(g2.getComp("VERTEX_MAP_SDI"), int).a;

        // Get the number of vertices and edges for each graph.
        var nG1 = nodeMapGraphG1.size;
        var mG1 = srcNodesG1.size;
        var nG2 = nodeMapGraphG2.size;
        var mG2 = srcNodesG2.size;

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
        var convertedRelationshipsG1 = makeDistArray(g1.n_edges, domain(int));
        var convertedRelationshipsG2 = makeDistArray(g2.n_edges, domain(int));
        var convertedLabelsG1 = makeDistArray(g1.n_vertices, domain(int));
        var convertedLabelsG2 = makeDistArray(g2.n_vertices, domain(int));

        for (k,v) in zip(edgeRelationshipsGraphG1.keys(), edgeRelationshipsGraphG1.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedRelationshipsG1[i].add(relationshipStringToInt[mapper[x]]);
        }

        for (k,v) in zip(edgeRelationshipsGraphG2.keys(), edgeRelationshipsGraphG2.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do
                convertedRelationshipsG2[i].add(relationshipStringToInt[mapper[x]]);
        }

        for (k,v) in zip(nodeLabelsGraphG1.keys(), nodeLabelsGraphG1.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedLabelsG1[i].add(labelStringToInt[mapper[x]]);
        }

        for (k,v) in zip(nodeLabelsGraphG2.keys(), nodeLabelsGraphG2.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do 
                convertedLabelsG2[i].add(labelStringToInt[mapper[x]]);
        }
        //******************************************************************************************
        //******************************************************************************************

        //************************************LOCALIZATION******************************************
        // var srcNodesG1: [0..<mG1] int = srcNodesG1Dist;
        // var dstNodesG1: [0..<mG1] int = dstNodesG1Dist;
        // var segGraphG1: [0..<nG1+1] int = segGraphG1Dist;
        // var srcRG1: [0..<mG1] int = srcRG1Dist;
        // var dstRG1: [0..<mG1] int = dstRG1Dist;
        // var segRG1: [0..<nG1+1] int = segRG1Dist;
        // var nodeMapGraphG1: [0..<nG1] int = nodeMapGraphG1Dist;
        // var convertedRelationshipsG1: [0..<mG1] domain(int) = convertedRelationshipsG1Dist;
        // var convertedLabelsG1: [0..<nG1] domain(int) = convertedLabelsG1Dist;

        // var srcNodesG2: [0..<mG2] int = srcNodesG2Dist;
        // var dstNodesG2: [0..<mG2] int = dstNodesG2Dist;
        // var segGraphG2: [0..<nG2+1] int = segGraphG2Dist;
        // var srcRG2: [0..<mG2] int = srcRG2Dist;
        // var dstRG2: [0..<mG2] int = dstRG2Dist;
        // var segRG2: [0..<nG2+1] int = segRG2Dist;
        // var nodeMapGraphG2: [0..<nG2] int = nodeMapGraphG2Dist;
        // var convertedRelationshipsG2: [0..<mG2] domain(int) = convertedRelationshipsG2Dist;
        // var convertedLabelsG2: [0..<nG2] domain(int) = convertedLabelsG2Dist;
        //******************************************************************************************
        //findWedges();
        //findTriangles();

        var IsoArrtemp = vf2(g1, g2);
        var IsoArr = nodeMapGraphG1[IsoArrtemp]; // Map vertices back to original values.
        
        proc findWedges() {
            // Iterate through all nodes
            for v in 0..g1.n_vertices-1 {
                // Retrieve in-neighbors and out-neighbors for node v
                var inNeighborsg1 = dstRG1[segRG1[v]..<segRG1[v+1]];
                var outNeighborsg1 = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

                // We check each in-neighbor against each out-neighbor to find potential wedges
                // There's no need to check if in-neighbors and out-neighbors are directly connected 
                // since wedges are formed based on the central node 'v'
                for inN in inNeighborsg1 {
                    for outN in outNeighborsg1 {
                        // For each pair (inN, outN), we have a potential wedge (inN, v, outN)
                        // Since 'v' is the central node connecting 'inN' and 'outN', this is a valid wedge by definition.
                        // Note: We're assuming that direct connection between 'inN' and 'outN' isn't a concern here based on your description.
                        writeln("Wedge found: ", inN, "-", v, "-", outN);
                    }
                }
            }
        }


        proc findTriangles() {
            // Iterate through all nodes as potential starting point A
            for A in 0..g1.n_vertices-1 {
                // Retrieve out-neighbors for node A (potential B nodes)
                ref outNeighborsA = dstNodesG1[segGraphG1[A]..<segGraphG1[A+1]];

                // For each out-neighbor B of A
                for B in outNeighborsA {
                    // Retrieve out-neighbors for node B (potential C nodes)
                    ref outNeighborsB = dstNodesG1[segGraphG1[B]..<segGraphG1[B+1]];

                    // For each out-neighbor C of B
                    for C in outNeighborsB {
                        // Check if C is also directly connected back to A, completing the triangle
                        // This requires checking if A is an in-neighbor of C
                        //var inNeighborsC = dstRG1[segRG1[C]..<segRG1[C+1]];
                        ref outNeighborsC = dstNodesG1[segGraphG1[C]..<segGraphG1[C+1]];

                        // If A is found in C's in-neighbors, we have identified a triangle A->B->C->A
                        if outNeighborsC.find(A) != outNeighborsC.domain.lowBound-1 {
                            writeln("Triangle found: ", A, "->", B, "->", C, "->", A);
                        }
                    }
                }
            }
        }

        proc findFeedForward()   throws {
            var feedForwardLoops: list([0..2] int);

            // Use parallel iteration over all nodes with `forall` for potential performance improvement
            forall A in 0..g1.n_vertices-1 with(ref feedForwardLoops) {
                // Retrieve out-neighbors for node A
                var outNeighborsA = dstNodesG1[segGraphG1[A]..<segGraphG1[A+1]];

                // Check each out-neighbor B of A
                for B in outNeighborsA {
                    // Skip if A->A or B->B direct loops
                    if A == B { continue; }

                    // Retrieve out-neighbors for node B
                    var outNeighborsB = dstNodesG1[segGraphG1[B]..<segGraphG1[B+1]];

                    // Check each out-neighbor C of B
                    for C in outNeighborsB {
                        // Skip if B->A (backward) or C->C direct loops, ensuring feed-forward
                        if B == C || C == A { continue; }

                        // Check for direct A->C connection for feed-forward loop
                        if outNeighborsA.find(C) != outNeighborsA.domain.lowBound-1 {
                        // Create an array for this loop and add it to the list
                        var loopArray: [0..2] int = [A, B, C];
                        feedForwardLoops.pushBack(loopArray);
                        //writeln("Feed-forward, A=", A, ", B=", B, ", C=", C);
                        }
                    }
                }
            }
            //var feedForwardLoopsArr: [0..feedForwardLoops.size()-1] int;
           
            return (feedForwardLoops);
        }

        proc findOutWedges()throws {
            var outWedges: list([0..2] int);

            // Iterate over each node and its out-neighbors
            for u in 0..g1.n_vertices-1 {
                var outNeighbors = dstNodesG1.localSlice(segGraphG1[u]..<segGraphG1[u+1]);
                if outNeighbors.size >= 2 {
                    // If there are at least two out-neighbors, there could be out-wedges
                    for i in outNeighbors {
                        for j in outNeighbors {
                            if i != j {
                                // For each pair of out-neighbors (B, C), we have an out-wedge (A->B, A->C)
                                var loopArray: [0..2] int = [u, i, j];
                                outWedges.pushBack(loopArray); // Adjust u-1 if using 0-based
                                writeln("u = ",u," i = ", i," j = ", j);
                            }
                        }
                    }
                }
            }

            return(outWedges);
        }
        /** Generate in-neighbors and out-neighbors for a given subgraph state.*/
        proc addToTinTout (u: int, v: int, state: State) {
            state.core[v] = u; // v from g2 to a u from g1
            state.depth += 1; // a pair of vertices were mapped therefore increment depth by 1

            var inNeighbors = dstRG1.localSlice(segRG1[u]..<segRG1[u+1]);
            var outNeighbors = dstNodesG1.localSlice(segGraphG1[u]..<segGraphG1[u+1]);

            state.Tin1.remove(u);
            state.Tout1.remove(u);
    
            for n1 in inNeighbors do if !state.isMappedn1(n1) then state.Tin1.add(n1);
            for n1 in outNeighbors do if !state.isMappedn1(n1) then state.Tout1.add(n1);
  
            var inNeighborsg2 = dstRG2.localSlice(segRG2[v]..<segRG2[v+1]);            
            var outNeighborsg2 = dstNodesG2.localSlice(segGraphG2[v]..<segGraphG2[v+1]);

            state.Tin2.remove(v);
            state.Tout2.remove(v);

            for n2 in inNeighborsg2 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
            for n2 in outNeighborsg2 do if !state.isMappedn2(n2) then state.Tout2.add(n2);
        } // end of addToTinTout
        // 
        // Generate in-neighbors and out-neighbors for a given subgraph state
        // for each element in array n1, with its index as n2.
        //
        proc addToTinToutArray(n1: [] int) throws{
            //writeln("-----------------begingng of addToTinToutArray----------");
            var initialstate = createInitialState(g1.n_vertices, g2.n_vertices);
            for i in 0..n1.size-1{
                //writeln("i = ", i, ", n1[i] = ", n1[i]);
                addToTinTout (n1[i], i, initialstate);
            }
            //writeln("-*-*-*-*-*-*-*-*-end of addToTinToutArray-*-*-*-*-*-*-*-*\n");
            //writeln("initialstate = ", initialstate);
            return initialstate;
        }
        /** Check to see if the mapping of n1 from g1 to n2 from g2 is feasible.*/
        proc isFeasible(n1: int, n2: int, state: State) throws {
            var termout1, termout2, termin1, termin2, new1, new2 : int = 0;
            
            // Process the out-neighbors of g2.
            var getOutN2 = dstNodesG2.localSlice(segGraphG2[n2]..<segGraphG2[n2+1]);
            for Out2 in getOutN2 {
                if state.core(Out2) != -1 {
                    var Out1 = state.core(Out2);
                    var eid1 = getEdgeId(n1, Out1, dstNodesG1, segGraphG1);
                    var eid2 = getEdgeId(n2, Out2, dstNodesG2, segGraphG2);

                    if eid1 == -1 || eid2 == -1 then return false;

                    var relationshipsG1eid1 = convertedRelationshipsG1[eid1];
                    var relationshipsG2eid2 = convertedRelationshipsG2[eid2];

                    // TODO: Add better relationship matching function.
                    // if relationshipsG1eid1 != relationshipsG2eid2 then return false;
                } 
                else {
                    if state.Tin2.contains(Out2) then termin2 += 1;
                    if state.Tout2.contains(Out2) then termout2 += 1;
                    if !state.Tin2.contains(Out2) && !state.Tout2.contains(Out2) then new2 += 1;
                }
            }
                
            // Process the in-neighbors of g2. 
            var getInN2 = dstRG2.localSlice(segRG2[n2]..<segRG2[n2+1]);
            for In2 in getInN2 {
                if state.core[In2] != -1 {
                    var In1 = state.core(In2);
                    var eid1 = getEdgeId(In1, n1, dstNodesG1, segGraphG1);
                    var eid2 = getEdgeId(In2, n2, dstNodesG2, segGraphG2);

                    if eid1 == -1 || eid2 == -1 then return false;

                    var relationshipsG1eid1 = convertedRelationshipsG1[eid1];
                    var relationshipsG2eid2 = convertedRelationshipsG2[eid2];

                    // TODO: Add better relationship matching function.
                    // if relationshipsG1eid1 != relationshipsG2eid2 then return false;
                }
                else {
                    if state.Tin2.contains(In2) then termin2 += 1;
                    if state.Tout2.contains(In2) then termout2 += 1;
                    if !state.Tin2.contains(In2) && !state.Tout2.contains(In2) then new2 += 1;
                }
            }
                
            // Process the out-neighbors of g1. 
            var getOutN1 = dstNodesG1.localSlice(segGraphG1[n1]..<segGraphG1[n1+1]);
            for Out1 in getOutN1 {
                if !state.isMappedn1(Out1) {
                    if state.Tin1.contains(Out1) then termin1 += 1;
                    if state.Tout1.contains(Out1) then termout1 += 1;
                    if !state.Tin1.contains(Out1) && !state.Tout1.contains(Out1) then new1 += 1;
                }
            }
                
            // Process the in-neighbors of g2.
            var getInN1 = dstRG1.localSlice(segRG1[n1]..<segRG1[n1+1]);
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

            // TODO: Add better label matching function.
            // if !nodesLabelCompatible(n1, n2) then return false;

            return true;
        } // end of isFeasible

        /** Return the unmapped vertices for g1 and g2. */
        proc getBothUnmappedNodes(state: State): ([0..<state.n1]int, int) throws {
            var UnMapG1: [0..<state.n1] int = -1;
            var UnMapG2: int = -1;

            for i in state.D_core by -1{
                if state.core[i] == -1 then UnMapG2 = i; 
                else UnMapG1[state.core[i]] = 0; 
            }
            
            return (UnMapG1, UnMapG2);
        } // end of getBothUnmappedNodes
       
        /** Create candidates based on current state and retuns a set of pairs.*/
        proc getCandidatePairsOpti(state: State): (list(int) , int) throws {
            //var candidates = new set((int, int), parSafe = true);

            if state.Tout1.size > 0 && state.Tout2.size > 0 {
                var minTout2: int;
                var unmappedG1: list(int);

                for elem in state.Tout2{
                    minTout2 = elem;
                    break;
                }    
                //for n1 in state.Tout1 do candidates.add((n1, minTout2));
                for n1 in state.Tout1 do unmappedG1.pushBack(n1);
                return (unmappedG1, minTout2);

            } else {
                if state.Tin1.size > 0 && state.Tin2.size > 0 {
                    var minTin2: int;
                    var unmappedG1: list(int);

                    for elem in state.Tin2{
                        minTin2 = elem;
                        break;
                    }
                    //for n1 in state.Tin1 do candidates.add((n1, minTin2));
                    for n1 in state.Tin1 do unmappedG1.pushBack(n1);
                    
                    return (unmappedG1, minTin2);
                } else { 
                    writeln("$$$$$ Last state = ", state);
                    //var unmappedG1: [0..<state.n1] int = -1;
                    var unmappedG1: list(int) = 0..#state.n1;
                    var unmappedG2: int = -1;
//remove
                    for i in state.D_core by -1{
                        if state.core[i] == -1 then unmappedG2 = i; 
                        else unmappedG1.remove[state.core[i]]; 
                    }
                    return (unmappedG1, unmappedG2);
                }
            }   
            //return (unmappedG1, unmappedG2);
        } // end of getCandidatePairsOpti
            
        /** Creates an initial, empty state.*/
        proc createInitialState(n1: int, n2: int): State throws {
            return new owned State(n1, n2);
        } // end of createInitialState

        /** Check that node labels are the same.*/
        proc nodesLabelCompatible(n1: int, n2: int): bool throws {
            var labelsG1n1 = convertedLabelsG1[n1];
            var labelsG2n2 = convertedLabelsG2[n2];

            if labelsG1n1 != labelsG2n2 then return false;

            return true;
        } // end of nodesLabelCompatible

        /** Perform the vf2 recursive steps returning all found isomorphisms.*/
        proc vf2Helper(state: owned State, depth: int): list(int) throws {
            var allmappings: list(int, parSafe=true);

            // Base case: check if a complete mapping is found
            if depth == g2.n_vertices {
                // Process the found solution
                for elem in state.core do allmappings.pushBack(elem);
                return allmappings;
            }


            
            if depth == 0 {
                var ffcandidates = findOutWedges();
                //forall n1Arr in ffcandidates with (ref state, ref allmappings) {
                for n1Arr in ffcandidates {
                        //var newState = state.clone();
                        //writeln("addToTinToutArray called");
                        // Update state with the new mapping
                        var newState = addToTinToutArray(n1Arr);
                        //writeln("addToTinToutArray returned : ",newState );

                        // Recursive call with updated state and increased depth
                        
                        var newMappings = vf2Helper(newState, 3);
                        
                        // Use a loop to add elements from newMappings to allmappings
                        for mapping in newMappings do allmappings.pushBack(mapping);
                    
                }
            } 
            if depth == 3 {
                // Generate candidate pairs (n1, n2) for mapping
                //var candidatePairs = getCandidatePairsOpti(state);
                var candidatePairs: list(int, parSafe=true);
                var n2: int;
                (candidatePairs, n2) = getCandidatePairsOpti(state);
                //writeln("state = ", state);
                //writeln("candidatePairs,", n2 );
                //writeln(candidatePairs);
                //writeln("///////////////////////////////////");
                // Iterate in parallel over candidate pairs
                //forall (n1, n2) in candidatePairs with (ref state, ref allmappings) {
                forall n1 in candidatePairs with (ref state, ref allmappings) {
                    if isFeasible(n1, n2, state) {
                        writeln("n1 = ", n1, " n2 = ", n2);
                        writeln("are feasiblr for state:");
                        writeln(state);
                        var newState = state.clone();

                        // Update state with the new mapping
                        addToTinTout(n1, n2, newState);

                        // Recursive call with updated state and increased depth
                        var newMappings = vf2Helper(newState, depth + 1);
                        
                        // Use a loop to add elements from newMappings to allmappings
                        for mapping in newMappings do allmappings.pushBack(mapping);
                    }
                }
            }
            

            return allmappings;
        }
        
        /** Main procedure that invokes all of the vf2 steps using the graph data that is
            initialized by `runVF2`.*/
        proc vf2(g1: SegGraph, g2: SegGraph): [] int throws {
            var initial = createInitialState(g1.n_vertices, g2.n_vertices);
            var solutions = vf2Helper(initial, 0);
            var subIsoArrToReturn: [0..#solutions.size](int);
            for i in 0..#solutions.size do subIsoArrToReturn[i] = solutions(i);
            return(subIsoArrToReturn);
        } // end of vf2
        
        return IsoArr;
    } //end of runVF2
} // end of SubgraphIsomorphism module