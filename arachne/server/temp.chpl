module SubgraphIsomorphism {


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

        /** Perform the vf2 recursive steps returning all found isomorphisms.*/
        proc vf2Helper(state: State, depth: int): list(int) throws {
            var allmappings: list(int, parSafe=true);
            var stack: list(State); // stack for backtracking

            stack.pushBack(state); // Initialize stack.
            while stack.size > 0 {

                var Poped_state = stack.popBack();

                if Poped_state.depth == g2.n_vertices {

                    for elem in  Poped_state.core do allmappings.pushBack(elem);
 
                }
                // Generate candidate pairs (n1, n2) for mapping
                var candidatePairs = getCandidatePairsOpti(Poped_state);

                coforall (n1, n2) in candidatePairs with (ref stack){

                    //writeln("current tid = ",myTid);
                    if isFeasible(n1, n2, Poped_state) {
                        var newState = Poped_state.clone();
                        // Update state with the new mapping
                        addToTinTout(n1, n2, newState);
                        stack.pushBack(newState);

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