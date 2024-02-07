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

    /** Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
    searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
    array that maps the isomorphic vertices of `g1` to those of `g2`.*/
    proc runVF2 (g1: SegGraph, g2: SegGraph, st: borrowed SymTab):[] int throws {
        var TimerArrNew:[0..30] real(64) = 0.0;
        var numIso: int = 0;
        var timerpreproc:stopwatch;
        timerpreproc.start();

        //******************************************************************************************
        var UnmappedG1: [0..<g1.n_vertices](int) = -1;
        var UnmappedG2: [0..<g2.n_vertices](int) = -1;
        
        
        

        timerpreproc.stop();
        TimerArrNew[0] += timerpreproc.elapsed();
        
        var timerVF2:stopwatch;
        timerVF2.start();
        var IsoArrtemp = vf2(g1, g2);
        timerVF2.stop();
        TimerArrNew[1] += timerVF2.elapsed();
        
        var IsoArr = nodeMapGraphG1[IsoArrtemp]; // Map vertices back to original values.

        


        /** Keeps track of the isomorphic mapping state during the execution process of VF2.*/
        record State {
            var n2: int;

            var D_core2: domain(1) = {0..1};

            var core2: [D_core2] int;
            
            var Tin1: domain(int);
            var Tout1: domain(int);

            var Tin2: domain(int);
            var Tout2: domain(int);
            
            var depth:int;

            /** State initializer.*/
            proc init() {
                this.n2 = 0;
                
                this.core2 = -1;


                this.Tin1  =  {1..0};
                this.Tout1 =  {1..0};
                this.Tin2  =  {1..0};
                this.Tout2 =  {1..0};

                this.depth = 0;
            }
            /** Initialized based on given sizes `n1` and `n2`.*/
            proc init(n2) {
                this.n2 = n2;

                var new_dom2: domain(1) = {0..<n2};
     
                this.D_core2 = new_dom2; // modifies how much core can store

                this.core2 = -1;
                
                this.Tin1  =  {1..0};
                this.Tout1 =  {1..0};

                this.Tin2  =  {1..0};
                this.Tout2 =  {1..0};

                this.depth = 0;
            }

            /** Copy current state information to a new state.*/
            proc copy() {
                var state = new State(n2);

                state.n2 = this.n2;

                state.D_core2 = this.D_core2;

                state.core2 = this.core2;
                
                state.Tin1 = this.Tin1;
                state.Tout1 = this.Tout1;

                state.Tin2 = this.Tin2;
                state.Tout2 = this.Tout2;

                state.depth = this.depth;
                return state;
            }

            /** Reset vectors during backtracking.*/
            proc reset() {
                //this.mapping.clear(); // reset to empty
                //this.core1.clear();
                //this.core2.clear();
                this.core2 = -1;
                this.D_core2 = {0..1};

                this.Tin1  =  {1..0};
                this.Tout1 =  {1..0};

                this.Tin2  =  {1..0};
                this.Tout2 =  {1..0};

                this.depth = 0;

            }

            /** Check if a given node is mapped in g1.*/
            proc isMappedn1(n1: int): bool {
                //if this.core1.contains(node) then return true;
                //else return false;
                var Mapflag: bool = false;
                for i in D_core2{
                    if this.core2[i] == n1 then Mapflag = true;
                }
                return (Mapflag);  // Check if the node is mapped in g1
            }
            
            /** Check if a given node is mapped in g2.*/
            proc isMappedn2(n2: int): bool {
                //if this.core2.contains(node) then return true;
                //else return false;
                return (this.core2[n2] != -1);  // Check if the node is mapped in g2
            }
                
            
        } 
        //////////////////////////////////////////////////////////////end of State record
            proc getBothUnmappedNodes(ref state:State, ref UnmappedG1, ref UnmappedG2) {


                for i in state.D_core2 {
                    //writeln("this.core2[i] = ", this.core2[i] );
                    if state.core2[i] != -1 then UnmappedG2[i] = 0;
                    else UnmappedG1[state.core2[i]] = 0;
                }

            }
            proc addToTinTout (u: int, v: int, ref state:State){
                
                state.core2[v] = u;  // Map x2 in g2 to x1 in g1
                var counter: int =0;
                for elem in state.core2{
                    if elem != -1 then counter += 1;
                }
                state.depth = counter;
 
 
                ref inNeighbors = dstRG1[segRG1[u]..<segRG1[u+1]];
                ref outNeighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];


                state.Tin1.remove(u);
                state.Tout1.remove(u);
    
                for n1 in inNeighbors do if !state.isMappedn1(n1) then state.Tin1.add(n1);
                for n1 in outNeighbors do if !state.isMappedn1(n1) then state.Tout1.add(n1);
   
                
                ref inNeighborsg2 = dstRG2[segRG2[v]..<segRG2[v+1]];            
                ref outNeighborsg2 = dstNodesG2[segGraphG2[v]..<segGraphG2[v+1]];


                state.Tin2.remove(v);
                state.Tout2.remove(v);
                
                for n2 in inNeighborsg2 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
                for n2 in outNeighborsg2 do if !state.isMappedn2(n2) then state.Tout2.add(n2);

                            
                return ;
            } 
            /** Check if a pair of candidates are feasible.*/

            proc isFeasible(n1: int, n2: int, ref state:State) throws {
                var termout1, termout2, termin1, termin2, new1, new2 : int = 0;


                
                // Get out neighbors of G1 and G2
                var getOutN1 = dstNodesG1[segGraphG1[n1]..<segGraphG1[n1+1]];
                var getOutN2 = dstNodesG2[segGraphG2[n2]..<segGraphG2[n2+1]];
            
                // Check out neighbors of n2 
                for Out2 in getOutN2 {
                    //if state.isMappedn2(Out2) {
                    if state.core2(Out2) != -1 {
                        //var Out1 = state.core2(Out2);
                        var Out1 = state.core2(Out2);
                        var eid1 = getEdgeId(n1, Out1, dstNodesG1, segGraphG1);
                        var eid2 = getEdgeId(n2, Out2, dstNodesG2, segGraphG2);

                        if eid1 == -1 || eid2 == -1 {

                            return false;
                        }

             
             
                        var relationshipsG1eid1 = convertedRelationshipsG1[eid1];
                        var relationshipsG2eid2 = convertedRelationshipsG2[eid2];
  
                        if relationshipsG1eid1 != relationshipsG2eid2 {;

                            return false;
                        }
                    } 
                    else {
                        if state.Tin2.contains(Out2) then termin2 += 1;
                        if state.Tout2.contains(Out2) then termout2 += 1;
                        if !state.Tin2.contains(Out2) && !state.Tout2.contains(Out2) then new2 += 1;                    
                       
                    }
                }
                
                // Get in neighbors of G1 and G2
                var getInN1 = dstRG1[segRG1[n1]..<segRG1[n1+1]];
                var getInN2 = dstRG2[segRG2[n2]..<segRG2[n2+1]];

                // Check in neighbors of n2 
                for In2 in getInN2 {
                    if state.core2[In2] != -1 {
                        var In1 = state.core2(In2);
                        var eid1 = getEdgeId(In1, n1, dstNodesG1, segGraphG1);
                        var eid2 = getEdgeId(In2, n2, dstNodesG2, segGraphG2);

                        if eid1 == -1 || eid2 == -1 {
                            return false;
                        }

     
                        var relationshipsG1eid1 = convertedRelationshipsG1[eid1];
                        var relationshipsG2eid2 = convertedRelationshipsG2[eid2];

                        if relationshipsG1eid1 != relationshipsG2eid2 {;

                            return false;
                        }
                    }
                    else {
                        if state.Tin2.contains(In2) then termin2 += 1;
                        if state.Tout2.contains(In2) then termout2 += 1;
                        if !state.Tin2.contains(In2) && !state.Tout2.contains(In2) then new2 += 1;
                    }
                }
                
                // Check out neighbors of n1 
                for Out1 in getOutN1 {
                    if !state.isMappedn1(Out1) {
                        if state.Tin1.contains(Out1) then termin1 += 1;
                        if state.Tout1.contains(Out1) then termout1 += 1;
                        if !state.Tin1.contains(Out1) && !state.Tout1.contains(Out1) then new1 += 1;
                    }
                }
                
                // Check in neighbors of n1
                for In1 in getInN1 {
                    if !state.isMappedn1(In1) {
                        if state.Tin1.contains(In1) then termin1 += 1;
                        if state.Tout1.contains(In1) then termout1 += 1;
                        if !state.Tin1.contains(In1) && !state.Tout1.contains(In1) then new1 += 1;
                    }
                }

                if !(termin2<=termin1 && termout2<=termout1 && (termin2+termout2+new2)<=(termin1+termout1+new1)) {
                    return false;
                }


                return true;
            } // end of isFeasible

/** Create candidates based on current state and retuns a set of pairs.*/
            proc getCandidatePairsOpti(ref state: State) throws {

                var candidates = new set((int, int), parSafe = true);

                


                if state.Tout1.size > 0 && state.Tout2.size > 0 {

                    var minTout2: int;
                    for elem in state.Tout2{
                        minTout2 = elem;
                        break;
                    }
                    
                    for n1 in state.Tout1 do candidates.add((n1, minTout2));
                
                } else {
                    //If Tin1 and Tin2 are both nonempty.
                    if state.Tin1.size > 0 && state.Tin2.size > 0 {
                        //var minTin2 = min reduce state.Tin2;
                        var minTin2: int;
                        for elem in state.Tin2{
                            minTin2 = elem;
                            break;
                        }
                        for n1 in state.Tin1 do candidates.add((n1, minTin2));
                    
                    } else { // not (Tin1 or Tin2) NOTE: What does this mean?
                        var timer16:stopwatch;
                        timer16.start();
                        
                        //var (unmappedG1,unmappedG2) = getBothUnmappedNodes(state);
                        getBothUnmappedNodes(state,UnmappedG1, UnmappedG2 );

                        timer16.stop();
                        TimerArrNew[16] += timer16.elapsed();
                        
                        var flagunmappedG2 = false;
                        var minUnmapped2 : int;

                        for elem in UnmappedG2{
                            if elem != -1{
                                minUnmapped2 = elem;
                                flagunmappedG2 = true;
                            }
                        }
                        //writeln("flagunmappedG2 = ", flagunmappedG2);
                        if !flagunmappedG2 {
                            //var minUnmapped2 = min reduce unmappedG2;

                            for i in 0..<g1.n_vertices {
                                if UnmappedG1[i] == -1 then candidates.add((i,minUnmapped2));
                            } 
                        }
                    } 
                }   

                //writeln(" candidates = ", candidates);
                return candidates;
            } // end of getCandidatePairsOpti
        /** Creates an initial, empty state. NOTE: Is this needed?*/
        proc createInitialState(n2: int): State throws {
            var state = new State();
            state.init(n2);
            return state;
        }  //end of createInitialState


        /** Check that node labels are the same.*/
        proc nodesLabelCompatible(n1: int, n2: int): bool throws {
            var timernodesLabelCompatible:stopwatch;
            timernodesLabelCompatible.start();



            var labelsG1n1 = convertedLabelsG1[n1];
            var labelsG2n2 = convertedLabelsG2[n2];
          
          
            if labelsG1n1 != labelsG2n2 {
                timernodesLabelCompatible.stop();
                TimerArrNew[25] += timernodesLabelCompatible.elapsed();                
                return false;
            }
            timernodesLabelCompatible.stop();
            TimerArrNew[25] += timernodesLabelCompatible.elapsed();
            return true;
        } // end of nodesLabelCompatible


        /** Depth-first-search-like steps to traverse a graph and return a list of all solution 
        states.*/
        proc dfs(ref initialState: State) throws {

            var timerfirstpartdfs:stopwatch;
            timerfirstpartdfs.start();


            //var allmappings: list (set((int, int)));
            var allmappings: list([0..#g2.n_vertices] int);
            var stack:list(State, parSafe=true); // stack for backtracking
            
           
            stack.pushBack(initialState); // Initialize stack.

            while stack.size > 0 {
                
                var timerstackpopBack:stopwatch;
                timerstackpopBack.start();
                
                var state = stack.popBack();

                timerstackpopBack.stop();
                TimerArrNew[8] += timerstackpopBack.elapsed();
                
                //if state.mapping.size == g2.n_vertices then allmappings.pushBack(state.mapping);
                var timer13:stopwatch;
                timer13.start();
                //if (min reduce state.core2 != -1 ){
                if state.depth == g2.n_vertices{
                    allmappings.pushBack(state.core2);
                    //writeln("current mapping # = ",state.core2 );
                    //numIso += 1;

                } 
                timer13.stop();
                TimerArrNew[13] += timer13.elapsed();

                //writeln("after adding allmappings is now = ", allmappings);
                var timer14:stopwatch;
                timer14.start();
                var candidatesOpti = getCandidatePairsOpti(state);
                timer14.stop();
                TimerArrNew[14] += timer14.elapsed();

                //writeln("candidatesOpti = ", candidatesOpti);
                
                var candidatesOptiFlagged = new set((int, int), parSafe = true);

                var timer15:stopwatch;
                timer15.start();

                for (n1, n2) in candidatesOpti {
                    var flagisFeasible: bool;

                    var timerisFeasible:stopwatch;
                    timerisFeasible.start();

                    flagisFeasible = isFeasible(n1, n2,  state);
                    if flagisFeasible then candidatesOptiFlagged.add((n1, n2));

                    timerisFeasible.stop();
                    TimerArrNew[5] += timerisFeasible.elapsed();
                }    
                for (n1, n2) in candidatesOptiFlagged {    
                    var flaglabel: bool;

                    
                    var timernodesLabelCompatible:stopwatch;
                    timernodesLabelCompatible.start();
                    
                    flaglabel = nodesLabelCompatible(n1, n2);
                    
                    timernodesLabelCompatible.stop();
                    TimerArrNew[6] += timernodesLabelCompatible.elapsed();

                    
                    if  flaglabel {
                        //writeln("is feasible for, ", n1,", ",n2, "passed");
                        var timer10:stopwatch;
                        timer10.start();
                        
                        var newState = state;
                                                 
                        timer10.stop();
                        TimerArrNew[10] += timer10.elapsed();

                        var timeraddToTinTout:stopwatch;
                        timeraddToTinTout.start();

                        addToTinTout(n1, n2, newState);

                        timeraddToTinTout.stop();
                        TimerArrNew[4] += timeraddToTinTout.elapsed();

                        //writeln("\nafter addToTinTout newState = ", newState);
                        var timerstackpushBack:stopwatch;
                        timerstackpushBack.start();
                        
                        stack.pushBack(newState);

                        timerstackpushBack.stop();
                        TimerArrNew[2] += timerstackpushBack.elapsed();
                        

                    }
                }

                timer15.stop();
                TimerArrNew[15] += timer15.elapsed();


            }
            return allmappings; // Isomappings
        }  // end of dfs


        /** Main procedure that invokes all of the vf2 steps using the graph data that is
        initialized by `runVF2`.*/
        proc vf2(g1: SegGraph, g2: SegGraph): [] int throws {
            var initial = createInitialState(g2.n_vertices);
            //writeln("initial = ", initial);
            var timerDFS:stopwatch;
            timerDFS.start();
            
            var solutions = dfs(initial);
            //writeln("solutions from DFS = ", solutions);
            
            timerDFS.stop();
            TimerArrNew[3] += timerDFS.elapsed();

            var subIsoArrToReturn: [0..(solutions.size*g2.n_vertices)-1](int);
            //writlen("solutions = ",solutions );
            var timersolution:stopwatch;
            timersolution.start();

            var posOffset = 0;
            for solSet in solutions {
                //writeln("solSet = ", solSet);
                var indx = 0;
                for elem in solSet {
                    subIsoArrToReturn[posOffset + indx] = elem;
                    indx +=1;
                    //writeln(elem," add to subIsoArrToReturn");
                }
                posOffset += g2.n_vertices;
            }
            timersolution.stop();
            TimerArrNew[12] += timersolution.elapsed();
            return(subIsoArrToReturn);
        } //end of vf2
        
        writeln("\n\n");

        writeln("Preprocessing total time = ", TimerArrNew[0]);
        writeln("PushBack total time = ", TimerArrNew[2]);
        writeln("PopBack total time = ", TimerArrNew[8]);
        writeln("Addto TinTout + AddPair total time = ", TimerArrNew[4]);
        writeln("isFeasible total time = ", TimerArrNew[5]);
        writeln("DFS total time = ", TimerArrNew[3]);

        writeln("node label total time = ", TimerArrNew[6]);
        writeln("INSIDE node label total time = ", TimerArrNew[25]);
        writeln("state copy total time = ", TimerArrNew[10]);
        writeln("state reset total time = ", TimerArrNew[11]);
        writeln("state solution total time = ", TimerArrNew[12]);
        writeln("allmapping + reduce time = ", TimerArrNew[13]);
        writeln("getCandidatePairsOpti time = ", TimerArrNew[14]);
        writeln("for over candidatestime = ", TimerArrNew[15]);
        writeln("get both unmapped total time = ", TimerArrNew[16]);


 
        writeln("\n\n\n\n\n");
        return IsoArr;
    } //end of runVF2
} // end of SubgraphIsomorphism module


// ... [existing module code] ...

proc recursiveVF2(state: State, g1: SegGraph, g2: SegGraph, depth: int) {
    // Base case: check if a complete mapping is found
    if state.depth == g2.n_vertices {
        // Process the found solution
        return;
    }

    // Generate candidate pairs (n1, n2) for mapping
    var candidatePairs = getCandidatePairs(state, g1, g2);

    // Iterate over candidate pairs
    for (n1, n2) in candidatePairs {
        if isFeasible(n1, n2, state, g1, g2) {
            // Update state with the new mapping
            addToTinTout(n1, n2);
            state.core2[n2] = n1;
            // Recursive call with updated state and increased depth
            recursiveVF2(state, g1, g2, depth+1);
            
            // Backtrack: remove the mapping added earlier
            state.core2[n2] = -1
            depth -= 1;
            // what about Tin, Tout?
        }
    }
}

proc runRecursiveVF2(g1: SegGraph, g2: SegGraph) {
    var initialState = new State(g2.n_vertices); // Initialize the state
    recursiveVF2(initialState, g1, g2, 0); // Start recursion with depth 0
}

// ... [Rest of module code] ...

