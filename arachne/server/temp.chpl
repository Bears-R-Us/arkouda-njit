       proc dfs(ref initialState: State, g1: SegGraph, g2: SegGraph):list(set((int, int))) throws {
 


        /** Main procedure that invokes all of the vf2 steps using the graph data that is
        initialized by `runVF2`.*/
        proc vf2(g1: SegGraph, g2: SegGraph): [] int throws {
            Create Initial State;
            Push Initial State to Stack; // Initialize stack.

            while stack is not EMPTY{
                Pop from stack;
                if state covers all the nodes of G2. output it mappings 
                
                Compute Candidates based on curent state;

                for all (n1, n2) in candidatesOpti {
                    if it is Feasible {
                        add pair to state;
                        add edges from/to new pair to statet;
                        push state to stack;
                        stack.pushBack(newState);
                    }
                }
                reset the state; 
            }
            return mappings; // Isos' mappings
        } //end of vf2
        
        isFeasible tries to check 2 different (syntactic and semantic) category of rules.
        semantic attributes which depends on atributes(here is the best palce to discuss the power of property graph 
        data structure to handle labels and relations)
        syntatic category contains 5 ruls. 
        
        proc isFeasible:
            INPUT: state, candidate pair n1, new
            OUTPUT: True, False
            
            check labels: 
                        candidates pair nodesLabel are to be compatible for labels
            
            Find all out_neighbors(successors) of n1 and n2;
            Find all in_neighbors(predessors) of n1 and n2
            
            check Rpred (topological consistency):
                        It checks that the mappings of the predecessor nodes of n1 and n2 are consistent with 
                        the existing mappings in the given state.
            check Rsucc (topological consistency):
                        It ensures that the structural relationship of successor nodes of n1 and n2 is preserved in 
                        the mapping. This rule is essential for pruning the search space and ensuring the integrity of 
                        the subgraph isomorphism being find.
            check Rin:
                        this focuses on ensuring that the candidate pair (n1, n2) being considered for the mapping
                        does not violate the in-degree constraints. This is done by comparing the number of successor and 
                        predecessor nodes of n1 and n2 that are not already part of the partial mapping. 
                        The rule enforces that n1 in G1 should not have more successors (or predecessors) outside the 
                        current mapping than n2 in G2. This condition helps in pruning the search space effectively.
            check Rout:
                        The Rout rule is for ensuring that the candidate pair does not violate out-degree constraints in 
                        the VF2 algorithm. It checks that the number of connections n1 and n2 have with nodes not yet 
                        included in the mapping is consistent and follows the subgraph isomorphism rules. 
                        The rule ensures that the node n1 in G1 should not have more successors (or predecessors) outside 
                        the current mapping than n2 in G2. This constraint is essential for maintaining the structural 
                        integrity of the subgraph isomorphism.
            check Rnew:
                        The Rnew rule is designed to ensure that the candidate pair (n1, n2) being considered for 
                        inclusion in the mapping is compatible in terms of their relationships with nodes not yet included
                        in the mapping. This rule looks at both predecessor and successor nodes of n1 and n2, comparing 
                        their counts with the nodes outside the current mapping. In essence, this rule checks whether the 
                        potential addition of (n1, n2) to the mapping would maintain the consistency of the graph structure, 
                        particularly with respect to nodes that are yet to be mapped. It ensures that n1 does not have more 
                        external (outside the current mapping) predecessor or successor connections than n2. 
                        This constraint helps in reducing the search space by pruning candidate pairs that cannot be part 
                        of a valid isomorphism, thus enhancing the efficiency of the VF2 algorithm.           




        proc getCandidatePairsOpti(state:State) {
            calculate G2 Unmapped nodes; 
            calculate G1 Unmapped nodes; 

            If Tout1 and Tout2 are both nonempty.
                Candidate set = Tout1 X min {Tout2} (min can be any ordering criterion. we choose index)
            else 
                If Tin1 and Tin2 are both nonempty
                    Candidate set = Tin1 X min{Tin2}
                else
                    If All Tin1,Tin2,Tout1, Tout2 are empty  and still have G2 Unmmaped node 
                        

            } else {
                //If Tin1 and Tin2 are both nonempty.
                if state.Tin1.size > 0 && state.Tin2.size > 0 {
                    var minTin2 = min reduce state.Tin2;
                    for n1 in state.Tin1 do candidates.add((n1, minTin2));
                } else { // not (Tin1 or Tin2) NOTE: What does this mean?
                    if unmapped.size > 0 {
                        var minUnmapped = min reduce unmapped;
                        for n1 in 0..#g1.n_vertices do if !state.core1.contains(n1) then candidates.add((n1, minUnmapped));
                    }
                } 
            }   
            timergetCandidatePairsOpti.stop();
            TimerArrNew[7] += timergetCandidatePairsOpti.elapsed();
            return candidates;
        } // end of getCandidatePairsOpti


 
        } // end of isFeasible