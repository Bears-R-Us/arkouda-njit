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

    class Cluster {
        //var id: int; // cluster id
        var n_member: int; // size of cluster
            
        var members: [0..<n_member] int;
        var is_wcc: bool;

        var depth:int; // clustering depth

        /** Cluster initializer.*/
        proc init(id: int, membersArray: [] int) {
            this.id = id;
            this.n_member = membersArray.size;
            
            this.members = membersArray;
            this.is_wcc = false;
            this.depth = 0;
        }
        proc removeDegreeOne() {
            //claculate cluster degree and remove the nodes with degree 1
            //update cluster nodes
        }


    } // end of Cluster class 

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
        SortSubGraphbyDegree();
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
        writeln("\n_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*");
        writeln("\n_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*");
        
        //writeln("\nDomain check = ", IsoArrtemp.domain == IsoArr.domain );
        //writeln("\nEquality check = ",IsoArrtemp.equals(IsoArr));


        /** Generate in-neighbors and out-neighbors for a given subgraph state.*/
        proc addToTinTout (u: int, v: int, state: State): int throws {
            state.core[v] = u; // v from g2 to a u from g1
            state.depth += 1; // a pair of vertices were mapped therefore increment depth by 1
if state.depth==g2.n_vertices{
            return 1;

} else {
            var inNeighbors = dstRG1[segRG1[u]..<segRG1[u+1]];
            var outNeighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];

            state.Tin1.remove(u);
            state.Tout1.remove(u);
            
            state.Tin1 += inNeighbors;
            state.Tout1 += outNeighbors;
            
            for i in state.D_core do if state.core[i] != -1 then state.Tin1.remove(state.core[i]);
            for i in state.D_core do if state.core[i] != -1 then state.Tout1.remove(state.core[i]);

            //for n1 in inNeighbors do if !state.isMappedn1(n1) then state.Tin1.add(n1);
            //for n1 in outNeighbors do if !state.isMappedn1(n1) then state.Tout1.add(n1);
  
            var inNeighborsg2 = dstRG2[segRG2[v]..<segRG2[v+1]];            
            var outNeighborsg2 = dstNodesG2[segGraphG2[v]..<segGraphG2[v+1]];

            state.Tin2.remove(v);
            state.Tout2.remove(v);

            for n2 in inNeighborsg2 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
            for n2 in outNeighborsg2 do if !state.isMappedn2(n2) then state.Tout2.add(n2);
            return 1;
}


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
            if state.depth ==0 {
                    var (unmappedG1, unmappedG2) = getBothUnmappedNodes(state);
                    //var flagunmappedG2 = false;
                    //var minUnmapped2 : int;

                    if unmappedG2 != -1 {
                        for i in 0..<state.n1 {
                            if unmappedG1[i] == -1 then candidates.add((i,unmappedG2));
                        } 
                    }
  
            return candidates;
            }
            else {
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
            }

        } // end of getCandidatePairsOpti
            
                    /** Create candidates based on current state and retuns a set of pairs.*/
        proc getCandidatePairsOpti_light(state: State): set((int, int)) throws {
            var candidates = new set((int, int), parSafe = true);

                    var (unmappedG1, unmappedG2) = getBothUnmappedNodes(state);
                    //var flagunmappedG2 = false;
                    //var minUnmapped2 : int;

                    if unmappedG2 != -1 {
                        for i in 0..<state.n1 {
                            if unmappedG1[i] == -1 then candidates.add((i,unmappedG2));
                        } 
                    }
  
            return candidates;
        } // end of getCandidatePairsOpti_light
           
        /** Creates an initial, empty state.*/

        proc createInitialClusters(id: int, membersArray: [] int): Cluster throws{
            // Create a Cluster object with the members from 'membersArray'
            return new owned Cluster(id, membersArray);
        }

        /** Check that node labels are the same.*/
        proc nodesLabelCompatible(n1: int, n2: int): bool throws {
            var labelsG1n1 = convertedLabelsG1[n1];
            var labelsG2n2 = convertedLabelsG2[n2];

            if labelsG1n1 != labelsG2n2 then return false;

            return true;
        } // end of nodesLabelCompatible

        /** Perform the vf2 recursive steps returning all found isomorphisms.*/
        proc wccHelper(cluster: owned Cluster, depth: int): list(int) throws {
            var allmappings: list(int, parSafe=true);

            // Base case: check if a complete mapping is found
            if cluster.is_wcc == true; {
                //writeln("Isos found = ", state.core);
                // Process the found solution
                for elem in state.core do allmappings.pushBack(elem);
                return allmappings;
            }

                // Generate candidate pairs (n1, n2) for mapping
                var candidateClusters = getCandidatePairsOpti(state);
                //writeln("\nstate depth = ", state.depth, " Candidte size = ", candidatePairs.size);
                // Iterate in parallel over candidate pairs
                forall (n1, n2) in candidateClusters with (ref state, ref allmappings) {
                //for (n1, n2) in candidatePairs {
                    if isFeasible(n1, n2, state) {
                        var newState = state.clone();

                        // Update state with the new mapping
                        addToTinTout(n1, n2, newState);

                        // Recursive call with updated state and increased depth
                        var newMappings: list(int, parSafe=true);
                        newMappings = wccHelper(newState, depth + 1);
                        
                        // Use a loop to add elements from newMappings to allmappings
                        for mapping in newMappings do allmappings.pushBack(mapping);
                    }
                }
            
       // }

            return allmappings;
        }
        

        proc wcc(g1: SegGraph, inputArrOfArrs: [] [] int): [] int throws {
            //var inputArrOfArrs: [] [] int;
            for i in 0..inputArrOfArrs.size {
                var initial = createInitialClusters(i, inputArrOfArrs[i]);
                var solutions = wccHelper(initial);
            }

            //var solutions = wccHelper();
            var subIsoArrToReturn: [0..#solutions.size](int);
            for i in 0..#solutions.size do subIsoArrToReturn[i] = solutions(i);
            return(subIsoArrToReturn);
        } // end of WCC

        
        return IsoArr;
    } //end of runWCC
} // end of WellConnected module

        

