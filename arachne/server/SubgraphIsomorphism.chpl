module SubgraphIsomorphism {
    // Chapel modules.
    use Reflection;
    use List;
    use Random;
    use List;
    use IO;
    use Time;
    use Set;
    use SortedSet;
    use DistributedDeque;
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


    proc runVF2 (g1: SegGraph, g2: SegGraph, st: borrowed SymTab):[] int throws {
        var TimerArrNew:[0..13] real(64) = 0.0;

        var timerpreproc:stopwatch;
        timerpreproc.start();

        // Extract the g1/G/g information from the SegGraph data structure.
        var srcNodesG1 = toSymEntry(g1.getComp("SRC"), int).a;
        var dstNodesG1 = toSymEntry(g1.getComp("DST"), int).a;
        var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS"), int).a;
        var srcRG1 = toSymEntry(g1.getComp("SRC_R"), int).a;
        var dstRG1 = toSymEntry(g1.getComp("DST_R"), int).a;
        var segRG1 = toSymEntry(g1.getComp("SEGMENTS_R"), int).a;
        var nodeMapGraphG1 = toSymEntry(g1.getComp("NODE_MAP"), int).a;

        // Extract the g2/H/h information from the SegGraph data structure.
        var srcNodesG2 = toSymEntry(g2.getComp("SRC"), int).a;
        var dstNodesG2 = toSymEntry(g2.getComp("DST"), int).a;
        var segGraphG2 = toSymEntry(g2.getComp("SEGMENTS"), int).a;
        var srcRG2 = toSymEntry(g2.getComp("SRC_R"), int).a;
        var dstRG2 = toSymEntry(g2.getComp("DST_R"), int).a;
        var segRG2 = toSymEntry(g2.getComp("SEGMENTS_R"), int).a;
        var nodeMapGraphG2 = toSymEntry(g2.getComp("NODE_MAP"), int).a;

        // OLIVER NOTE: Normalize node labels and edge relationships id values so those of H match
        //              those of G to speed up semantic checks. 
        // In the SegGraph data structure for property graphs, there could be many different types 
        // of labels and relationships. Therefore, we will do some preprocessing here to normalize
        // all labels and relationships and place them into sets for quick intersections.
        var edgeRelationshipsGraphG1 = (g1.getComp("EDGE_RELATIONSHIPS"):(borrowed MapSymEntry(string, (string, borrowed SegStringSymEntry)))).stored_map;
        var nodeLabelsGraphG1 = (g1.getComp("VERTEX_LABELS"):(borrowed MapSymEntry(string, (string, borrowed SegStringSymEntry)))).stored_map;
        var edgeRelationshipsGraphG2 = (g2.getComp("EDGE_RELATIONSHIPS"):(borrowed MapSymEntry(string, (string, borrowed SegStringSymEntry)))).stored_map;
        var nodeLabelsGraphG2 = (g2.getComp("VERTEX_LABELS"):(borrowed MapSymEntry(string, (string, borrowed SegStringSymEntry)))).stored_map;
        var relationshipStringToInt, labelStringToInt = new map(string, int); 

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

        var convertedRelationshipsG1 = makeDistArray(g1.n_edges, set(int, parSafe=true));
        var convertedRelationshipsG2 = makeDistArray(g2.n_edges, set(int, parSafe=true));
        var convertedLabelsG1 = makeDistArray(g1.n_vertices, set(int, parSafe=true));
        var convertedLabelsG2 = makeDistArray(g2.n_vertices, set(int, parSafe=true));

        for (k,v) in zip(edgeRelationshipsGraphG1.keys(), edgeRelationshipsGraphG1.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do convertedRelationshipsG1[i].add(relationshipStringToInt[mapper[x]]);
        }

        for (k,v) in zip(edgeRelationshipsGraphG2.keys(), edgeRelationshipsGraphG2.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do convertedRelationshipsG2[i].add(relationshipStringToInt[mapper[x]]);
        }

        for (k,v) in zip(nodeLabelsGraphG1.keys(), nodeLabelsGraphG1.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do convertedLabelsG1[i].add(labelStringToInt[mapper[x]]);
        }

        for (k,v) in zip(nodeLabelsGraphG2.keys(), nodeLabelsGraphG2.values()) {
            var arr = toSymEntry(getGenericTypedArrayEntry(k,st), int).a;
            var mapper = getSegString(v[1].name,st);
            forall (x,i) in zip(arr, arr.domain) do convertedLabelsG2[i].add(labelStringToInt[mapper[x]]);
        }

        var Orig_Label_Mapper_G_to_Pass: [0..1] string;
        var Orig_Label_Mapper_H_to_Pass: [0..1] string;
        var Orig_Relationships_Mapper_G_to_Pass: [0..1] string;
        var Orig_Relationships_Mapper_H_to_Pass: [0..1] string;
        
        // OLIVER NOTE: Commenting this out for now because I am honestly not sure if it actually 
        //              improves performance at all. 
        // // make them local
        // var srcNodesG1: [0..<srcNodesG1Dis.size] int;        srcNodesG1 = srcNodesG1Dis;
        // var dstNodesG1: [0..<dstNodesG1Dis.size] int;        dstNodesG1 = dstNodesG1Dis;
        // var segGraphG1: [0..<segGraphG1Dis.size] int;        segGraphG1 = segGraphG1Dis;
        // //var edgeRelationshipsGraphG1: [0..<edgeRelationshipsGraphG1Dis.size] int;        edgeRelationshipsGraphG1 = edgeRelationshipsGraphG1Dis;
        // //var nodeLabelsGraphG1: [0..<nodeLabels_GraphG1Dis.size] int;        nodeLabelsGraphG1 = nodeLabels_GraphG1Dis;
        // //var nodeMapGraphG1: [0..<nodeMap_GraphG1Dis.size] int;        nodeMapGraphG1 = nodeMap_GraphG1Dis;
        // var srcRG1: [0..<srcRG1Dis.size] int;        srcRG1 = srcRG1Dis;
        // var dstRG1: [0..<dstRG1Dis.size] int;        dstRG1 = dstRG1Dis;
        // var segRG1: [0..<segRG1Dis.size] int;        segRG1 = segRG1Dis;

        // // make them local
        // var srcNodesG2: [0..<srcNodesG2Dis.size] int;        srcNodesG2 = srcNodesG2Dis;
        // var dstNodesG2: [0..<dstNodesG2Dis.size] int;        dstNodesG2 = dstNodesG2Dis;
        // var segGraphG2: [0..<segGraphG2Dis.size] int;        segGraphG2 = segGraphG2Dis;
        // //var edgeRelationshipsGraphG2: [0..<edgeRelationshipsGraphG2Dis.size] int;        edgeRelationshipsGraphG2 = edgeRelationshipsGraphG2Dis;
        // //var nodeLabelsGraphG2: [0..<nodeLabels_GraphG2Dis.size] int;        nodeLabelsGraphG2 = nodeLabels_GraphG2Dis;
        // //var nodeMapGraphG2: [0..<nodeMap_GraphG2Dis.size] int;        nodeMapGraphG2 = nodeMap_GraphG2Dis;
        // var srcRG2: [0..<srcRG2Dis.size] int;        srcRG2 = srcRG2Dis;
        // var dstRG2: [0..<dstRG2Dis.size] int;        dstRG2 = dstRG2Dis;
        // var segRG2: [0..<segRG2Dis.size] int;        segRG2 = segRG2Dis;
        timerpreproc.stop();
        TimerArrNew[0] += timerpreproc.elapsed();
        
        var timerVF2:stopwatch;
        timerVF2.start();
        var IsoArrtemp = vf2(g1, g2);
        timerVF2.stop();
        TimerArrNew[1] += timerVF2.elapsed();

        var IsoArr = nodeMapGraphG1[IsoArrtemp];

        proc PropGraphRelationshipMapper(segGraph, dstNodes, edgeRelationshipsGraph, 
                                        fromNode: int, toNode: int) throws {
            //writeln("-----------------PropGraphRelationshipMapper called-------------------\n");
            // and you should be aware of more than one relation, think about it!! ask Oliver

            var BoolValue : bool = false;
            var StringLabelValue : string;

            // Check if there is an edge from "fromNode" to "toNode" in PropGraph
            var adj_list_of_fromNode_start = segGraph[fromNode];
            var adj_list_of_fromNode_end = segGraph[fromNode+1]-1;
            
            var Edge_found = bin_search_v(dstNodes, adj_list_of_fromNode_start, adj_list_of_fromNode_end, toNode);
            var temp = new set(int, parSafe=true);

            if Edge_found > -1 then {
                BoolValue = true;
                
                var rels = edgeRelationshipsGraph[Edge_found];
                // for elemnts in setToConvert{
                //     StringLabelValue = Mapper[elemnts];
                // }
                return(BoolValue, rels);

            }

            return (BoolValue, temp);

        }  // end of PropGraphRelationshipMapper
        // proc PropGraphNodeLabelMapper(nodeLabels_Graph, srearchNode: int, Mapper): (bool, string) throws {
        //     //writeln("-----------------PropGraphNodeLabelMapper called-------------------\n");

        //     var BoolValue : bool = false;
        //     var StringLabelValue : string;

        
        //     var setToConvert =  convertedLabelsG1[srearchNode];

        //     // remember make a time to write an IF to check the existing of index!!
        //     // if it was out of range return FALSE
        //     // and you should be aware of more than one label, think about it!! ask Oliver
        //     for elemnts in setToConvert{
        //             StringLabelValue = Mapper[elemnts];
        //     }
        //     if StringLabelValue.size > 0 then {
        //     BoolValue = true;
        //     } // If there is at least 1 label, print out the string representation of the one at index 0.
            
        //     return (BoolValue, StringLabelValue);
        // }

        // State record 
        record State {
            var n1: int;
            var n2: int;

            var core1:  map(int, int);
            var core2:  map(int, int);
            
            // Other state fields

            // Initialize sets
            var mapping: set((int , int)); 

            //to track the depth in the search tree
            var depth: int;
            
            // current cost of the mapping
            var cost: real;

            // Tin tracks in-neighbors - nodes with edges to current partial mapping
            // Tout tracks out-neighbors - nodes with edges from current mapping
            var Tin1: domain(int); 
            var Tout1: domain(int);

            var Tin2: domain(int);
            var Tout2: domain(int);

            // State initializer
            proc init() {
                this.n1 = 0;
                this.n2 = 0;

                this.core1 = new map(int, int);
                this.core2 = new map(int, int);
                
                this.mapping = new set((int, int));
                // I didnt use these 2 variables
                // I added cost in case of wieght on edge or something like that
                // depth in case of I wanted to check reaching the size of subgraph
                // which I changed my mind and didnt use 
                this.depth = 0;
                
                this.cost = 0.0;

                this.Tin1  =  {1..0};
                this.Tout1 =  {1..0};

                this.Tin2  =  {1..0};
                this.Tout2 =  {1..0};
            }  
            // Initialize based on graph sizes
            proc init(n1, n2) {
                this.n1 = n1;
                this.n2 = n2;

                this.core1 = new map(int, int);
                this.core2 = new map(int, int);

                this.mapping = new set((int, int));
            
                this.depth = 0;
                this.cost = 0.0; 

                this.Tin1  =  {1..0};
                this.Tout1 =  {1..0};

                this.Tin2  =  {1..0};
                this.Tout2 =  {1..0};   
            }
            // Copy state
            proc copy() {
                var state = new State(n1, n2);

                state.core1 = this.core1;
                state.core2 = this.core2;
                
                state.mapping = this.mapping;  
            
                state.depth = this.depth;
                state.cost = this.cost;
                
                state.Tin1 = this.Tin1;
                state.Tout1 = this.Tout1;

                state.Tin2 = this.Tin2;
                state.Tout2 = this.Tout2;

                return state;
            }

            // Resetting vectors when backtracking
            proc reset() {

                mapping.clear(); // reset to empty

                core1.clear();
                core2.clear();

                depth -= 1;
                cost -= 1;

                Tin1.clear();
                Tout1.clear();

                Tin2.clear();
                Tout2.clear(); 
            }
            
            // Add node pair to mapping 
            proc addPair(x1: int, x2: int) {
                // Update core mapping

                core1.add(x1, x2);
                core2.add(x2, x1);

                // Add pair to mapping
                mapping.add((x1, x2));

                // Increment depth 
                depth += 1;

            }

            // Check if node of g1 is mapped 
            proc isMappedn1(node: int): bool {

                // Check node within bounds
                if node >= 0 && node < n1 { // wasting time?!!!!
                    // Node is from g1, check core1
                    if core1.contains(node) {
                        return true;
                    }
                }
                // Node outside bounds, return false
                return false;
            }
            // Check if node of g2 is mapped 
            proc isMappedn2(node: int): bool {

                // Check node within bounds
                if node >= 0 && node < n2 {

                    // Node is from g2, check core2
                    if core2.contains(node) {
                        return true;
                    }
                }
                // Node outside bounds, return false
                return false;
            }

        } // end of State record

        // try again to add it to state record!! 
        proc addToTinTout(ref state: State, u : int, v: int): State throws {
            //writeln("-----------------addToTinTout called-------------------");
            //writeln("-----------------for", u, ", ", v, "-------------------\n");

            // Get in and out neighbors
            var adj_list_of_node_start = segRG1[u];
            var adj_list_of_node_end = segRG1[u + 1]-1;

            var inNeighbors = dstRG1[adj_list_of_node_start..adj_list_of_node_end];

            adj_list_of_node_start = segGraphG1[u];
            adj_list_of_node_end = segGraphG1[u + 1]-1;
            
            var outNeighbors = dstNodesG1[adj_list_of_node_start..adj_list_of_node_end];

            // Add neighbors of u to tin1, tout1 from g1
            if state.Tin1.contains(u) {
                state.Tin1.remove(u); 
            }

            if state.Tout1.contains(u) {
                state.Tout1.remove(u);
            }

            // Add unmapped neighbors to Tin
            for n1 in inNeighbors {
                //if state.core1[n1] == -1 {
                if !state.core1.contains(n1) {
                    state.Tin1.add(n1);
                }
            }
            // Add unmapped neighbors to Tout
            for n1 in outNeighbors {
                //if state.core1[n1] == -1 {
                if !state.core1.contains(n1) {
                    state.Tout1.add(n1);
                }
            }

            // Add neighbors of v to tin2, tout2 from g2

            // Get in and out neighbors
            adj_list_of_node_start = segRG2[v];
            adj_list_of_node_end = segRG2[v + 1]-1;

            var inNeighborsg2 = dstRG2[adj_list_of_node_start..adj_list_of_node_end];

            adj_list_of_node_start = segGraphG2[v];
            adj_list_of_node_end = segGraphG2[v + 1]-1;
            
            var outNeighborsg2 = dstNodesG2[adj_list_of_node_start..adj_list_of_node_end];

            if state.Tin2.contains(v) {
                state.Tin2.remove(v); 
            }
            if state.Tout2.contains(v) {
                state.Tout2.remove(v);
            }
            // Add unmapped neighbors to Tin
            //forall n2 in inNeighborsg2 with(ref state){
            for n2 in inNeighborsg2 {
                //if state.core2[n2] == -1 {
                if !state.core2.contains(n2) {
                    
                    state.Tin2.add(n2);
                }
            }
            // Add unmapped neighbors to Tout
            //forall n2 in outNeighborsg2 with(ref state){
            for n2 in outNeighborsg2 {
                //if state.core2[n2] == -1 {
                if !state.core2.contains(n2) {
                    state.Tout2.add(n2);
                }
            }

            return state;
            
        } // end of addToTinTout

        // Create initial state with empty mappings, vectors, etc
        proc createInitialState(): State throws {
            //writeln("-----------------createInitialState called-------------------\n");

            var state = new State();

            state.init(g1.n_vertices, g2.n_vertices);
            /*
            ///test
            state.addPair(1, 0);
            state = addToTinTout(newState, 1, 0);            
            
            state.addPair(3, 1);
            state = addToTinTout(newState, 3, 1);
            ///test
            */
            return state;

        }  //end of createInitialState

        var timergetUnmappedNodesg1:stopwatch;
        timergetUnmappedNodesg1.start();
        // Two silly function. wrote just to quick check but worked.LOL
        proc getUnmappedNodesg1(graph: SegGraph, state: State) throws {
            //writeln("-----------------getUnmappedNodesg1 called-------------------\n");
            var unmapped: list(int) = 0..#graph.n_vertices;
            for key in state.core1.keys(){
                unmapped.remove(key);
            }

            return unmapped;
        } // end of getUnmappedNodesg1
        timergetUnmappedNodesg1.stop();
        TimerArrNew[5] += timergetUnmappedNodesg1.elapsed();

        var timergetUnmappedNodesg2:stopwatch;
        timergetUnmappedNodesg2.start();
        proc getUnmappedNodesg2(graph, state) throws {
            //writeln("-----------------getUnmappedNodesg2 called-------------------\n");

            var unmapped: list(int);//
            //var values = [1, 0, 2, 3];// ordered based on degree- I had worse results
            for n in 0..<graph.n_vertices { 
            //for n in values{    
                if !state.isMappedn2(n) {
                    unmapped.pushBack(n);
                }
            }

            return unmapped;
        } // end of getUnmappedNodesg2
        
        timergetUnmappedNodesg2.stop();
        TimerArrNew[6] += timergetUnmappedNodesg2.elapsed();



        // Create candidates based on current state and retuns a list of pairs
        // based on old paper!!
        proc getCandidatePairsOpti(state:State) throws {
            //writeln("-----------------getCandidatePairsOpti called-------------------\n");
            //writeln("state = ", state);
            //////////////////////// new version added Dec 5
            var timergetCandidatePairsOpti:stopwatch;
            timergetCandidatePairsOpti.start();
            
            var candidates = new set((int, int), parSafe = true);
            
            var unmapped2 = getUnmappedNodesg2(g2, state);

            // If Tout1 and Tout2 are both nonempty.
            if state.Tout1.size > 0 && state.Tout2.size > 0 {
                
                var minTout2 = min reduce state.Tout2;
                //forall n1 in state.Tout1 with (ref candidates){
                for n1 in state.Tout1 {
                    //writeln("HERE 1");
                    candidates.add((n1, minTout2)); 
                }
                
            } 
                else {
                    //If Tin1 and Tin2 are both nonempty. 
                    if state.Tin1.size > 0 && state.Tin2.size > 0{
                        var minTin2 = min reduce state.Tin2;

                        //forall n1 in state.Tin1 with (ref candidates){
                        for n1 in state.Tin1 {
                            //writeln("HERE 2");
                            candidates.add((n1, minTin2)); 
                        }
                    } else { //not (Tin1 or Tin2)
                                if unmapped2.size >0 {
                                    var minUnmapped2 = min reduce unmapped2;
                                    //forall n1 in unmapped1 with (ref candidates){
                                    //for n1 in unmapped1 {
                                    //forall n1 in 0..#g1.n_vertices with (ref candidates) {
                                    for n1 in 0..#g1.n_vertices{
                                        if !state.core1.contains(n1){
                                            candidates.add((n1, minUnmapped2));
                                        }    
                                    }
                                }    
                            } 
                }   
            //writeln("candidates = ", candidates);
            timergetCandidatePairsOpti.stop();
            TimerArrNew[7] += timergetCandidatePairsOpti.elapsed();
            return candidates;

        } // end of getCandidatePairsOPti




        // Check node labels are the same
        proc nodesLabelCompatible(n1: int, n2: int): bool throws {
            //writeln("-----------------nodesLabelCompatible called-------------------\n");
            var timernodesLabelCompatible:stopwatch;
            timernodesLabelCompatible.start();
            if (convertedLabelsG1[n1] & convertedLabelsG1[n2]).size <= 0 {
                timernodesLabelCompatible.stop();
                TimerArrNew[4] += timernodesLabelCompatible.elapsed();                
                return false;
            }
            timernodesLabelCompatible.stop();
            TimerArrNew[4] += timernodesLabelCompatible.elapsed();
            return true;
        }// end of nodesLabelCompatible



        // Check if candidates' pairs are feasible
        proc isFeasible(state: State, n1: int, n2: int) throws {
            
            var timerisFeasible:stopwatch;
            timerisFeasible.start();
            //writeln("-----------------isFeasible called for (",n1,",", n2,")-------------------");
            //////////////////////// new version added Dec 13
            var termout1, termout2, termin1, termin2, new1, new2 : int =0 ;

            if !nodesLabelCompatible(n1, n2) {
                //writeln("Node labels are Inconsistent");
                timerisFeasible.stop();
                TimerArrNew[2] += timerisFeasible.elapsed();
                return false;
            }
            // Out Neighbours of G1
            var adj_list_of_node_start = segGraphG1[n1];
            var adj_list_of_node_end = segGraphG1[n1 + 1]-1;
            
            var getOutN1 = dstNodesG1[adj_list_of_node_start..adj_list_of_node_end];

            // Out Neighbours of G2
            adj_list_of_node_start = segGraphG2[n2];
            adj_list_of_node_end = segGraphG2[n2 + 1]-1;
            
            var getOutN2 = dstNodesG2[adj_list_of_node_start..adj_list_of_node_end];
         
            // Check out neighbors of n2 
            for Out2 in getOutN2 {
                if state.isMappedn2(Out2) {
                    var Out1 = state.core2(Out2);
                    // Check edge compatibility
                    var (flag1, label1) = PropGraphRelationshipMapper(segGraphG1, dstNodesG1, convertedRelationshipsG1, n1, Out1);
                    var (flag2, label2) = PropGraphRelationshipMapper(segGraphG2, dstNodesG2, convertedRelationshipsG1, n2, Out2);
            
                    if !flag1 || (label2 & label1).size < 0 {
                        timerisFeasible.stop();
                        TimerArrNew[2] += timerisFeasible.elapsed();
                        return false;
                    }
                } 
                else {
                    
                    if state.Tin2.contains(Out2){
                        termin2 += 1;
                    }
                    if state.Tout2.contains(Out2){
                        termout2 += 1;
                    }
                    if !state.Tin2.contains(Out2) && !state.Tout2.contains(Out2){
                        new2 += 1;
                    }
                }
            }
            
            // In Neighbours of G1
            adj_list_of_node_start = segRG1[n1];
            adj_list_of_node_end = segRG1[n1 + 1]-1;

            var getInN1 = dstRG1[adj_list_of_node_start..adj_list_of_node_end];
            
            // In Neighbours of G2
            adj_list_of_node_start = segRG2[n2];
            adj_list_of_node_end = segRG2[n2 + 1]-1;

            var getInN2 = dstRG2[adj_list_of_node_start..adj_list_of_node_end];

            // Check In neighbors of n2 
            for In2 in getInN2 {
                if state.isMappedn2(In2) {
                    var In1 = state.core2(In2);
                    // Check edge compatibility
                    var (flag1, label1) = PropGraphRelationshipMapper(segGraphG1, dstNodesG1, convertedRelationshipsG1, In1, n1);
                    var (flag2, label2) = PropGraphRelationshipMapper(segGraphG2, dstNodesG2, convertedRelationshipsG2, In2, n2);
            
                    if !flag1 || (label2 & label1).size <= 0 {
                        timerisFeasible.stop();
                        TimerArrNew[2] += timerisFeasible.elapsed();
                        return false;
                    }
                }
                else {
                    if state.Tin2.contains(In2){
                        termin2 += 1;
                    }
                    if state.Tout2.contains(In2){
                        termout2 += 1;
                    }
                    if !state.Tin2.contains(In2) && !state.Tout2.contains(In2){
                        new2 += 1;
                    }
                }
            }
            
            // Check Out neighbors of n1 
            for Out1 in getOutN1 {
                if state.isMappedn1(Out1) {
                    //Nothing to do
                }
                else {
                    if state.Tin1.contains(Out1){
                        termin1 += 1;
                    }
                    if state.Tout1.contains(Out1){
                        termout1 += 1;
                    }
                    if !state.Tin1.contains(Out1) && !state.Tout1.contains(Out1){
                        new1 += 1;
                    }
                }
            }
            // Check In neighbors of n1 
            for In1 in getInN1 {
                if state.isMappedn1(In1) {
                    //Nothing to do
                }
                else {
                    if state.Tin1.contains(In1){
                        termin1 += 1;
                    }
                    if state.Tout1.contains(In1){
                        termout1 += 1;
                    }
                    if !state.Tin1.contains(In1) && !state.Tout1.contains(In1){
                        new1 += 1;
                    }
                }
            }
            timerisFeasible.stop();
            TimerArrNew[2] += timerisFeasible.elapsed();
            return termin2<=termin1 && termout2<=termout1 && (termin2+termout2+new2)<=(termin1+termout1+new1);
        }// end of isFeasible

        

        // DFS like to traverse graph and returns list of all solution states 
        proc dfs(ref initialState: State, g1: SegGraph, g2: SegGraph): list (set((int, int))) throws {
            var timerDFS:stopwatch;
            timerDFS.start();
            //writeln("-----------------dfs called-------------------\n");

            var allmappings: list (set((int, int)));
           // Stack defined for backtracking
           // parSafe to be sure that no race condition
            var stack: list(State, parSafe = true);
            
            // Initialize stack
            stack.pushBack(initialState);
            //writeln("initialState pushed to stack", initialState);

            while stack.size > 0 {
                var state = stack.popBack();
                if state.mapping.size == g2.n_vertices {

                    allmappings.pushBack(state.mapping);
                }

                var candidatesOpti = getCandidatePairsOpti(state);


                //forall (n1, n2) in candidatesOpti with(ref stack) {
                for (n1, n2) in candidatesOpti {
                    if isFeasible(state, n1, n2) {
                        var newState = state.copy();
                        newState.addPair(n1, n2);
                        newState = addToTinTout(newState, n1, n2);
                        stack.pushBack(newState);
                    }
                }
                //writeln("end of checking all current candidates\n");
                state.reset();
            }
            timerDFS.stop();
            TimerArrNew[3] += timerDFS.elapsed();
            return allmappings; // Isomappings
            
        }  //end of dfs 


        // Main procudre of VF2 Subgraph Isomorphism
        proc vf2(g1: SegGraph, g2: SegGraph): [] int throws {
            //writeln("-----------------vf2 called-------------------\n");
            
            var initial = createInitialState();

            var solutions = dfs(initial, g1, g2);

            var subIsoArrToReturn: [0..(solutions.size*g2.n_vertices)-1](int);

            var posOffset = 0;
            // just to have a nice and readable output? should I get ride of it?!!!!! 
            for solSet in solutions {
                for (n1, n2) in solSet {
                    subIsoArrToReturn[posOffset + n2] = n1;
                }
                posOffset += g2.n_vertices;
            }

            return(subIsoArrToReturn);
        } //end of VF2
        
        for i in 0..13 {
            if i == 0 {
                writeln("Preprocessing total time = ", TimerArrNew[0]);
            }              
            if i == 1 {
                writeln("\nVF2 total time = ", TimerArrNew[1]);
            }            
            if i == 2 {
                writeln("\nisFeasible total time = ", TimerArrNew[2]);
            }            
            if i == 3 {
                writeln("\nDFS total time = ", TimerArrNew[3]);
            }            
            if i == 4 {
                writeln("\nnodesLabelCompatible total time = ", TimerArrNew[4]);
            }            
            if i == 7 {
                writeln("\ngetCandidatePairsOpti total time = ", TimerArrNew[7]);
            }
        }
        return IsoArr;

    } //end of runVF2

} // end of SubgraphIsomorphism module