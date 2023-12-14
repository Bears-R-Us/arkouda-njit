module SubgraphIsomorphismVF2 {
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
    // Global 
    // Global counter for isomorphisms
    proc runVF2 (g1: SegGraph, g2: SegGraph, SubgraphDegree: [?D1] int, 
                    graphDegree: [?D2] int, Orig_Label_Mapper_G_to_Pass: [?D3] string, 
                    Orig_Label_Mapper_H_to_Pass: [?D4] string, Orig_Relationships_Mapper_G_to_Pass: [?D5] string, 
                    Orig_Relationships_Mapper_H_to_Pass: [?D6] string):[] int throws {
        
        // Extract the g1/G information from PropGraph DS
        var srcNodesG1 = toSymEntry(g1.getComp("SRC"), int).a;
        var dstNodesG1 = toSymEntry(g1.getComp("DST"), int).a;
        var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS"), int).a;
        var edgeRelationshipsGraphG1 = toSymEntry(g1.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var nodeLabels_GraphG1 = toSymEntry(g1.getComp("VERTEX_LABELS"), domain(int)).a;
        var nodeMap_GraphG1 = toSymEntry(g1.getComp("NODE_MAP"), int).a;
        var srcRG1 = toSymEntry(g1.getComp("SRC_R"), int).a;
        var dstRG1 = toSymEntry(g1.getComp("DST_R"), int).a;
        var segRG1 = toSymEntry(g1.getComp("SEGMENTS_R"), int).a;

        // Extract the g2/H information from PropGraph DS
        var srcNodesG2 = toSymEntry(g2.getComp("SRC"), int).a;
        var dstNodesG2 = toSymEntry(g2.getComp("DST"), int).a;
        var segGraphG2 = toSymEntry(g2.getComp("SEGMENTS"), int).a;
        var edgeRelationshipsGraphG2 = toSymEntry(g2.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var nodeLabels_GraphG2 = toSymEntry(g2.getComp("VERTEX_LABELS"), domain(int)).a;
        var srcRG2 = toSymEntry(g2.getComp("SRC_R"), int).a;
        var dstRG2 = toSymEntry(g2.getComp("DST_R"), int).a;
        var segRG2 = toSymEntry(g2.getComp("SEGMENTS_R"), int).a;

         
        //var IsoArr:[0..1] int;
        
        // I don't like this part and preparing output
        // it is wasting memory and time!!!
        var IsoArrtemp = vf2(g1, g2);

        var IsoArr = nodeMap_GraphG1[IsoArrtemp];        
        //writeln("inside VF2 IsoArr     = ", IsoArr);

        proc PropGraphRelationshipMapper(segGraph, dstNodes, edgeRelationshipsGraph, 
                                        fromNode: int, toNode: int, Mapper): (bool, string) throws {
            //writeln("-----------------PropGraphRelationshipMapper called-------------------\n");
            // and you should be aware of more than one relation, think about it!! ask Oliver

            var BoolValue : bool = false;
            var StringLabelValue : string;

            // Check if there is an edge from "fromNode" to "toNode" in PropGraph
            var adj_list_of_fromNode_start = segGraph[fromNode];
            var adj_list_of_fromNode_end = segGraph[fromNode+1]-1;
            
            var Edge_found = bin_search_v(dstNodes, adj_list_of_fromNode_start, adj_list_of_fromNode_end, toNode);

            if Edge_found > -1 then {
                BoolValue = true;
                
                var setToConvert = edgeRelationshipsGraph[Edge_found];
                for elemnts in setToConvert{
                    StringLabelValue = Mapper[elemnts];
                }

            }

            return (BoolValue, StringLabelValue);

        }  // end of PropGraphRelationshipMapper
        proc PropGraphNodeLabelMapper(nodeLabels_Graph, srearchNode: int, Mapper): (bool, string) throws {
            //writeln("-----------------PropGraphNodeLabelMapper called-------------------\n");

            var BoolValue : bool = false;
            var StringLabelValue : string;

        
            var setToConvert =  nodeLabels_Graph[srearchNode];

            // remember make a time to write an IF to check the existing of index!!
            // if it was out of range return FALSE
            // and you should be aware of more than one label, think about it!! ask Oliver
            for elemnts in setToConvert{
                    StringLabelValue = Mapper[elemnts];
            }
            if StringLabelValue.size > 0 then {
            BoolValue = true;
            } // If there is at least 1 label, print out the string representation of the one at index 0.
            
            return (BoolValue, StringLabelValue);
        }

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
            return state;

        }  //end of createInitialState
        // Two silly function. wrote just to quick check but worked.LOL
        proc getUnmappedNodesg1(graph: SegGraph, state: State) throws {
            //writeln("-----------------getUnmappedNodesg1 called-------------------\n");
            var unmapped: list(int) = 0..#graph.n_vertices;
            for key in state.core1.keys(){
                unmapped.remove(key);
            }

            return unmapped;
        } // end of getUnmappedNodesg1

        proc getUnmappedNodesg2(graph, state) throws {
            //writeln("-----------------getUnmappedNodesg2 called-------------------\n");

            var unmapped: list(int);
            for n in 0..<graph.n_vertices {
                if !state.isMappedn2(n) {
                    unmapped.pushBack(n);
                }
            }

            return unmapped;
        } // end of getUnmappedNodesg2
        

        // Create candidates based on current state and retuns a list of pairs
        // based on old paper!!
        proc getCandidatePairsOpti(state:State) throws {
            //writeln("-----------------getCandidatePairsOpti called-------------------\n");
//////////////////////// new version added Dec 5

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
            //if candidates.size == 0 then writeln("We made a huge mistake");
            return candidates;

        } // end of getCandidatePairsOPti
        
        // Check node labels are the same
        proc nodesLabelCompatible(n1: int, n2: int): bool throws {
            //writeln("-----------------nodesLabelCompatible called-------------------\n");

            var label1 = PropGraphNodeLabelMapper(nodeLabels_GraphG1, n1, Orig_Label_Mapper_G_to_Pass)[1];
            var label2 = PropGraphNodeLabelMapper(nodeLabels_GraphG2, n2, Orig_Label_Mapper_H_to_Pass)[1];

            if label1 != label2 {
                return false;
            }

            return true;

        }// end of nodesLabelCompatible

        // Check if candidates' pairs are feasible
        proc isFeasible(state: State, n1: int, n2: int) throws {
            //writeln("-----------------isFeasible called for (",n1,",", n2,")-------------------");
//////////////////////// new version added Dec 13
            var termout1, termout2, termin1, termin2, new1, new2 : int =0 ;

            if !nodesLabelCompatible(n1, n2) {
                //writeln("Node labels are Inconsistent");
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
                    var (flag1, label1) = PropGraphRelationshipMapper(segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, n1, Out1, Orig_Relationships_Mapper_G_to_Pass);
                    var (flag2, label2) = PropGraphRelationshipMapper(segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, n2, Out2, Orig_Relationships_Mapper_H_to_Pass);
            
                    if !flag1 || (label2 != label1) {
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
                    var (flag1, label1) = PropGraphRelationshipMapper(segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, In1, n1, Orig_Relationships_Mapper_G_to_Pass);
                    var (flag2, label2) = PropGraphRelationshipMapper(segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, In2, n2, Orig_Relationships_Mapper_H_to_Pass);
            
                    if !flag1 || label2 != label1 {
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
            
            return termin2<=termin1 && termout2<=termout1 && (termin2+termout2+new2)<=(termin1+termout1+new1);
        }// end of isFeasible

        // DFS like to traverse graph and returns list of all solution states 
        proc dfs(ref initialState: State, g1: SegGraph, g2: SegGraph): list (set((int, int))) throws {
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
            // why I did it?
            for solSet in solutions {
                for (n1, n2) in solSet {
                    subIsoArrToReturn[posOffset + n2] = n1;
                }
                posOffset += g2.n_vertices;
            }

            return(subIsoArrToReturn);
        } //end of VF2
        
        return(IsoArr);

    } //end of runVF2

} // end of module