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

        // Extract the g2/H information from PropGraph DS
        var srcNodesG2 = toSymEntry(g2.getComp("SRC"), int).a;
        var dstNodesG2 = toSymEntry(g2.getComp("DST"), int).a;
        var segGraphG2 = toSymEntry(g2.getComp("SEGMENTS"), int).a;
        var edgeRelationshipsGraphG2 = toSymEntry(g2.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var nodeLabels_GraphG2 = toSymEntry(g2.getComp("VERTEX_LABELS"), domain(int)).a;
        
        var TimerArrNew:[0..17] real(64) = 0.0;
        var effectiveArr:[0..7] int = 0;
        var timerpreproc:stopwatch;
        timerpreproc.start();


        // Predecessor computation
        var PredecessorsG1: [0..#g1.n_vertices] list(int);
        var PredecessorsG2: [0..#g2.n_vertices] list(int);

        var timerpredG1:stopwatch;
        timerpredG1.start();

        forall i in 0..g1.n_vertices-1 with (ref PredecessorsG1) {
            PredecessorsG1[i] = getInNeighbors(g1.n_vertices, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, i, Orig_Relationships_Mapper_G_to_Pass);
            //PredecessorsG1[i] = getPredecessors(g1.n_vertices, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, i, Orig_Relationships_Mapper_G_to_Pass);
        }
        timerpredG1.stop();
        TimerArrNew[14] += timerpredG1.elapsed();

        var timerpredG2:stopwatch;
        timerpredG2.start();

        forall i in 0..g2.n_vertices-1 with(ref PredecessorsG2) {
            PredecessorsG2[i] = getInNeighbors(g2.n_vertices, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, i, Orig_Relationships_Mapper_H_to_Pass);
            //PredecessorsG2[i] = getPredecessors(g2.n_vertices, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, i, Orig_Relationships_Mapper_H_to_Pass);
        }
        timerpredG2.stop();
        TimerArrNew[15] += timerpredG2.elapsed();

        // Successors computation
        var SuccessorsG1: [0..#g1.n_vertices] list(int);
        var SuccessorsG2: [0..#g2.n_vertices] list(int);

        var timersuccG1:stopwatch;
        timersuccG1.start();
        forall i in 0..g1.n_vertices-1 with(ref SuccessorsG1) {
            SuccessorsG1[i].pushBack(getOutNeighbors(segGraphG1, i, dstNodesG1));
            //SuccessorsG1[i] = getSuccessors(segGraphG1, i, dstNodesG1);
        }
        timersuccG1.stop();
        TimerArrNew[16] += timersuccG1.elapsed();

        var timersuccG2:stopwatch;
        timersuccG2.start();
        forall i in 0..g2.n_vertices-1 with(ref SuccessorsG2){
            SuccessorsG2[i].pushBack(getOutNeighbors(segGraphG2, i, dstNodesG2));
            //SuccessorsG2[i] = getSuccessors(segGraphG2, i, dstNodesG2);
        }
        timersuccG2.stop();
        TimerArrNew[17] += timersuccG2.elapsed();
        
        timerpreproc.stop();
        TimerArrNew[0] += timerpreproc.elapsed();

        
        //var IsoArr:[0..1] int;
        
        var timerVF2:stopwatch;
        timerVF2.start();
        
        var IsoArrtemp = vf2(g1, g2);
        
        timerVF2.stop();
        TimerArrNew[1] += timerVF2.elapsed();
        
        

        var IsoArr = nodeMap_GraphG1[IsoArrtemp];        
        writeln("inside VF2 IsoArr     = ", IsoArr);

        proc PropGraphRelationshipMapper(segGraph, dstNodes, edgeRelationshipsGraph, 
                                        fromNode: int, toNode: int, Mapper): (bool, string) throws {
            //writeln("-----------------PropGraphRelationshipMapper called-------------------\n");
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

            //var D1 = {0..<n1};
            //var D2 = {0..<n2};

            // Core vectors
            //var core1: [D1] int = -1;
            //var core2: [D2] int = -1;
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

                //this.D1 = {0..<this.n1};
                //this.D2 = {0..<this.n2};
            
                //this.core1 = -1;
                //this.core2 = -1;
            
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
            // Initialize based on graph sizes
            proc init(n1, n2) {
                this.n1 = n1;
                this.n2 = n2;

                //this.D1 = {0..<this.n1};
                //this.D2 = {0..<this.n2};

                //this.core1 = -1;
                //this.core2 = -1;

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

                //core1 = -1; // reset to -1
                //core2 = -1;
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
                //core1[x1] = x2;
                //core2[x2] = x1;
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
                if node >= 0 && node < n1 {
                    // Node is from g1, check core1
                    //if core1(node) != -1 {
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

                    // Node is from g1, check core1
                    //if core2(node) != -1 {
                    if core2.contains(node) {
                        return true;
                    }
                }
                // Node outside bounds, return false
                return false;
            }

        } // end of State record

        // Get nodes that point to node 
        proc getInNeighbors(n_vertices: int, segGraph, dstNodes, edgeRelationshipsGraph , node: int, Mapper) throws {
            //writeln("-----------------getInNeighbors called-------------------");
            //writeln("-----------------for ",node, "-------------------");
            var inNeighbors: list(int, parSafe = true);

            // Loop through all nodes
            forall i in 0..n_vertices-1 with(ref inNeighbors){

                // Check if i points to node
                if PropGraphRelationshipMapper(segGraph, dstNodes, edgeRelationshipsGraph, 
                                    i, node, Mapper)[0]{
        
                    // Node i points to node, so it is an in-neighbor  
                    inNeighbors.pushBack(i);

                }

            }
            //writeln("-----------------inNeighbors = ",inNeighbors, "-------------------");
            return inNeighbors;        
        }  //end of getInNeighbors

        // Get nodes pointed to from 'node'
        proc getOutNeighbors(segGraph, node: int, dstNodes) throws {
            //writeln("-----------------getOutNeighbors called-------------------");
            //writeln("-----------------for ",node, "-------------------\n");
            
            var adj_list_of_node_start = segGraph[node];
            var adj_list_of_node_end = segGraph[node+1]-1;
            
            var outNeighbors = dstNodes[adj_list_of_node_start..adj_list_of_node_end];
            //writeln("-----------------getOutNeighbors  = ",outNeighbors);

            return outNeighbors;
       
        }// end of getOutNeighbors


        proc addToTinTout(ref state: State, u : int, v: int): State throws {
            //writeln("-----------------addToTinTout called-------------------");
            //writeln("-----------------for", u, ", ", v, "-------------------\n");

            // Get in and out neighbors
            var inNeighbors = PredecessorsG1[u]; //getInNeighbors(g1.n_vertices, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, u, Orig_Relationships_Mapper_G_to_Pass);
            //writeln("inNeighbors g1 (",u,")= ", inNeighbors);

            var outNeighbors = SuccessorsG1[u]; //getOutNeighbors(segGraphG1, u, dstNodesG1);
            //writeln("outNeighbors g1 (", u,")= ", outNeighbors);

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
            var inNeighborsg2 = PredecessorsG2[v]; //getInNeighbors(g2.n_vertices, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, v, Orig_Relationships_Mapper_H_to_Pass);
            var outNeighborsg2 = SuccessorsG2[v]; //getOutNeighbors(segGraphG2, v, dstNodesG2);
            //writeln("inNeighbors g2 (",v,")= ", inNeighbors);
            //writeln("outNeighbors g2 (", v,")= ", outNeighbors);
            
            if state.Tin2.contains(v) {
                state.Tin2.remove(v); 
            }
            if state.Tout2.contains(v) {
                state.Tout2.remove(v);
            }
            // Add unmapped neighbors to Tin
            //writeln("g2 , inNeighbors begin");
            forall n2 in inNeighborsg2 with(ref state){
                //if state.core2[n2] == -1 {
                if !state.core2.contains(n2) {
                    
                    state.Tin2.add(n2);
                }
            }
            //writeln("g2 , outNeighbors begin");

            // Add unmapped neighbors to Tout
            forall n2 in outNeighborsg2 with(ref state){
                //if state.core2[n2] == -1 {
                if !state.core2.contains(n2) {
                    state.Tout2.add(n2);
                }
            }

            //writeln(" state afte tin tout = ", state); 
            return state;
            
        } // end of addToTinTout

        // Create initial state with empty mappings, vectors, etc
        proc createInitialState(): State throws {
            writeln("-----------------createInitialState called-------------------\n");

            var state = new State();

            state.init(g1.n_vertices, g2.n_vertices);

            //state.core1 = -1; 
            //state.core2 = -1;
            //state.core1.clear(); 
            //state.core2.clear();

            //state.depth = 0;
            return state;

        }  //end of createInitialState
/*
        // Check if state is a valid solution 
        proc isSolution(state: State): bool throws {
            //writeln("-----------------isSolution called-------------------\n");
          
            // Check each mapped node
            for (n1, n2) in state.mapping {
                // Check degree equivalency 
                if graphDegree[n1] < SubgraphDegree[n2] {
                    writeln("Degree mismatch!");
                    return false;
                }
            }

            writeln("Degrees match across mapping"); 
            
            return true;
        } // end of isSolution
*/
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
        
        // Why chapel array has no contains()/Find()?!
        proc arrFindKey(passedarr, key:int) throws {
            //writeln("-----------------arrFindKey called-------------------\n");

            var flag: bool = false;
            
            forall elm in passedarr with(ref flag) {
                if elm == key then flag = true;
            }
            return flag;
        } // end of arrFindKey

        // Create candidates based on current state and retuns a list of pairs
        // based on old paper!!
        proc getCandidatePairsOpti(state:State) throws {
            //writeln("-----------------getCandidatePairsOpti called-------------------\n");

            var candidates = new set((int, int), parSafe = true);
            
            var unmapped2 = getUnmappedNodesg2(g2, state);

            // If Tout1 and Tout2 are both nonempty.
            if state.Tout1.size > 0 && state.Tout2.size > 0 {
                
                var minTout2 = min reduce state.Tout2;
                //forall n1 in state.Tout1 with (ref candidates){
                forall n1 in state.Tout1 with (ref candidates){
                    //writeln("HERE 1");
                    candidates.add((n1, minTout2)); 
                }
                
            } 
                else {
                    //If Tin1 and Tin2 are both nonempty. 
                    if state.Tin1.size > 0 && state.Tin2.size > 0{
                        var minTin2 = min reduce state.Tin2;
                        //forall n1 in state.Tin1 with (ref candidates) {
                        forall n1 in state.Tin1 with (ref candidates){
                            //writeln("HERE 2");
                            candidates.add((n1, minTin2)); 
                        }
                    } else { //not (Tin1 or Tin2)
                                if unmapped2.size >0 {
                                    var minUnmapped2 = min reduce unmapped2;
                                    //forall n1 in unmapped1 with (ref candidates){
                                    //for n1 in unmapped1 {
                                    forall n1 in 0..#g1.n_vertices with (ref candidates) {
                                        if !state.core1.contains(n1){
                                            //writeln("HERE 3");
                                            candidates.add((n1, minUnmapped2));
                                        }    
                                    }
                                }    
                            } 
                }   
            //if candidates.size == 0 then writeln("We made a huge mistake");
            return candidates;

        } // end of getCandidatePairsOPti
/*
        // Get predecessors of a node from Graph
        proc getPredecessors(n_vertices: int, segGraph, dstNodes, edgeRelationshipsGraph, node: int, Mapper) throws {
            //writeln("-----------------getPredecessors called-------------------\n");
            //writeln("-----------------for ",node,"\n");

            var preds: list(int, parSafe = true);
            var visited = new set(int); 
            var stack: list(int, parSafe = true);
            //writeln("at the begining visited = ", visited);
            //writeln("at the begining preds = ", preds);
            //writeln("at the begining stack = ", stack);

            stack.pushBack(node);  
            //writeln("after pushBack stack = ", stack);
            while (stack.size > 0) {

                var curr = stack.popBack();
                //writeln("after popBack stack = ", stack);
                //writeln("curr = ", curr);

                if !visited.contains(curr) {
            
                    visited.add(curr);
                    //writeln("after add visited = ", visited);
                    //writeln("getInNeighbors(", curr,") = ", getInNeighbors(graph, curr, Mapper));

                    // Check nodes pointing to curr
                    for nbr in getInNeighbors(n_vertices, segGraph, dstNodes, edgeRelationshipsGraph , curr, Mapper){
                        if !preds.contains(nbr) then preds.pushBack(nbr);
                        //writeln("after pushBack preds = ", preds);
                        // Traverse
                        stack.pushBack(nbr); 
                        //writeln("after pushBack stack = ", stack);
                    }
                }
            }
            //writeln("getPredecessors retrun preds = ", preds);

            return preds;
        } // end of getPredecessors
*/
/*
        // Get successors of a node
        // by using a graph traversal BFS approach
        //  * Uses distributed queue for scalable BFS. Beaware it is NOT standard package!!!
        proc getSuccessors(segGraph, node: int, dstNodes) throws {
            //writeln("-----------------getSuccessors called-------------------\n");

            var visited = new set(int);
            var succs: list(int, parSafe = true); 
            
            // Distributed deque for queue  
            var queue = new DistDeque(int);

            queue.enqueue(node);

            
            while queue.size > 0 {

                // Get next node to visit
                var (foundElem, curr) = queue.dequeue();
                // Check if visited
                if visited.contains(curr) {
                    continue;
                }
                
                // Add to visited      
                visited.add(curr);

                // Find outgoing edges 
                for nbr in getOutNeighbors(segGraph, curr, dstNodes)  {

                    // Add as a successor  
                    //succs.pushBack(nbr);
                    if !succs.contains(nbr) then succs.pushBack(nbr);
                    // Enqueue next nodes  
                    queue.enqueue(nbr);    
                }

            }
            //writeln("getSuccessors retrun succs = ", succs);
    
            return succs;
        } // end of getSuccessors
*/
/*
        // Get 2-hop neighbors
        proc get2HopNeighbors(n_vertices: int, node: int, segGraph, dstNodes, edgeRelationshipsGraph, Mapper, predsFlag: bool) throws{
            //writeln("-----------------get2HopNeighbors called-------------------\n");
            //writeln("-----------------for graph, node = ",node,"preds = ", preds," -------------------\n");

            // 1-hop neighbors
            var oneHop = if predsFlag then getPredecessors(n_vertices, segGraph, dstNodes, edgeRelationshipsGraph, node, Mapper) 
                        else getSuccessors(segGraph, node, dstNodes);
            //writeln("oneHop = ", oneHop, " oneHop.type =",(oneHop.type):string);
            // 2-hop neighbors  

            var twoHop: list(int);
            //writeln("twoHop = ", twoHop, " twoHop.type =",(twoHop.type):string);

            for n in oneHop {
                var more = if predsFlag then getPredecessors(n_vertices, segGraph, dstNodes, edgeRelationshipsGraph, node, Mapper)
                        else getSuccessors(segGraph, node, dstNodes);
                
                for m in more {
                    twoHop.pushBack(m);  
                }              
            }
            
            // Filter out dups
            twoHop = twoHop.uniq();

            // Remove 1-hop  
            twoHop = twoHop.except(oneHop);

            
            //writeln("twoHop = ", twoHop);
            for n in oneHop {
                twoHop.remove(n);
            }
                //writeln("twoHop - oneHop = ", twoHop);// Exclude 1-hop neighbors

            return twoHop.toArray();
        } // end of get2HopNeighbors
*/
/*
        // Checks that the proposed mapping of node n2 satisfies 
        // the ordering constraint relative to already mapped nodes.
        // Added to avoid multiple travel to a specific branch
        proc RmappingInOrder(state: State, n1: int, n2: int): bool {
            writeln("-----------------RmappingInOrder called-------------------\n");

            var mapped = state.core1;
            //writeln("state.core2 = ", state.core1);
            //writeln("mapped = ", mapped);
            if (mapped.size > 0) {

                var maxMapped = max reduce(mapped);
                //writeln("maxMapped = ", maxMapped);
                if (n2 <= maxMapped) {
                writeln("Violates ordering");
                return false;
                }
            
            }

            return true;

        } // end of RmappingInOrder
*/
        // Rpred This checks:
        // All mapped predecessors n' of n should have a mapped predecessor m' of m.
        // All mapped predecessors m' of m should have a mapped predecessor n' of n.
        // So it verifies this mapping consistency in both directions between the predecessor sets.
        proc Rpred(state: State, n1: int, n2: int): bool throws {
            //writeln("-----------------Rpred called-------------------\n");
            // Get predecessors
            var nPreds = PredecessorsG1[n1]; //getPredecessors(g1.n_vertices, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, n1, Orig_Relationships_Mapper_G_to_Pass);
            var mPreds = PredecessorsG2[n2]; //getPredecessors(g2.n_vertices, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, n2, Orig_Relationships_Mapper_H_to_Pass);

            writeln("nPreds = ", nPreds);
            writeln("mPreds = ", mPreds);
            var flag: bool = true;

            // Check each direction
            // 1. G1 -> G2
            for nprime in nPreds {
                writeln("nprime = ", nprime);
                if state.isMappedn1(nprime) {
                    writeln(nprime, " is mapped");
                    var mprime = state.core1[nprime];
                    writeln("mprime = ", mprime);
                    //if !arrFindKey(mPreds, mprime) {
                    if mPreds.find(mprime)!= -1 {    
                        writeln(mprime," is not in mpreds ");
                        flag = false;
                    }
                }
            }
            // 2. G2 -> G1
            for mprime in mPreds {
                writeln("mprime = ", mprime);
                if state.isMappedn2(mprime) {
                    writeln(mprime, " is mapped");
                    var nprime = state.core2[mprime];
                    writeln("nprime = ", nprime);
                    //if !arrFindKey(nPreds, nprime) { 
                    if nPreds.find(nprime)!= -1{    
                        writeln(nprime," is not in nPreds ");
                        flag = false;
                    }
                }
            }

            //writeln("-----------------Rpred returned ",flag, "-------------------\n");
            return flag;

/*
                if state.isMappedn2(p) {
                    var m = state.core2[p];
                    writeln(p ," is mapped and ",m," = state.core2[p]" );
                    if !arrFindKey(n1Preds, m) {
                        flag = false;
                        writeln("flag = false for ", m, "is not in", n1Preds);
                    } else if getEdgeCount(segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, m, n1, Orig_Relationships_Mapper_G_to_Pass) 
                            < getEdgeCount(segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, p, n2, Orig_Relationships_Mapper_H_to_Pass) {
                            //if getEdgeCount(g1, m, n1) != getEdgeCount(g2, p, n2) {
                            writeln("getEdgeCountG1_m_n1 != getEdgeCountG2_p_n2 ");    
                            flag = false;
                        } 

                }

            }
            writeln("-----------------Rpred returned ",flag, "-------------------\n");
            return flag;
*/
        }// end of Rpred
/*
        proc getEdgeCount(segGraph, dstNodes, edgeRelationshipsGraph, 
                                    n1, n2, Mapper): int throws {
            //writeln("-----------------getEdgeCount called-------------------\n");

            var count = 0;
            // Check if n1 points to node n2
            if PropGraphRelationshipMapper(segGraph, dstNodes, edgeRelationshipsGraph, 
                                    n1, n2, Mapper)[0]{
                                        count += 1;
            }  

            // Also check if n2 is pointed to n1
            if PropGraphRelationshipMapper(segGraph, dstNodes, edgeRelationshipsGraph, 
                                    n2, n1, Mapper)[0]{
                                        count += 1;
            }  
            
            return count;

        }
*/
        // Rsucc It checks:
        // All mapped successors n' of n should have a mapped successor m' of m.
        // All mapped successors m' of m should have mapped successor n' of n.

        proc Rsucc(state: State, n1: int, n2: int): bool throws {
            //writeln("-----------------Rsucc called-------------------\n");

            var n1Succs = SuccessorsG1[n1]; //getSuccessors(segGraphG1, n1, dstNodesG1);
            var n2Succs = SuccessorsG2[n2]; //getSuccessors(segGraphG2, n2, dstNodesG2);
            //writeln("n1Succs = ", n1Succs);
            //writeln("n2Succs = ", n2Succs);

            var flag: bool = true;

            // Check each direction  
 
            var n1Mapped = 0;
            for s in n1Succs {
                if state.isMappedn1(s) {
                    n1Mapped += 1;
                }
            }
            //writeln("n1Mapped = ", n1Mapped);

            var n2Mapped = 0;
            for s in n2Succs {
                if state.isMappedn2(s) {
                    n2Mapped += 1;
                }
            }
            //writeln("n2Mapped = ", n2Mapped);

            if n1Mapped < n2Mapped {
                return false;
            }

            return true;

        } // end of Rsucc
/*            for s in n2Succs {
                if state.isMappedn2(s) {

                    var m = state.core2[s];
                    writeln(s ," is mapped and ",m," = state.core2[p]" );

                        if !arrFindKey(n1Succs, m) {
                            flag = false;
                            writeln("flag = false for ", m, "is not in", n1Succs);

                        } else if getEdgeCount(segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, n1, m, Orig_Relationships_Mapper_G_to_Pass)
                             < getEdgeCount(segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, n2, s, Orig_Relationships_Mapper_H_to_Pass) {
                                writeln("getEdgeCountG1_m_n1 != getEdgeCountG2_p_n2 ");
                                writeln();    
                                flag = false;
                            }
                }
            }
            
            return flag;
            //return true;
        } // end of Rsucc
*/
        // Rin checks that the number of unmapped in-neighbors of n1 (node from graph 1) 
        // is greater than or equal to the number of unmapped in-neighbors of n2 (node from graph 2).
        proc Rin(state: State, n1: int, n2: int): bool throws {
            //writeln("-----------------Rin called-------------------\n");
            var n1PredUnmapped, n2PredUnmapped = 0;

            var n1Pred = PredecessorsG1[n1]; //getPredecessors(g1.n_vertices, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, n1, Orig_Relationships_Mapper_G_to_Pass);
            var n2Pred = PredecessorsG2[n2]; //getPredecessors(g2.n_vertices, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, n2, Orig_Relationships_Mapper_H_to_Pass);

            //writeln("n1Pred = ", n1Pred);
            //writeln("n2Pred = ", n2Pred);

            // Filter unmapped nodes
            for p in n1Pred {
                if !state.isMappedn1(p) {
                    n1PredUnmapped += 1; 
                }
            }

            for p in n2Pred {
                if !state.isMappedn2(p) {
                    n2PredUnmapped += 1;
                }
            }
            // Check unmapped predecessor counts
            if n1PredUnmapped < n2PredUnmapped {
                return false;
            }

            var n1SuccUnmapped, n2SuccUnmapped = 0;

            var n1Succ = SuccessorsG1[n1]; //getSuccessors(segGraphG1, n1, dstNodesG1);
            var n2Succ = SuccessorsG2[n2]; //getSuccessors(segGraphG2, n2, dstNodesG2);

            //writeln("n1Succ = ", n1Succ);
            //writeln("n2Succ = ", n2Succ);
            
            // Filter unmapped nodes
            for s in n1Succ {
                if !state.isMappedn1(s) {
                    n1SuccUnmapped += 1;
                }
            }
            
            for s in n2Succ  {
                if !state.isMappedn2(s) {
                    n2SuccUnmapped += 1;
                }
            }

            // Check successor counts 
            if n1SuccUnmapped < n2SuccUnmapped {
                return false;
            }

            return true;
        }  // end of Rin

        // Rout checks that the number of unmapped out-neighbors of n1 (node from graph 1) 
        // is greater than or equal to the number of unmapped out-neighbors of n2 (node from graph 2)
        proc Rout(state: State, n1: int, n2: int): bool throws{
            //writeln("-----------------Rout called-------------------\n");

            var n1PredUnmapped = 0;

            var n1Pred = PredecessorsG1[n1]; //getPredecessors(g1.n_vertices, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, n1, Orig_Relationships_Mapper_G_to_Pass);
            var n2Pred = PredecessorsG2[n2]; //getPredecessors(g2.n_vertices, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, n2, Orig_Relationships_Mapper_H_to_Pass);

            var getOutN1 = SuccessorsG1[n1]; //getOutNeighbors(segGraphG1, n1, dstNodesG1);
            var getOutN2 = SuccessorsG2[n2]; //getOutNeighbors(segGraphG2, n2, dstNodesG2);
         
            for p in n1Pred {
                if !state.isMappedn1(p) && getOutN1.find(p)!= -1{  
                   // if arrFindKey(getOutN1, p) {
                        n1PredUnmapped += 1;
                   // } 
                }
            }

            var n2PredUnmapped = 0;

            for p in n2Pred {
                if !state.isMappedn2(p) && getOutN2.find(p) != -1 {
                   // if arrFindKey(getOutN2, p) {
                        n2PredUnmapped += 1;  
                   // }
                }
            }

            if n1PredUnmapped < n2PredUnmapped {
                return false;
            }

            return true;
        } // end of Rout
        
        // Rnew performs a 2-level lookahead in the search space 
        // to prune states that will have no valid successors after 
        // 2 steps.
/*        proc Rnew(state: State, n1: int, n2: int): bool throws {
            writeln("-----------------Rnew called-------------------\n");
            // Get 2-hop neighbors
            var n1Pred2 = get2HopNeighbors(g1.n_vertices, n1, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, Orig_Label_Mapper_G_to_Pass, true); 
            var n2Pred2 = get2HopNeighbors(g2.n_vertices, n2, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, Orig_Label_Mapper_H_to_Pass, true);

            var n1Succ2 = get2HopNeighbors(g1.n_vertices, n1, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, Orig_Label_Mapper_G_to_Pass, false);
            var n2Succ2 = get2HopNeighbors(g2.n_vertices, n2, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, Orig_Label_Mapper_H_to_Pass, false);

            // Filter already mapped nodes
            var n1PredUnmapped, n2PredUnmapped, 
                n1SuccUnmapped, n2SuccUnmapped: domain(int);

            for n in n1Pred2 {
                if !state.isMappedn1(n) {
                n1PredUnmapped += n; 
                }
            }

            for n in n2Pred2 {
                if !state.isMappedn2(n) {
                n2PredUnmapped += n;
                }  
            }

            for n in n1Succ2 {
                if !state.isMappedn1(n) {
                n1SuccUnmapped += n;
                }
            }

            for n in n2Succ2 {
                if !state.isMappedn2(n) {
                n2SuccUnmapped += n;
                }
            }

            // Check sizes
            if n1PredUnmapped.size < n2PredUnmapped.size {
                return false; 
            }

            if n1SuccUnmapped.size < n2SuccUnmapped.size {
                return false;
            }

            return true;

        } // end of Rnew
*/
        // Rnew performs a 2-level lookahead in the search space 
        // to prune states that will have no valid successors after 
        // 2 steps.
        // after reading again and again I changed my mind. I think this
        // new function is more effective than get2HopNeighbors stuff
        proc Rnew(state: State, n1: int, n2: int): bool throws {
            //writeln("-----------------Rnew called-------------------\n");
            var n1NotIn, n2NotIn = 0;
            var n1Pred = PredecessorsG1[n1]; //getPredecessors(g1.n_vertices, segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, n1, Orig_Relationships_Mapper_G_to_Pass);
            var n2Pred = PredecessorsG2[n2];//getInNeighbors(g2.n_vertices, segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, n2, Orig_Relationships_Mapper_H_to_Pass);

            for p in n1Pred {
                if !state.isMappedn1(p) && !state.Tin1.contains(p) && !state.Tout1.contains(p) {
                    n1NotIn += 1; 
                }
            }
            
            for p in n2Pred {
                if !state.isMappedn2(p) && !state.Tin2.contains(p) && !state.Tout2.contains(p) {
                    n2NotIn += 1; 
                }
            }
            if n1NotIn < n2NotIn {
                writeln("Rnew first condition returned false for ",n1,", ", n2);
                writeln("state = ", state);
                return false;
            }


            var n1NotOut, n2NotOut = 0;
            var n1Succ = getOutNeighbors(segGraphG1, n1, dstNodesG1);
            var n2Succ = getOutNeighbors(segGraphG2, n2, dstNodesG2);

            for s in n1Succ {
                if !state.isMappedn1(s) && !state.Tin1.contains(s) && !state.Tout1.contains(s) {
                    n1NotOut += 1; 
                }
            }            
            
            for s in n2Succ {
                if !state.isMappedn2(s) && !state.Tin2.contains(s) && !state.Tout2.contains(s) {
                    n2NotOut += 1; 
                }
            }
            
            if n1NotOut < n2NotOut {
                writeln("Rnew second condition returned false for ",n1,", ", n2);
                writeln("state = ", state);
                return false;
            }

            return true;

        } // end of Rnew

        // Check node labels are the same
        proc nodesLabelCompatible(n1: int, n2: int): bool throws {
            //writeln("-----------------nodesLabelCompatible called-------------------\n");

            var label1 = PropGraphNodeLabelMapper(nodeLabels_GraphG1, n1, Orig_Label_Mapper_G_to_Pass)[1];
            var label2 = PropGraphNodeLabelMapper(nodeLabels_GraphG2, n2, Orig_Label_Mapper_H_to_Pass)[1];

            if label1 != label2 {
                return false;
            }

            return true;

        }

        //Edge label checking:
        proc edgesLabelCompatible(n1, n2, x1, x2): bool throws{
            //writeln("-----------------edgesLabelCompatible called-------------------\n");
            
            var (flag1, label1) = PropGraphRelationshipMapper(segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, n1, x1, Orig_Relationships_Mapper_G_to_Pass);
            var (flagrev1, labelrev1) = PropGraphRelationshipMapper(segGraphG1, dstNodesG1, edgeRelationshipsGraphG1, x1, n1, Orig_Relationships_Mapper_G_to_Pass);

            var (flag2, label2) = PropGraphRelationshipMapper(segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, n2, x2, Orig_Relationships_Mapper_H_to_Pass);
            var (flagrev2, labelrev2) = PropGraphRelationshipMapper(segGraphG2, dstNodesG2, edgeRelationshipsGraphG2, x2, n2, Orig_Relationships_Mapper_H_to_Pass);
            
            if flag2 && !flag1 {
                return false;

            } else if flag2 && flag1 {
                if label1 == label2 {
                    return true;
                } else {
                    return false;
                }

            } 

            if flagrev2 && !flagrev1 {
                return false;

            } else if flagrev2 && flagrev1 {
                if labelrev1 == labelrev2 {
                    return true;
                } else {
                    return false;
                }

            } 
                       
            return true;  
        }

        proc RpredRsuccRsemanticFeasible(state, n1, n2) throws{
            //writeln("-----------------RsemanticFeasible called-------------------\n");
            //writeln("-----------------for n1 = ",n1," n2 = ",n2," -------------------\n");
            var flag: bool = true;
            if !nodesLabelCompatible(n1, n2) {
                //writeln("Node labels are Inconsistent");
                return false;
            }
            
            // Check edge compatibility
            //forall (x1, x2) in state.mapping with(ref flag){
            for (x1, x2) in state.mapping {
                if !edgesLabelCompatible(n1, n2, x1, x2) {
                    //writeln("Edge labels are Inconsistent", x1, x2);
                flag = false;
                }
            }

            return flag;

        }

        // Check if candidates' pairs are feasible
        proc isFeasible(state: State, n1: int, n2: int) throws {
            //writeln("-----------------isFeasible called for (",n1,",", n2,")-------------------");
//////////////////////// new version Dec 13
            var termout1, termout2, termin1, termin2, new1, new2 : int =0 ;

            if !nodesLabelCompatible(n1, n2) {
                //writeln("Node labels are Inconsistent");
                return false;
            }

            var getOutN1 = SuccessorsG1[n1]; //getOutNeighbors(segGraphG1, n1, dstNodesG1);
            var getOutN2 = SuccessorsG2[n2]; //getOutNeighbors(segGraphG2, n2, dstNodesG2);
         
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
            var getInN1 = PredecessorsG1[n1]; 
            var getInN2 = PredecessorsG2[n2];
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
        }

/*            
            var timerisFeasible:stopwatch;
            timerisFeasible.start();

            //if !RmappingInOrder(state, n1, n2) {
                //writeln("Feasibility returned FALSE because of RmappingInOrder");
                //return false;
            //} 
            var timerRpredRsuccRsemantic:stopwatch;
            timerRpredRsuccRsemantic.start();
            
            if !RpredRsuccRsemanticFeasible(state, n1, n2) {
                //writeln("Feasibility returned False for",n1,", ",n2," RsemanticFeasible");
                effectiveArr[0] += 1;
                return false;
            } 
            timerRpredRsuccRsemantic.stop();
            //outMsg = "RsemanticFeasible output took " + timerRsemanticFeasible.elapsed():string + " sec";
            //writeln(outMsg);
            TimerArrNew[5] += timerRpredRsuccRsemantic.elapsed();

            var timerRin:stopwatch;
            timerRin.start();
            
            if !Rin(state, n1, n2) {
                //writeln("Feasibility returned False for",n1,", ",n2," Rin");
                effectiveArr[1] += 1;
                return false;
            }
            timerRin.stop();
            //outMsg = "Rin output took " + timerRin.elapsed():string + " sec";
            //writeln(outMsg);
            TimerArrNew[6] += timerRin.elapsed();

            var timerRout:stopwatch;
            timerRout.start();
            
            if !Rout(state, n1, n2) {
                //writeln("Feasibility returned False for",n1,", ",n2," Rout");
                effectiveArr[2] += 1;
                return false;
            }  
            timerRout.stop();
            //outMsg = "Rout output took " + timerRout.elapsed():string + " sec";
            //writeln(outMsg);
            TimerArrNew[7] += timerRout.elapsed();

            var timerRnew:stopwatch;
            timerRnew.start();
            
            if !Rnew(state, n1 ,n2) {
                //writeln("Feasibility returned False for",n1,", ",n2," Rnew");
                effectiveArr[3] += 1;
                return false;
            } 
            timerRnew.stop();
            //outMsg = "Rnew output took " + timerRnew.elapsed():string + " sec";
            //writeln(outMsg);
            TimerArrNew[8] += timerRnew.elapsed();



            //writeln("-----------------isFeasible PASSED ALL CHECKS-------------------");
            timerisFeasible.stop();
            TimerArrNew[3] += timerisFeasible.elapsed();
            effectiveArr[4] += 1;

            return true;// passed all checks
        }
*/
        // DFS like to traverse graph and returns list of all solution states 
        proc dfs(ref initialState: State, g1: SegGraph, g2: SegGraph): list (set((int, int))) throws {
            //writeln("-----------------dfs called-------------------\n");

            //var allSolutions: list(State);
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
                var timercandidatesOpti:stopwatch;
                timercandidatesOpti.start();

                var candidatesOpti = getCandidatePairsOpti(state);
                
                timercandidatesOpti.stop();
                TimerArrNew[4] += timercandidatesOpti.elapsed();

                //var counter: int = 0;
                forall (n1, n2) in candidatesOpti with(ref stack) {
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
            //time

            var timerDFS:stopwatch;
            timerDFS.start();

            var solutions = dfs(initial, g1, g2);
            
            timerDFS.stop();
            TimerArrNew[2] += timerDFS.elapsed();

            var subIsoArrToReturn: [0..(solutions.size*g2.n_vertices)-1](int);

            var posOffset = 0;

            for solSet in solutions {
                for (n1, n2) in solSet {
                    subIsoArrToReturn[posOffset + n2] = n1;
                }
                posOffset += g2.n_vertices;
            }


            return(subIsoArrToReturn);
        } //end of VF2
        

        for i in 0..17 {
            if i == 0 {
                writeln("**********************Preprocessing *********************");
                writeln("Preprocessing total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[i]);
            }               
            if i == 14 {
                writeln("PredecessorsG1 total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[i]);
            }            
            if i == 15 {
                writeln("PredecessorsG2 total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[i]);
            }            
            if i == 16 {
                writeln("SuccessorsG1 total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[i]);
            }            
            if i == 17 {
                writeln("SuccessorsG2 total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[i]);
            }

            if i == 1 {
                writeln("\nVF2 total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[i]);
            }              
            
            if i == 2 {
                writeln("DFS total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[i]);
            }            
            if i == 3 {
                writeln("\nisFeasible total time = ", TimerArrNew[i]);
                writeln("isFeasible usage = ", effectiveArr[4]);
            }              
            if i == 4 {
                writeln("\nCandidateOpti total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[i]);
            }             
            if i == 5 {
                writeln("\nRpredRsuccRsemantic total time = ", TimerArrNew[5]);
                writeln("# usage = ", effectiveArr[0]);
            }              
            if i == 6 {
                writeln("\nRin total time = ", TimerArrNew[6]);
                writeln("# usage = ", effectiveArr[1]);
            }              
            if i == 7 {
                writeln("\nRout total time = ", TimerArrNew[7]);
                writeln("# usage = ", effectiveArr[2]);
            }            
            if i == 8 {
                writeln("\nRnew total time = ", TimerArrNew[8]);
                writeln("# usage = ", effectiveArr[3]);
            }              
            if i == 11 {
                writeln("\ngetunmapped1 total time = ", TimerArrNew[i]);
                writeln("# usage = ", effectiveArr[6]);
            }              
            if i == 12 {
                writeln("\ngetunmapped2 total time = ", TimerArrNew[i]);
                writeln("# usage = ", effectiveArr[7]);
            }  
            if i == 13 {
                writeln("candidate creation total time = ", TimerArrNew[i]);
                //writeln("Rpred usage = ", effectiveArr[3]);
            }  
            
        }

        return(IsoArr);

    } //end of runVF2
} // end of module