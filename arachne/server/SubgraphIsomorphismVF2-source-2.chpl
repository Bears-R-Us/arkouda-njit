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
    //Global mappers
    var Orig_Label_Mapper_G_Passed: list(string);
    var Orig_Label_Mapper_H_Passed: list(string);
    
    var Orig_Rel_Mapper_G_Passed: list(string);
    var Orig_Rel_Mapper_H_Passed: list(string);
    
    var graphDegree_passed: list(int); 
    var SubgraphDegree_passed: list(int);

    //var g1numVertices: int;
    //var g2numVertices: int;
    proc runVF2 (g1: SegGraph, g2: SegGraph, SubgraphDegree: [?D1] int, 
                    graphDegree: [?D2] int, Orig_Label_Mapper_G_to_Pass: [?D3] string, 
                    Orig_Label_Mapper_H_to_Pass: [?D4] string, Orig_Relationships_Mapper_G_to_Pass: [?D5] string, 
                    Orig_Relationships_Mapper_H_to_Pass: [?D6] string): ([] (int), int) throws {
        
        // Extract the g1/G information from PropGraph DS
        var srcNodesG1 = toSymEntry(g1.getComp("SRC"), int).a;
        var dstNodesG1 = toSymEntry(g1.getComp("DST"), int).a;
        var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS"), int).a;
        var edgeRelationshipsGraphG4 = toSymEntry(g1.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var nodeLabels_GraphG1 = toSymEntry(g1.getComp("VERTEX_LABELS"), domain(int)).a;

        // Extract the g2/H information from PropGraph DS
        var srcNodesG2 = toSymEntry(g2.getComp("SRC"), int).a;
        var dstNodesG2 = toSymEntry(g2.getComp("DST"), int).a;
        var segGraphG2 = toSymEntry(g2.getComp("SEGMENTS"), int).a;
        var edgeRelationshipsGraphG2 = toSymEntry(g2.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
        var nodeLabels_GraphG2 = toSymEntry(g2.getComp("VERTEX_LABELS"), domain(int)).a;
        
        var vf2List = vf2(g1, g2);
        var vf2FoundIsoArr: [1..0] int;

        writeln("segGraphG2.type = ", segGraphG2.type():string);        
        // Function to check is there any edge from Source node to Destination node. 
        // If there is it will get back the Original Relationship (Label) from the mapped INDEX
        proc PropGraphRelationshipMapper(PropGraph: SegGraph, fromNode: int, toNode: int, Mapper: list(string)): (bool, string) throws {
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
                //writeln("edgeRelationshipsGraph[Edge_found] = ", edgeRelationshipsGraph[Edge_found]);
                for elemnts in setToConvert{
                    StringLabelValue = Mapper[elemnts];
                }

            }

            return (BoolValue, StringLabelValue);

        }
        proc PropGraphNodeLabelMapper(PropGraph: SegGraph, srearchNode: int, Mapper: list(string)): (bool, string) throws {
            //writeln("-----------------PropGraphNodeLabelMapper called-------------------\n");

            var BoolValue : bool = false;
            var StringLabelValue : string;

            // Extract the graph information needed for Graph Vertex Labels! 
            //const ref label_mapper_Graph_entry = toSegStringSymEntry(PropGraph.getComp("VERTEX_LABELS_MAP"));
            //var label_mapper_Graph = assembleSegStringFromParts(label_mapper_Graph_entry.offsetsEntry, label_mapper_Graph_entry.bytesEntry, SymTablePassed);

            //writeln("Mapper = ",Mapper);
        
            var setToConvert =  nodeLabels_Graph[srearchNode];

            // remember make a time to write an IF to check the existing of index!!
            // if it was out of range return FALSE
            for elemnts in setToConvert{
                    StringLabelValue = Mapper[elemnts];
                    //writeln("StringLabelValue = ", StringLabelValue);
            }
            if StringLabelValue.size > 0 then {
            BoolValue = true;
            } // If there is at least 1 label, print out the string representation of the one at index 0.
            /*if PropGraph.hasComp("NODE_MAP"){
            var NodeMaplVAr = toSymEntry(PropGraph.getComp("NODE_MAP"));
            writeln("*********************55555555555555555555555***********************");
            writeln("NodeMaplVAr = ", NodeMaplVAr );
            }   
            else 
            {
            writeln("WE HAVE NOTHING HERE"); 
            } */   
            //writeln("0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-0-");
            //writeln("Check availability of Orig_Label_Mapper_Graph_Passed: ", Orig_Label_Mapper_Graph_Passed);
            return (BoolValue, StringLabelValue);
        }
        
        // State record 
        record State {
            var n1: int;
            var n2: int;

            var D1 = {0..<n1};
            var D2 = {0..<n2};

            // Core vectors
            var core1: [D1] int = -1;
            var core2: [D2] int = -1;
            
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

                this.D1 = {0..<this.n1};
                this.D2 = {0..<this.n2};
            
                this.core1 = -1;
                this.core2 = -1;
            
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

                this.D1 = {0..<this.n1};
                this.D2 = {0..<this.n2};

                this.core1 = -1;
                this.core2 = -1;

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

                core1 = -1; // reset to -1
                core2 = -1;

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
                core1[x1] = x2;
                core2[x2] = x1;

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
                    if core1(node) != -1 {
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
                    if core2(node) != -1 {
                        return true;
                    }
                }
                // Node outside bounds, return false
                return false;
            }

        }// end of State record


        ////////////////////////////////////////////checked////////////////////////////////////
        // Get nodes that point to node 
        proc getInNeighbors(graph: SegGraph, node: int, Mapper: list(string)) throws {
            writeln("-----------------getInNeighbors called-------------------");
            writeln("-----------------for ",node, "-------------------");
            var inNeighbors: list(int);

            // Loop through all nodes
            forall i in 0..graph.n_vertices-1 with(ref inNeighbors){

                // Check if i points to node
                if PropGraphRelationshipMapper(graph, i, node,  Mapper)[0]{
        
                    // Node i points to node, so it is an in-neighbor  
                    inNeighbors.pushBack(i);

                }

            }
            //writeln("-----------------inNeighbors = ",inNeighbors, "-------------------");
            return inNeighbors;        
        }

        // Get nodes pointed to from 'node'
        proc getOutNeighbors(graph: SegGraph, node: int, Mapper: list(string)) throws {
            writeln("-----------------getOutNeighbors called-------------------");
            writeln("-----------------for ",node, "-------------------\n");
            var srcNodes = toSymEntry(graph.getComp("SRC"), int).a;
            var dstNodes = toSymEntry(graph.getComp("DST"), int).a;
            var segGraph = toSymEntry(graph.getComp("SEGMENTS"), int).a;
            var edgeRelationshipsGraph = toSymEntry(graph.getComp("EDGE_RELATIONSHIPS"), domain(int)).a;
            
            var adj_list_of_node_start = segGraph[node];
            var adj_list_of_node_end = segGraph[node+1]-1;
            
            var outNeighbors = dstNodes[adj_list_of_node_start..adj_list_of_node_end];
            writeln("-----------------getOutNeighbors  = ",outNeighbors);

            return outNeighbors;
       
        }

        proc addToTinTout(ref state: State, u : int, v: int, g1 : SegGraph, g2: SegGraph): State throws {
            writeln("-----------------addToTinTout called-------------------");
            writeln("-----------------for", u, ", ", v, "-------------------\n");
            writeln("-----------------State = ", state);

            // Get in and out neighbors
            var inNeighbors = getInNeighbors(g1, u, Orig_Rel_Mapper_G_Passed);
            var outNeighbors = getOutNeighbors(g1, u, Orig_Rel_Mapper_G_Passed);
            writeln("inNeighbors (",u,")= ", inNeighbors);
            writeln("outNeighbors (", u,")= ", outNeighbors);

            // Add neighbors of u to tin1, tout1 from g1
            if state.Tin1.contains(u) {
                state.Tin1.remove(u); 
            }

            if state.Tout1.contains(u) {
                state.Tout1.remove(u);
            }

            // Add unmapped neighbors to Tin
            for n1 in inNeighbors {
                if state.core1[n1] == -1 {
                    state.Tin1.add(n1);
                }
            }
            // Add unmapped neighbors to Tout
            for n1 in outNeighbors {
                if state.core1[n1] == -1 {
                    state.Tout1.add(n1);
                }
            }

            // Add neighbors of v to tin2, tout2 from g2

            // Get in and out neighbors
            var inNeighborsg2 = getInNeighbors(g2, v, Orig_Rel_Mapper_H_Passed);
            var outNeighborsg2 = getOutNeighbors(g2, v, Orig_Rel_Mapper_H_Passed);
            writeln("inNeighbors (",v,")= ", inNeighbors);
            writeln("outNeighbors (", v,")= ", outNeighbors);
            
            if state.Tin2.contains(v) {
                state.Tin2.remove(v); 
            }
            if state.Tout2.contains(v) {
                state.Tout2.remove(v);
            }
            // Add unmapped neighbors to Tin
            writeln("g2 , inNeighbors begin");
            for n2 in inNeighborsg2 {
                if state.core2[n2] == -1 {
                    state.Tin2.add(n2);
                }
            }
            writeln("g2 , outNeighbors begin");

            // Add unmapped neighbors to Tout
            for n2 in outNeighborsg2 {
                if state.core2[n2] == -1 {
                    state.Tout2.add(n2);
                }
            }

            writeln(" state afte tin tout = ", state); 
            return state;
        }

        // Create initial state with empty mappings, vectors, etc
        proc createInitialState(g1: SegGraph, g2: SegGraph) throws {

            writeln("-----------------createInitialState called-------------------\n");

            var state = new State();

            state.init(g1.n_vertices, g2.n_vertices);

            state.core1 = -1; 
            state.core2 = -1;
            state.depth = 0;
            return state;

        }
        // Create candidates based on current state and retuns a list of pairs
        proc getCandidatePairs(state:State, g1:SegGraph , g2:SegGraph) throws {
            writeln("-----------------getCandidatePairs called-------------------\n");
            /*
            record TupleComparator {

                proc compare(a: (int, int), b: (int, int)) {


                // Check second value first
                if a(1) < b(1) then return -1;  
                if a(1) > b(1) then return 1;

                // Check first value if second is equal
                if a(0) < b(0) then return -1;
                if a(0) > b(0) then return 1;

                return 0;
                
                }

            }*/

            //var candidates = new sortedSet((int, int), comparator=new TupleComparator());
            var candidates = new set((int, int));
            // Use Tout sets
            for n1 in state.Tout1 {
                for n2 in state.Tout2 {
                candidates.add((n1, n2));
                }
            }
            //writeln("candidates after Tout = ", candidates);
            // Use Tin sets
            if candidates.isEmpty() {
                for n1 in state.Tin1 {
                    for n2 in state.Tin2 {
                        candidates.add((n1, n2));  
                    }
                }
            }
            //writeln("candidates after Tin = ", candidates);

            // Check unmapped nodes if still empty
            if candidates.isEmpty() {
                //writeln("Tin was emptyXXXXXXX");

                // Get product of unmapped nodes
                var unmapped1 = getUnmappedNodesg1(g1, state);
                var unmapped2 = getUnmappedNodesg2(g2, state);

                // Add their product
                for n1 in unmapped1 {
                    for n2 in unmapped2 {
                        candidates.add((n1, n2));
                    }
                }

            }
            //writeln("candidates in return = ", candidates);

            return candidates;

        }
        // Two silly function. wrote just to quick check but worked.LOL
        proc getUnmappedNodesg1(graph: SegGraph, state: State) throws {
            var unmapped: list(int);

            for n in 0..<graph.n_vertices {
                if !state.isMappedn1(n) {
                    unmapped.pushBack(n);
                }
            }

            return unmapped;
        }

        proc getUnmappedNodesg2(graph, state) {
            var unmapped: list(int);

            for n in 0..<graph.n_vertices {
                if !state.isMappedn2(n) {
                    unmapped.pushBack(n);
                }
            }

            return unmapped;
        }
        // Check node labels are the same
        proc nodesLabelCompatible(n1: int, n2: int, g1: SegGraph, g2: SegGraph): bool throws {
            writeln("-----------------nodesLabelCompatible called-------------------\n");

            //var label1 = g1.nodeLabels[n1];
            //var label2 = g2.nodeLabels[n2];

            var label1 = PropGraphNodeLabelMapper(g1, n1, Orig_Label_Mapper_G_Passed)[1];
            var label2 = PropGraphNodeLabelMapper(g2, n2, Orig_Label_Mapper_H_Passed)[1];
            writeln("label1 = ", label1);
            writeln("label2 = ", label2);

            if label1 != label2 {
                return false;
            }

            return true;

        }
        //Edge label checking:
        proc edgesLabelCompatible(n1, n2, x1, x2, g1: SegGraph, g2: SegGraph): bool throws{
            writeln("-----------------edgesLabelCompatible called-------------------\n");

            //var label1 = g1.edgeLabels[n1, x1];  
            //var label2 = g2.edgeLabels[n2, x2];

            var label1 = PropGraphRelationshipMapper(g1, n1, x1, Orig_Rel_Mapper_G_Passed)[1];
            var label1Reverse = PropGraphRelationshipMapper(g1, x1, n1, Orig_Rel_Mapper_G_Passed)[1];
            var label2 = PropGraphRelationshipMapper(g2, n2, x2, Orig_Rel_Mapper_H_Passed)[1]; 
            var label2Reverse = PropGraphRelationshipMapper(g2, x2, n2, Orig_Rel_Mapper_H_Passed)[1]; 
            writeln("edge label1 (",n1,", ",x1,")= ", label1);
            writeln("edge label1Reverse (",x1,", ",n1,")= ", label1Reverse);
            writeln("edge label2 (",n2,", ",x2,")= ", label2);
            writeln("edge label2Reverse (",x2,", ",n2,")= ", label2Reverse);        

            if label1 != label2 {
                return false;
            }        
            
            if label1Reverse != label2Reverse {
                return false;
            }
            
            return true;

        }

        // Get predecessors of a node from Graph
        proc getPredecessors(graph: SegGraph, node: int, Mapper: list(string)): list(int) throws {
            //writeln("-----------------getPredecessors called-------------------\n");

            var preds: list(int);
            var visited = new set(int); 
            var stack: list(int);
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
                    for nbr in getInNeighbors(graph, curr, Mapper) {
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
        }
        // Get successors of a node
        // by using a graph traversal breadth-first search approach
        //  * Uses distributed queue for scalable BFS. LOL
        proc getSuccessors(graph: SegGraph, node: int, Mapper: list(string)): list(int) throws {
            //writeln("-----------------getSuccessors called-------------------\n");

            var visited = new set(int);
            var succs: list(int); 
            
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
                for nbr in getOutNeighbors(graph, curr, Mapper) {
                    
                    // Add as a successor  
                    succs.pushBack(nbr);
                    
                    // Enqueue next nodes  
                    queue.enqueue(nbr);    
                }

            }
            //writeln("getSuccessors retrun succs = ", succs);

            return succs;
        }

        // Get 2-hop neighbors
        proc get2HopNeighbors(graph, node, preds, Mapper: list(string)) throws{
            //writeln("-----------------get2HopNeighbors called-------------------\n");
            //writeln("-----------------for graph, node = ",node,"preds = ", preds," -------------------\n");
            
            // 1-hop neighbors
            var oneHop = if preds then getPredecessors(graph, node, Mapper) 
                        else getSuccessors(graph, node, Mapper);
            //writeln("oneHop = ", oneHop, " oneHop.type =",(oneHop.type):string);
            // 2-hop neighbors  

            var twoHop: list(int);
            //writeln("twoHop = ", twoHop, " twoHop.type =",(twoHop.type):string);

            for n in oneHop {
                var more = if preds then getPredecessors(graph, n, Mapper)
                        else getSuccessors(graph, n, Mapper);
                
                for m in more {
                    twoHop.pushBack(m);  
                }              
            }
            /*
    // Filter out dups
    twoHop = twoHop.uniq();

    // Remove 1-hop  
    twoHop = twoHop.except(oneHop);

            */
            //writeln("twoHop = ", twoHop);
            for n in oneHop {
                twoHop.remove(n);
            }
                //writeln("twoHop - oneHop = ", twoHop);// Exclude 1-hop neighbors

            return twoHop;
        }

        proc RsemanticFeasible(state, n1, n2, g1, g2) throws{
            writeln("-----------------RsemanticFeasible called-------------------\n");

            if !nodesLabelCompatible(n1, n2, g1, g2) {
                writeln("Node labels are Inconsistent");
                return false;
            }
            
            // Check edge compatibility
            for (x1, x2) in state.mapping {
                if !edgesLabelCompatible(n1, n2, x1, x2, g1, g2) {
                    writeln("Edge labels are Inconsistent");
                return false;
                }
            }

            return true;

        }

        // Checks that the proposed mapping of node n2 satisfies 
        // the ordering constraint relative to already mapped nodes.
        // Added to avoid multiple travel to a specific branch
        proc RMappingInOrder(state, n1, n2, g1, g2): bool {
            writeln("-----------------RMappingInOrder called-------------------\n");

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

        }

        // Rpred feasibility rule checks that the number of mapped predecessors is consistent 
        // between a candidate mapping of nodes n1 and n2.
        proc Rpred(state: State, n1: int, n2: int, g1:SegGraph , g2: SegGraph): bool throws {
            writeln("-----------------Rpred called-------------------\n");

            var n1Preds = getPredecessors(g1, n1, Orig_Rel_Mapper_G_Passed);
            var n2Preds = getPredecessors(g2, n2, Orig_Rel_Mapper_H_Passed);
            writeln("n1Preds = ", n1Preds);
            writeln("n2Preds = ", n2Preds);
            var n1Mapped = 0;
            for p in n1Preds {
                if state.isMappedn1(p) {
                n1Mapped += 1;
                }
            }
            writeln("n1Mapped = ", n1Mapped);

            var n2Mapped = 0;
            for p in n2Preds { 
                if state.isMappedn2(p) {
                n2Mapped += 1; 
                }
            }
            writeln("n2Mapped = ", n2Mapped);

            if n1Mapped != n2Mapped {
                return false;
            }

            return true;

        }

        //Rsucc - Successor Count Checking
        proc Rsucc(state: State, n1: int, n2: int, g1: SegGraph, g2: SegGraph): bool throws {
            writeln("-----------------Rsucc called-------------------\n");

            var n1Succs = getSuccessors(g1, n1, Orig_Rel_Mapper_G_Passed);
            var n2Succs = getSuccessors(g2, n2, Orig_Rel_Mapper_H_Passed);

            //writeln("n1Succs = ", n1Succs);
            //writeln("n2Succs = ", n2Succs);

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

        }

        // Rin checks that the number of unmapped in-neighbors of n1 (node from graph 1) 
        // is greater than or equal to the number of unmapped in-neighbors of n2 (node from graph 2).
        proc Rin(state, n1, n2, g1, g2): bool throws{
            writeln("-----------------Rin called-------------------\n");
            
            // Get unmapped in-neighbors
            var n1Pred = getPredecessors(g1, n1, Orig_Rel_Mapper_G_Passed);
            var n2Pred = getPredecessors(g2, n2, Orig_Rel_Mapper_H_Passed); 
    
            // Filter unmapped nodes
            //writeln("///// Filter unmapped nodes from Predecessors");
            var n1PredUnmapped, n2PredUnmapped, 
                n1SuccUnmapped, n2SuccUnmapped: domain(int);


            for n in n1Pred {
                if !state.isMappedn1(n) {
                    n1PredUnmapped += n;
                } 
            } 
            //writeln("n1PredUnmapped = ", n1PredUnmapped);

            for n in n2Pred {
                if !state.isMappedn2(n) {
                    n2PredUnmapped += n;
                } 
            } 
            //writeln("n2PredUnmapped = ", n2PredUnmapped);


            var n1Succ = getInNeighbors(g1, n1, Orig_Rel_Mapper_G_Passed);
            var n2Succ = getInNeighbors(g2, n2, Orig_Rel_Mapper_H_Passed);
            
            // Filter unmapped nodes
            //writeln("///// Filter unmapped nodes from InNeighbors");

            for n in n1Succ {
                if !state.isMappedn1(n) {
                    n1SuccUnmapped += n;
                } 
            } 
            //writeln("n1SuccUnmapped = ", n1SuccUnmapped);

            for n in n2Succ {
                if !state.isMappedn2(n) {
                    n2SuccUnmapped += n;
                } 
            } 
            //writeln("n2SuccUnmapped = ", n2SuccUnmapped);
    

            // Check predecessor counts
            if (n1PredUnmapped.size < n2PredUnmapped.size) {
                return false;
            }

            // Check successor counts 
            if (n1SuccUnmapped.size < n2SuccUnmapped.size) {
                return false;  
            }

            return true;

        }

        // Rout checks that the number of unmapped out-neighbors of n1 (node from graph 1) 
        // is greater than or equal to the number of unmapped out-neighbors of n2 (node from graph 2)
        proc Rout(state, n1, n2, g1, g2): bool throws{
            writeln("-----------------Rout called-------------------\n");
            var n1OutNbrs = getOutNeighbors(g1, n1, Orig_Rel_Mapper_G_Passed);
            var n2OutNbrs = getOutNeighbors(g2, n2, Orig_Rel_Mapper_H_Passed);

            // Filter unmapped 
            var n1OutUnmapped, n2OutUnmapped,
                n1PredUnmapped, n2PredUnmapped: domain(int);
            //writeln("///// Filter unmapped nodes from OutNeighbors");

            for n in n1OutNbrs {
                if !state.isMappedn1(n) {
                n1OutUnmapped += n;
                }
            }
            //writeln("n1OutUnmapped = ", n1OutUnmapped);

            for n in n2OutNbrs {
                if !state.isMappedn2(n) {
                n2OutUnmapped += n;
                }
            }
            //writeln("n2OutUnmapped = ", n2OutUnmapped);

            var n1Pred = getPredecessors(g1, n1, Orig_Rel_Mapper_G_Passed);
            var n2Pred = getPredecessors(g2, n2, Orig_Rel_Mapper_H_Passed);

            // Filter unmapped 
            //writeln("///// Filter unmapped nodes from Predecessors");

            for n in n1Pred {
                if !state.isMappedn1(n) {
                n1PredUnmapped += n;
                }
            }
            //writeln("n1PredUnmapped = ", n1PredUnmapped);

            for n in n2Pred {
                if !state.isMappedn2(n) {
                n2PredUnmapped += n;
                }
            }
            //writeln("n2PredUnmapped = ", n2PredUnmapped);
            if (n1OutUnmapped.size < n2OutUnmapped.size) {
                return false;
            }
            
            if (n1PredUnmapped.size < n2PredUnmapped.size) {
                return false;
            }

            return true;

        }

        // Rnew performs a 2-level lookahead in the search space 
        // to prune states that will have no valid successors after 
        // 2 steps.
        proc Rnew(state, n1, n2, g1, g2): bool throws {
            writeln("-----------------Rnew called-------------------\n");

            // Get 2-hop neighbors
            var n1Pred2 = get2HopNeighbors(g1, n1, true, Orig_Rel_Mapper_G_Passed); 
            var n2Pred2 = get2HopNeighbors(g2, n2, true, Orig_Rel_Mapper_H_Passed);

            var n1Succ2 = get2HopNeighbors(g1, n1, false, Orig_Rel_Mapper_G_Passed);
            var n2Succ2 = get2HopNeighbors(g2, n2, false, Orig_Rel_Mapper_H_Passed);

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

        }

        // Check if candidates' pairs are feasible
        proc isFeasible(state: State, n1: int, n2: int, g1: SegGraph, g2: SegGraph) throws {
            writeln("-----------------isFeasible called for (",n1,",", n2,")-------------------");
            

            if !RMappingInOrder(state,n1 ,n2 ,g1 ,g2): bool {
                writeln("Feasibility returned FALSE because of RMappingInOrder");
                return false;
            }  
        
            if !Rpred(state,n1 ,n2 ,g1 ,g2): bool {
                writeln("Feasibility returned FALSE because of Rpred");
                return false;
            }

            if !Rsucc(state,n1 ,n2 ,g1 ,g2): bool {
                writeln("Feasibility returned FALSE because of Rsucc");
                return false;
            }
            
            if !Rin(state, n1, n2, g1, g2) {
                writeln("Feasibility returned False because of Rin");
                return false;
            }

            if !Rout(state, n1, n2, g1, g2) {
                writeln("Feasibility returned False because of Rout");
                return false;
            }  
            
            if !Rnew(state,n1 ,n2 ,g1 ,g2): bool {
                writeln("Feasibility returned FALSE because of Rnew");
                return false;
            } 
            
            if !RsemanticFeasible(state, n1, n2, g1, g2) {
                writeln("Feasibility returned False because of RsemanticFeasible");
                return false;
            } 
            

            writeln("-----------------isFeasible PASSED ALL CHECKS-------------------");

            return true;// passed all checks
        }

        // Check if state is a valid solution 
        proc isSolution(state: State, g2: SegGraph): bool throws {
            writeln("-----------------isSolution called-------------------\n");
            
            // Check all g2 nodes mapped
            var allMapped = true;
            for n in 0..<g2.n_vertices {
                if !state.isMappedn2(n) {
                    allMapped = false;
                    break;
                }
            }

            if !allMapped {
                return false;
            }

            return true;
        }

        // This will traverse all the edges of each mapped node and ensure 
        // the connectivity is consistent between g1 and g2 subgraphs.
        proc validateMapping(state: State, g1: SegGraph, g2: SegGraph): bool throws {
            //writeln("-----------------validateMapping called-------------------\n");

            // Check all edges between mapped nodes
            for (n1, n2) in state.mapping {

                var outNeighborsn1 = getOutNeighbors(g1, n1, Orig_Rel_Mapper_G_Passed);
                var outNeighborsn2 = getOutNeighbors(g2, n2, Orig_Rel_Mapper_H_Passed);

                //for n1_neighbor in g1.adjacencyList[n1] {
                for n1_neighbor in outNeighborsn1 {
                
                    if state.isMappedn1(n1_neighbor) {

                        var n2_neighbor = state.core1[n1_neighbor];
                        
                        //if !g2.adjacencyList[n2].contains(n2_neighbor) {
                        if !outNeighborsn2.contains(n2_neighbor) {
                            writeln("Invalid mapping between ", n1, ", ", n2);
                            return false;
                        }
                    
                        // Check edge labels match
                        //if g2.edgeLabels[n2, n2_neighbor] != g1.edgeLabels[n1, n1_neighbor] {
                        if PropGraphRelationshipMapper(g2, n2, n2_neighbor, Orig_Rel_Mapper_H_Passed)[1] != PropGraphRelationshipMapper(g1, n1, n1_neighbor, Orig_Rel_Mapper_G_Passed)[1] {
                            writeln("Invalid edge label");
                            return false; 
                        }

                    } 
                }
            }

            return true;

        }

        // DFS like to traverse graph and returns list of all solution states 
        proc dfs(ref initialState: State, g1: SegGraph, g2: SegGraph): list(State) throws {
            writeln("-----------------dfs called-------------------\n");

            var allSolutions: list(State);
            
            // Stack defined for backtracking
            var stack: list(State);
            
            // Initialize stack
            stack.pushBack(initialState);
            writeln("initialState pushed to stack", initialState);

            while stack.size > 0 {
                var state = stack.popBack();

                writeln("pop happened stack.size = ", stack.size,"\n");
                writeln("\nworking state now is:", state);

                
                if state.mapping.size == g2.n_vertices {
                    writeln("if state.mapping.size == g2.n_vertices { WORKED ");
                    if isSolution(state, g2) {
                        //writeln("isSolution = TRUE");
                        //if !allSolutions.contains(state){
                            allSolutions.pushBack(state);
                        //} 
                writeln("************************NEW ISO FOUND: ", state.mapping);
                writeln("now the stack.size = ", stack.size,"\n");
                    }

                }
                var candidates = getCandidatePairs(state, g1, g2);
                writeln("Candidate (new version) has: #",candidates.size," to check = ",candidates,"\n" );
                
                //var counter: int = 0;
                for (n1, n2) in candidates {
                    
                    //counter += 1;
                    var newState = state.copy();
                    
                    //if newState.mapping.size < g2.n_vertices{
                        //writeln("newState.mapping.size = ", newState.mapping.size);
                        //writeln("g2.n_vertices = ", g2.n_vertices);
            
                        if isFeasible(newState, n1, n2, g1, g2) {
                            newState.addPair(n1, n2);
                            newState = addToTinTout(newState, n1, n2, g1, g2);
                        
                            // I beleive this "validateMapping" WAS NOT in VF2. ?!
                            // so we had a lot of usless processing
                            // read paper again to be sure!

                            //if validateMapping(newState, g1, g2){

                                stack.pushBack(newState);
                        
                                //writeln("push happened stack.size = ", stack.size,"\n");
                                //writeln("newly added state is :", newState.mapping);

                        //}
                        }
                
                    //}
                    //writeln("counter = ", counter);   
                }
                writeln("end of checking all current candidates\n");
                state.reset();

            }

            return allSolutions; // solution
            
        } 
        // Main procudre of VF2 Subgraph Isomorphism
        proc vf2(g1: SegGraph, g2: SegGraph): list(int) throws {
            
            //writeln("-----------------vf2 called-------------------\n");

            var subIsoListToReturn: list(int);
            
            //var Orig_Label_Mapper_G_Passed = Orig_Label_Mapper_G_to_Pass;
            //Initializing Node labels Mappers
            /*  for e in Orig_Label_Mapper_G_to_Pass {
            Orig_Label_Mapper_G_Passed.pushBack(e); 
            }
            for e in Orig_Label_Mapper_H_to_Pass {
            Orig_Label_Mapper_H_Passed.pushBack(e); 
            }
            //Initializing edge labels Mappers
            for e in Orig_Relationships_Mapper_G_to_Pass {
            Orig_Rel_Mapper_G_Passed.pushBack(e); 
            }
            for e in Orig_Relationships_Mapper_H_to_Pass {
            Orig_Rel_Mapper_H_Passed.pushBack(e); 
            }         
            
            for e in graphDegree {
            graphDegree_passed.pushBack(e); 
            }
            
            //writeln("graphDegree_passed = ", graphDegree_passed);
                    
            for e in SubgraphDegree {
            SubgraphDegree_passed.pushBack(e);  
            }
            */
            //writeln("SubgraphDegree_passed = ", SubgraphDegree_passed);
            //g1numVertices = g1.n_vertices;
            //g2numVertices = g2.n_vertices;

            //writeln("g1.n_vertices.type = ", g1.n_vertices.type:string);

            var initial = createInitialState(g1, g2);
            var solutions = dfs(initial, g1, g2);
            //var solutions: list(State);
            /////////////////////////////test area - should be deleted///////////////////////////
            //{7: 0, 0: 1, 1: 2, 3: 3}
            //{7: 0, 0: 1, 3: 2, 2: 3}
            /*
            initial.addPair(7, 0);
            initial = addToTinTout(initial, 7, 0, g1, g2);        
            
            initial.addPair(0, 1);
            initial = addToTinTout(initial, 0, 1, g1, g2);        
            
            //initial.addPair(0, 2);
            //initial = addToTinTout(initial, 0, 2, g1, g2);
            writeln("initial = ",initial );
            var candidates = getCandidatePairs(initial, g1, g2);
            writeln("Candidate (new version) has: #",candidates.size," to check = ",candidates,"\n" );

                var newState = initial.copy();
                isFeasible(newState, 1, 2, g1, g2);

            writeln("-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+\n" );

                var newState1 = initial.copy();
                isFeasible(newState1, 3, 2, g1, g2);
            /////////////////////////////end test area///////////////////////
            */
            /* record TupleComparator {

                    proc compare(a: (int, int), b: (int, int)) {


                    // Check second value first
                    if a(1) < b(1) then return -1;  
                    if a(1) > b(1) then return 1;

                    // Check first value if second is equal
                    if a(0) < b(0) then return -1;
                    if a(0) > b(0) then return 1;

                    return 0;
                    
                    }

                }

                var candidatesinorder = new sortedSet((int, int), comparator=new TupleComparator());*/
                var i = 1;
                for solution in solutions {
                    writeln("\nMapping #",i,":");
                    writeln("\n",solution.mapping);
                    i += 1;
                    for (x1, x2) in solution.mapping {
                        write(x2, " : ", x1, ",");
                        subIsoListToReturn.pushBack(x1);
                    }

                }


            writeln("\nsubIsoListToReturn = ", subIsoListToReturn);
            writeln("Found isos = ", subIsoListToReturn.size);

            return(subIsoListToReturn);
        } //end of VF2
        
        return(vf2FoundIsoArr, vf2FoundIsoArr.size);

    } //end of runVF2
} // end of module
