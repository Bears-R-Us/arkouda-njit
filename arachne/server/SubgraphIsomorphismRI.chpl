module SubgraphIsomorphismRI {
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
    proc runRI (g1: SegGraph, g2: SegGraph, SubgraphDegree: [?D1] int, 
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

        var IsoArr:[0..1] int;
        //var IsoArrtemp = RIsearch(g1, g2);
/*
        writeln("RI working!");
        writeln("SubgraphDegree = ", SubgraphDegree);
        
        greatestConstraintFirst();

        // Record to track partial match 
        record MatchEntry {
            // map g2 vertex to g1 vertex
            var mapping: map(int, int);  
            // index up to which mapping is complete    
            var checkIndex: int;
        }
        
        record State {
            var unOrdered: list(int) = 0..#g2.n_vertices;

            var miu:[0..#g2.n_vertices] int = -1;
            // Tin tracks in-neighbors - nodes with edges to current partial mapping
            // Tout tracks out-neighbors - nodes with edges from current mapping
            var Tin2: domain(int);
            var Tout2: domain(int);
            var mapped:[0..#g2.n_vertices] bool = false;

        } // end of State record
        proc addToTinTout(ref state: State, v: int): State throws {
            //writeln("-----------------addToTinTout called-------------------");
            state.unOrdered.remove(v);
            state.mapped[v] = true;

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

        // Vertex order generation  
        proc greatestConstraintFirst() {
            
            var state = new State();
            // Order of vertices
            
            var urank: 3*int;

            // Find start vertex 
            var startVertex = SubgraphDegree.find(max reduce SubgraphDegree) ;
            writeln("startVertex =", startVertex);
            
            addToTinTout(state, startVertex);

            writeln("state addToTinTout=", state);

            // Set start vertex
            state.miu[0] = startVertex;
            sizemiu = 1;


            var parent:[0..#g2.n_vertices] int = -1;
            
            var parentmiu: list (int);
            var um: int = -1;
            parentmiu.pushBack(parent[0]);
            
            urank =  (-1,-1,-1);

            while(state.unOrdered.size>0) {

                um = sizemiu;
                for u in unOrdered {
                    // Labeled neighbors   
                    var labeledNeighbors = 0;
                    var extension = 0;
                    var candidates = 0;

                    // In Neighbours of G2
                    var adj_list_of_node_start = segRG2[u];
                    var adj_list_of_node_end = segRG2[u + 1]-1;

                    var getInN2_u = dstRG2[adj_list_of_node_start..adj_list_of_node_end];
                    for nodes in getInN2_u {
                        if miu.find(nodes) { //already in miu
                            labeledNeighbors += 1;
                        }
                        if miu.find(nodes) && (state.Tin2.contains(node) || state.Tout2.contains(node)) { //nodes not mapped yet and has edge to miumembers {
                            extension += 1;
                        }
                        if !miu.find(nodes) && !state.Tin2.contains(node) && !state.Tout2.contains(node) {  //not in miu
                            candidates += 1;
                        }
                    }

                    // Out Neighbours of G2
                    adj_list_of_node_start = segGraphG2[u];
                    adj_list_of_node_end = segGraphG2[u + 1]-1;
                
                    var getOutN2_u = dstNodesG2[adj_list_of_node_start..adj_list_of_node_end]; 
                    for nodes in getOutN2_u {
                        if miu.contain(nodes) {  //already in miu
                            labeledNeighbors += 1;
                        }
                        if miu.contain(nodes) && (state.Tin2.contains(node) || state.Tout2.contains(node)) { //nodes not mapped yet and has edge to miumembers {
                            extension += 1;
                        }
                        if !miu.contain(nodes) && !state.Tin2.contains(node) && !state.Tout2.contains(node) {  //not in miu
                            candidates += 1;
                        }
                    }
                    if urank !> (labeledNeighbors, extension, candidates) {
                        state.miu(m) = u;
                        urank = (labeledNeighbors, extension, candidates);
                    }

                }
                //for i in 
                state.miu[m] = ui;
                var inNeighborsg2_um = dstRG2[segRG2[um]..segRG2[um + 1]-1];
                var outNeighborsg2_um = dstNodesG2[segRG2[um]..segRG2[um + 1]-1];
                var ui = min reduce inNeighborsg2_um;
                var uiout = min reduce outNeighborsg2_um;
                if ui =< uiout  {
                    ui = uiout;
                }
                parent[um] = ui;
                //append um to miu
                state.miu[sizemiu] = um;
                sizemiu += 1;

                //append parent um to parentmiu
                parentmiu.pushBack(parent[um]);
                // V = V \ {um}
                state.unOrdered.remove(um);

            }//end while

            writeln("miu = ", miu, " parentmiu = ", parentmiu);
            return (miu, parentmiu);

        }

*/        
    return(IsoArr);
    } //end of runRI

} // end of module