module BreadthFirstSearch {
    // Chapel modules.
    use Reflection;
    use Set;
    use List;

    // Arachne modules.
    use GraphArray;
    use Utils;
    use Aggregators;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use AryUtil;

    /** 
    * Breadth-first search for shared-memory (one locale) systems. Uses a Chapel set for 
    *
    * graph: graph to run bfs on. 
    *
    * returns: success string message. */
    proc bfs_kernel_und_smem(graph:SegGraph, root:int, depth: [?D] int):string throws {
        // Extract graph data.
        var src = toSymEntry(graph.getComp("SRC"),int).a;
        var dst = toSymEntry(graph.getComp("DST"),int).a;
        var str = toSymEntry(graph.getComp("START_IDX"),int).a;
        var nei = toSymEntry(graph.getComp("NEIGHBOR"),int).a;
        
        // Generate the frontier sets.
        var frontier_sets : [{0..1}] list(int, parSafe=true);
        frontier_sets[0] = new list(int, parSafe=true);
        frontier_sets[1] = new list(int, parSafe=true);
        
        var frontier_sets_idx = 0;
        var cur_level = 0;
        depth[root] = cur_level;
        frontier_sets[frontier_sets_idx].pushBack(root);
        while true { 
            var pending_work:bool;
            forall u in frontier_sets[frontier_sets_idx] with (|| reduce pending_work) {
                ref neighborhood = dst.localSlice(str[u]..str[u]+nei[u]-1);
                for v in neighborhood {
                    if (depth[v] == -1) {
                        pending_work = true;
                        depth[v] = cur_level + 1;
                        frontier_sets[(frontier_sets_idx + 1) % 2].pushBack(v);
                    }
                }
            }
            frontier_sets[frontier_sets_idx].clear();
            if !pending_work {
                break;
            }
            cur_level += 1;
            frontier_sets_idx = (frontier_sets_idx + 1) % 2;
        }// end while 
        return "success";
    }// end of bfs_kernel_und_smem
        
    /** 
    * Using a remote aggregator above for sets, we are going to perform aggregated writes to the
    * locales that include the neighborhood of the vertex being processed.
    *
    * graph: graph to run bfs on. 
    *
    * returns: success string message. */
    proc bfs_kernel_und_dmem(graph:SegGraph, root:int, depth: [?D] int):string throws {
        // Initialize the frontiers on each of the locales.
        coforall loc in Locales do on loc {
            frontier_sets[0] = new set(int, parSafe=true);
            frontier_sets[1] = new set(int, parSafe=true);
        } 
        frontier_sets_idx = 0;
        var src = toSymEntry(graph.getComp("SRC"),int).a;
        var dst = toSymEntry(graph.getComp("DST"),int).a;
        var str = toSymEntry(graph.getComp("START_IDX"),int).a;
        var nei = toSymEntry(graph.getComp("NEIGHBOR"),int).a;
        
        // Add the root to the locale that owns it and update size & depth.
        for lc in find_locs(root, graph) {
            on lc do frontier_sets[frontier_sets_idx].add(root);
        }
        var cur_level = 0;
        depth[root] = cur_level;

        while true { 
            var pending_work:bool;
            coforall loc in Locales with(|| reduce pending_work) {
                on loc {
                    var edgeBegin = src.localSubdomain().low;
                    var edgeEnd = src.localSubdomain().high;
                    var vertexBegin = src[edgeBegin];
                    var vertexEnd = src[edgeEnd];
                    forall u in frontier_sets[frontier_sets_idx] with (|| reduce pending_work, var agg = new SetDstAggregator(int)) {
                        var numNF = nei[u];
                        var edgeId = str[u];
                        var nextStart = max(edgeId, edgeBegin);
                        var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                        ref neighborhood = dst.localSlice(nextStart..nextEnd);
                        for v in neighborhood { 
                            if (depth[v] == -1) {
                                pending_work = true;
                                depth[v] = cur_level + 1;
                                var locs = find_locs(v, graph);
                                for lc in locs {
                                    agg.copy(lc.id, v);
                                }
                            }
                        }
                    } //end forall
                    frontier_sets[frontier_sets_idx].clear();
                } // end on loc
            }// end coforall loc
            if !pending_work {
                break;
            }
            cur_level += 1;
            frontier_sets_idx = (frontier_sets_idx + 1) % 2;
        }// end while 
        return "success";
    }// end of bfs_kernel_und_dmem
}// end of BreadthFirstSearch module