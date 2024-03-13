module BreadthFirstSearch {
    // Chapel modules.
    use Reflection;
    use List;
    use ReplicatedDist;

    // Package modules.
    use CopyAggregation;

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
    * Breadth-first search for shared-memory (one locale) systems.
    *
    * graph: graph to run bfs on. 
    *
    * returns: success string message. */
    proc bfs_kernel_und_smem(graph:SegGraph, root:int, ref depth: [?D] int):string throws {
        // Extract graph data.
        var src = toSymEntry(graph.getComp("SRC_SDI"),int).a;
        var dst = toSymEntry(graph.getComp("DST_SDI"),int).a;
        var seg = toSymEntry(graph.getComp("SEGMENTS_SDI"),int).a;
        
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
                var adj_list_start = seg[u];
                var num_neighbors = seg[u+1] - adj_list_start;
                if (num_neighbors != 0) {
                    var adj_list_end = adj_list_start + num_neighbors - 1;
                    ref neighborhood = dst.localSlice(adj_list_start..adj_list_end);
                    for v in neighborhood {
                        if (depth[v] == -1) {
                            pending_work = true;
                            depth[v] = cur_level + 1;
                            frontier_sets[(frontier_sets_idx + 1) % 2].pushBack(v);
                        }
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
    proc bfs_kernel_und_dmem_opt(graph:SegGraph, root:int, ref depth: [?D] int):string throws {
        // Initialize the frontiers on each of the locales.
        coforall loc in Locales with (ref frontier_sets) do on loc {
            frontier_sets[0] = new list(int, parSafe=true);
            frontier_sets[1] = new list(int, parSafe=true);
        } 
        frontier_sets_idx = 0;
        const ref src = toSymEntry(graph.getComp("SRC_SDI"),int).a;
        const ref dst = toSymEntry(graph.getComp("DST_SDI"),int).a;
        const ref seg = toSymEntry(graph.getComp("SEGMENTS_SDI"),int).a;
        const ref ranges = graph.getComp("RANGES_SDI").getRanges();
        
        // Add the root to the locale that owns it and update size & depth.
        for lc in find_locs(root, ranges) {
            on lc do frontier_sets[frontier_sets_idx].pushBack(root);
        }
        var cur_level = 0;
        depth[root] = cur_level;

        while true { 
            var pending_work:bool;
            coforall loc in Locales with(|| reduce pending_work, ref depth, ref frontier_sets) {
                on loc {
                    var src_low = src.localSubdomain().low;
                    var src_high = src.localSubdomain().high;
                    forall u in frontier_sets[frontier_sets_idx] with (|| reduce pending_work, var frontier_agg = new ListDstAggregator(int)/*, var depth_agg = new DstAggregator(int)*/) {
                        var adj_list_start = seg[u]; // Possible remote read.
                        var num_neighbors = seg[u+1] - adj_list_start; // Possible remote read.
                        if (num_neighbors != 0) {
                            var adj_list_end = adj_list_start + num_neighbors - 1;
                            
                            // Only pull the part of the adjacency list that is local.
                            var actual_start = max(adj_list_start, src_low);
                            var actual_end = min(src_high, adj_list_end);
                            const ref neighborhood = dst.localSlice(actual_start..actual_end);

                            for (i,v) in zip(neighborhood.domain, neighborhood) { 
                                if (depth[v] == -1) {
                                    pending_work = true;
                                    depth[v] = cur_level + 1; // Really no way to make this write "local"? Maybe compiler is automating aggregations here?
                                    // depth_agg.copy(depth[v], cur_level + 1); // Really bad performance! Why?
                                    var locs = find_locs(v, ranges);
                                    for lc in locs do frontier_agg.copy(lc.id, v);
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
    }// end of bfs_kernel_und_dmem_opt
}// end of BreadthFirstSearch module