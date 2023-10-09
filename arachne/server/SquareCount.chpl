module SquareCount {
    // Arachne modules.
    use GraphArray;

    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use AryUtil;



    /** 
    * Sequential square counting for an undirected graph. 
    *
    * graph: SegGraph to run square counting on. 
    *
    * returns: integer square count. */
    proc square_count_sequential_kernel(graph:SegGraph, degree:[?D1] int):int throws {
        var src = toSymEntry(graph.getComp("SRC"),int).a;
        var dst = toSymEntry(graph.getComp("DST"),int).a;
        var seg = toSymEntry(graph.getComp("SEGMENTS"),int).a;

        var square_count:int = 0;
        var L : [0..<graph.n_vertices] int;
        L = 0;
        
        proc NodeCompare(u: int, v: int): bool {
             if degree[u] < degree[v] {
                return true;
            } else if degree[u] == degree[v] && u < v{
                return true ;
            }
        return false;
        }

        for v in L.domain {
            var v_adj_list_start = seg[v];
            var v_adj_list_end = seg[v+1] - 1;
            ref v_neighborhood = dst.localSlice(v_adj_list_start..v_adj_list_end);
            for u in v_neighborhood {
                if NodeCompare(u , v) {
                    var u_adj_list_start = seg[u];
                    var u_adj_list_end = seg[u+1] - 1;
                    ref u_neighborhood = dst.localSlice(u_adj_list_start..u_adj_list_end);
                    for y in u_neighborhood {
                        if NodeCompare(y , v) {
                            square_count += L[y];
                            L[y] += 1;  
                        }
                    }
                }
            }
            for u in v_neighborhood {
                if NodeCompare(u , v) {
                    var u_adj_list_start = seg[u];
                    var u_adj_list_end = seg[u+1] - 1;
                    ref u_neighborhood = dst.localSlice(u_adj_list_start..u_adj_list_end);
                    for y in u_neighborhood {
                        L[y] = 0;
                    }
                }
            }
        }
        return square_count;
    }
}