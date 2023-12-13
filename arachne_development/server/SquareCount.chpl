module SquareCount {
    // Arachne modules.
    use GraphArray;

    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use AryUtil;

    /** 
    * Total degree order operator u << v compares the degrees of the two nodes and returns
    * true if the degree of u is less than the degree of v, or if equal, if the integer specifier
    * of u is less than that of v. 
    *
    * :arg u: vertex u
    * :type u: int
    * :arg v: vertex v
    * :type v: int
    * :arg degree: array containing degrees
    * :type degree: [?D] int
    *
    * :returns: bool */ 
    inline proc nodeCompare(u: int, v: int, ref degree): bool {
        if degree[u] < degree[v] then return true;
        else if degree[u] == degree[v] && u < v then return true; 
        else return false;
    }
    
    /** 
    * Sequential square counting for an undirected graph. 
    *
    * :arg graph: SegGraph to run square counting on. 
    * :type graph: SegGraph
    * :arg degree: degree sequence for each vertex u in the graph. 
    * :type degree: [?D] int
    *
    * :returns: int */
    proc squareCountSequential(graph:SegGraph, ref degree:[?D1] int):int throws {
        var src = toSymEntry(graph.getComp("SRC"),int).a;
        var dst = toSymEntry(graph.getComp("DST"),int).a;
        var seg = toSymEntry(graph.getComp("SEGMENTS"),int).a;

        var square_count:int = 0;
        var L : [0..<graph.n_vertices] int;
        L = 0;

        for v in L.domain {
            var v_adj_list_start = seg[v];
            var v_adj_list_end = seg[v+1] - 1;
            ref v_neighborhood = dst.localSlice(v_adj_list_start..v_adj_list_end);
            for u in v_neighborhood {
                if nodeCompare(u,v,degree) {
                    var u_adj_list_start = seg[u];
                    var u_adj_list_end = seg[u+1] - 1;
                    ref u_neighborhood = dst.localSlice(u_adj_list_start..u_adj_list_end);
                    for y in u_neighborhood {
                        if nodeCompare(y,v,degree) {
                            square_count += L[y];
                            L[y] += 1;  
                        }
                    }
                }
            }
            for u in v_neighborhood {
                if (nodeCompare(u,v,degree)) {
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
