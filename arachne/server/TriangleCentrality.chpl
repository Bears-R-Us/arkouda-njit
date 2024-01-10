module TriangleCentrality {
    // Chapel modules.
    use Atomics;

    // Arachne modules.
    use GraphArray;
    use Utils;

    // Arkouda modules.
    use AryUtil;
    use MultiTypeSymEntry;

    /**
    Returns the triangle centrality for each vertex of the graph.
    
    :arg graph: SegGraph whose TriNum we want to find.
    :arg triangleCentralities: array to store the triangle centrality for each vertex.
    :type triangleCentralities: [?D] real
    
    :returns: int
    */
    proc minimum_search_triangle_centrality(graph: borrowed SegGraph, ref triangleCentralities) throws {
	    ref src = toSymEntry(graph.getComp("SRC"), int).a;
        ref dst = toSymEntry(graph.getComp("DST"), int).a;
        ref seg = toSymEntry(graph.getComp("SEGMENTS"), int).a;
        ref vertexMap = toSymEntry(graph.getComp("VERTEX_MAP"), int).a;

        var NeiTriNum = makeDistArray(graph.n_vertices, atomic int);
        var NeiNonTriNum = makeDistArray(graph.n_vertices, atomic int);
        var TriNum = makeDistArray(graph.n_vertices, atomic int);
        var NeiAry = makeDistArray(graph.n_edges, bool);

        NeiAry = false;
        forall (x,y,z) in zip(NeiTriNum, NeiNonTriNum, TriNum) {
            x.write(0); y.write(0); z.write(0);
        }

        writeln("\n\n\n\n\n");
        writeln("src = ", src);
        writeln("dst = ", dst);

        writeln("\n\n\n\n\n");
        writeln("NeiTriNum = ", NeiTriNum);
        writeln("NeiNonTriNum = ", NeiNonTriNum);
        writeln("TriNum = ", TriNum);
        writeln("NeiAry = ", NeiAry);

        var triCount:int = 0;
        forall i in src.domain with (+ reduce triCount) { 
            var u = src[i];
            var v = dst[i];
            if (u != v) { // ignore self-loops
                var du = seg[u+1] - seg[u];
                var dv = seg[v+1] - seg[v];
                var s, l, ds, dl : int;
                if (du <= dv) { s = u; l = v; ds = du; dl = dv; } // u has smallest adjacency list
                else { s = v; l = u; ds = dv; dl = du; } // v has smallest adjacency list
                var nextStart = seg[s];
                var nextEnd = seg[s+1] - 1;
                if (ds > 0) {
                    ref neighborhood = dst[nextStart..nextEnd];
                    for (w,j) in zip(neighborhood,nextStart..nextEnd) { // get every neighbor of s
                        var edge:int;
                        if (l != w && s != w) { // don't process l itself in neighbors of s
                            var dw = seg[w+1] - seg[w];
                            if (dl < dw) then edge = getEdgeId(l,w,dst,seg); // l is smaller, search w in adjacency list of l
                            else edge = getEdgeId(w,l,dst,seg); // w is smaller, search l in adjacency list of w
                            if (edge != -1) {
                                triCount += 1;
                                TriNum[s].add(1);
                                TriNum[l].add(1);
                                TriNum[w].add(1);
                                NeiAry[i] = true;
                                NeiAry[j] = true;
                                NeiAry[edge] = true;
                            }
                        }
                    }
                }
            }      
        }

        // Get the actual number of triangles for each vertex without repeats.
        var TriNumFixed = makeDistArray(graph.n_vertices, int);
        forall (tris,tris_big) in zip(TriNumFixed, TriNum) do tris = tris_big.read() / 2;

        forall i in src.domain {
            var u = src[i];
            var v = dst[i];

            if NeiAry[i] then NeiTriNum[u].add(TriNumFixed[v]);
            else NeiNonTriNum[u].add(TriNumFixed[v]);
        }

        writeln("\n\n\n\n\n");
        writeln("NeiTriNum = ", NeiTriNum);
        writeln("NeiNonTriNum = ", NeiNonTriNum);
        writeln("TriNumFixed = ", TriNumFixed);
        writeln("NeiAry = ", NeiAry);


        writeln("\n\n\n\n\n");
        writeln("triCount = ", triCount);
        for u in vertexMap.domain {
            var curnum = 0;
            ref neighborhood = dst[seg[u]..seg[u+1]-1];
            for w in neighborhood do if w != u then curnum += (TriNumFixed[w]);
            writeln("curnum for ", u, " is ", curnum);
            writeln("NeiTriNum for ", u, " is ", NeiTriNum[u].read());
            writeln("TriNumFixed for ", u, " is ", TriNumFixed[u]);
            triangleCentralities[u] = 
                (
                    (TriNumFixed[u]) +
                    (curnum - (NeiTriNum[u].read() + TriNumFixed[u]) * (2.0 / 3.0))
                ):real / (triCount / 2.0):real;
            writeln();
        }

        writeln("\n\n\n\n\n");
        writeln("NeiTriNum = ", NeiTriNum);
        writeln("NeiNonTriNum = ", NeiNonTriNum);
        writeln("TriNumFixed = ", TriNumFixed);
        writeln("NeiAry = ", NeiAry);
        writeln("triangleCentralities = ", triangleCentralities);

        writeln("\n\n\n\n\n");

    } // end of minimum_search_triangle_count_kernel
}// end of TriangleCentrality module