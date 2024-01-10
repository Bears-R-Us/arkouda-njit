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
    
    :arg graph: graph whose vertex triangle centralities we want to find.
    :arg triangleCentralities: array to store the triangle centrality for each vertex.
    :type triangleCentralities: [?D] real
    
    :returns: void
    */
    proc minimum_search_triangle_centrality(graph: borrowed SegGraph, ref triangleCentralities) throws {
	    ref src = toSymEntry(graph.getComp("SRC"), int).a;
        ref dst = toSymEntry(graph.getComp("DST"), int).a;
        ref seg = toSymEntry(graph.getComp("SEGMENTS"), int).a;
        ref vertexMap = toSymEntry(graph.getComp("VERTEX_MAP"), int).a;

        // Number of triangles each neighbor of u is a part of
        var NeiTriNum = makeDistArray(graph.n_vertices, atomic int); 
        
        // Number of triangles that u is a part of 
        var TriNum = makeDistArray(graph.n_vertices, atomic int);
        
        // Denotes if some edge e is part of a triangle edge
        var NeiAry = makeDistArray(graph.n_edges, bool);

        NeiAry = false;
        forall (x,y) in zip(NeiTriNum, TriNum) {
            x.write(0); y.write(0);
        }

        var triCount:int = 0;
        
        // Counts total triangles, populates TriNum, and populates NeiAry
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

        /* NOTE: Due to the symmetrical DI data structure, each edge is processed twice. Due to the
        nature of triangle counting, each triangle is counted three times. Therefore, the triangle
        counting above counts each triangle 6 times, that we take into account by dividing by 6
        below.*/
        
        // Counts number of neighbor triangles for a vertex v
        forall i in src.domain {
            var u = src[i];
            var v = dst[i];
            if NeiAry[i] then NeiTriNum[u].add(TriNum[v].read() / 6);
        }

        // Calculates centralities
        forall u in vertexMap.domain {
            var curnum = 0;
            ref neighborhood = dst[seg[u]..seg[u+1]-1];
            for w in neighborhood do if w != u then curnum += (TriNum[w].read() / 6);
            triangleCentralities[u] = (
                    (TriNum[u].read() / 6) +
                    (curnum - (NeiTriNum[u].read() + TriNum[u].read() / 6) * 2.0 / 3.0)
            ):real / (triCount / 6.0):real;
        }
    } // end of minimum_search_triangle_centrality
}// end of TriangleCentrality module