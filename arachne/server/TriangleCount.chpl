module TriangleCount {
    // Arachne modules.
    use GraphArray;
    use Utils;

    // Arkouda modules.
    use MultiTypeSymEntry;

    /**
    * Returns the number of triangles found in the graph. 
    *
    * :arg graph: SegGraph whose triangles we want to find.
    * :type graph: borrowed SegGraph
    *
    * :returns: int
    */
    proc minimum_search_triangle_count_kernel(graph: borrowed SegGraph): int throws {
	    ref src = toSymEntry(graph.getComp("SRC_SDI"), int).a;
        ref dst = toSymEntry(graph.getComp("DST_SDI"), int).a;
        ref seg = toSymEntry(graph.getComp("SEGMENTS_SDI"), int).a;
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
                    forall w in neighborhood with (+ reduce triCount) { // get every neighbor of s
                        var edge:int;
                        if (l != w && s != w) { // don't process l itself in neighbors of s
                            var dw = seg[w+1] - seg[w];
                            if (dl < dw) then edge = getEdgeId(l,w,dst,seg); // l is smaller, search w in adjacency list of l
                            else edge = getEdgeId(w,l,dst,seg); // w is smaller, search l in adjacency list of w
                            if (edge != -1) then triCount += 1;
                        }
                    }
                }
            }      
        }
        triCount = triCount / 2; // Each edge is processed twice, so divide by 2
        return triCount;
    } // end of minimum_search_triangle_count_kernel

    proc minimum_search_triangle_count_per_vertex(graph: borrowed SegGraph, vertex:int) throws {
      	ref src = toSymEntry(graph.getComp("SRC_SDI"), int).a;
        ref dst = toSymEntry(graph.getComp("DST_SDI"), int).a;
        ref seg = toSymEntry(graph.getComp("SEGMENTS_SDI"), int).a;
        var triCount:int = 0;
        var start = seg[vertex];
        var end = seg[vertex+1];
        forall i in src.domain[start..end] with (+ reduce triCount) { 
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
                    forall w in neighborhood with (+ reduce triCount) { // get every neighbor of s
                        var edge:int;
                        if (l != w && s != w) { // don't process l itself in neighbors of s
                            var dw = seg[w+1] - seg[w];
                            if (dl < dw) then edge = getEdgeId(l,w,dst,seg); // l is smaller, search w in adjacency list of l
                            else edge = getEdgeId(w,l,dst,seg); // w is smaller, search l in adjacency list of w
                            if (edge != -1) then triCount += 1;
                        }
                    }
                }
            }
        }
        triCount = triCount / 2; // Each edge is processed twice, so divide by 2
        return triCount;
    } // end of minimum_search_triangle_count_per_vertex
}// end of TriangleCount module