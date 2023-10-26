module TriangleCount {
    // Chapel modules.
    use Time;
    
    // Arachne modules.
    use GraphArray;
    use Utils;

    // Arkouda modules.
    use MultiTypeSymEntry;
    
    /**
    * Extract the integer identifier for an edge `<u,v>`. TODO: any function that queries into the 
    * graph data structure should probably be a class method of SegGraph.
    *
    * :arg u: source vertex to index for.
    * :type u: int
    * :arg v: destination vertex v to binary search for
    * :type v: int
    * :arg graph: Graph to search within.
    * :type graph: borrowed SegGraph
    *
    * :returns: int
    */
    proc getEdgeId(u:int, v:int, ref dst:[?D1] int, ref seg:[?D2] int): int throws {
        var start = seg[u];
        var end = seg[u+1]-1;
        var eid = bin_search_v(dst, start, end, v);

        return eid;
    }

    /**
    * Returns the number of triangles found in the graph. 
    *
    * :arg graph: SegGraph whose triangles we want to find.
    * :type graph: borrowed SegGraph
    *
    * :returns: int
    */
    proc minimum_search_triangle_count_kernel(graph: borrowed SegGraph): int throws {
	    ref src = toSymEntry(graph.getComp("SRC"), int).a;
        ref dst = toSymEntry(graph.getComp("DST"), int).a;
        ref seg = toSymEntry(graph.getComp("SEGMENTS"), int).a;
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
                    for w in neighborhood { // get every neighbor of s
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
      	ref src = toSymEntry(graph.getComp("SRC"), int).a;
        ref dst = toSymEntry(graph.getComp("DST"), int).a;
        ref seg = toSymEntry(graph.getComp("SEGMENTS"), int).a;
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
                    for w in neighborhood { // get every neighbor of s
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
        triCount = triCount / 2;
        return triCount;
    } // end of minimum_search_triangle_count_per_vertex
}// end of TriangleCount module