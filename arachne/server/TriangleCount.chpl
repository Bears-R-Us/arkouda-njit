module TriangleCount {
    // Chapel modules.
    use Time;
    
    // Arachne modules.
    use GraphArray;
    use Utils;
    
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
    proc getEdgeId(u:int, v:int, graph:SegGraph): int throws {
        var src = toSymEntry(graph.getComp("SRC"), int).a;
        var dst = toSymEntry(graph.getComp("DST"), int).a;
        var seg = toSymEntry(graph.getComp("SEGMENTS"), int).a;

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
    proc minimum_search_triangle_count_kernel(graph: SegGraph): int throws {
	    var src = toSymEntry(graph.getComp("SRC"), int).a;
        var dst = toSymEntry(graph.getComp("DST"), int).a;
        var seg = toSymEntry(graph.getComp("SEGMENTS"), int).a;
        var triCount:int = 0;
        
        var timer: stopwatch;
        timer.start();
        forall i in src.domain with (+ reduce triCount) { 
            var u = src[i];
            var v = dst[i];
            if u != v {
                var du = seg[u+1] - seg[u];
                var dv = seg[v+1] - seg[v];
                var s, l, ds, dl : int;
                if (du <= dv) { s = u; l = v; ds = du; dl = dv; } // u has smallest adjacency list
                else { s = v; l = u; ds = dv; dl = du; } // v has smallest adjacency list
                var nextStart = seg[s];
                var nextEnd = seg[s+1] - 1;
                if (ds > 0) {
                    forall w in dst.localSlice(nextStart..nextEnd) with (+ reduce triCount) {
                        // var w = dst[j]; // get every other neighbor of s
                        var edge:int;
                        if (l != w && s != w) { // don't process l itself
                            var dw = seg[w+1] - seg[w];
                            if (dl < dw) then edge = getEdgeId(l,w,graph); // l is smaller, search w in adjacency list of l
                            else edge = getEdgeId(w,l,graph); // w is smaller, search l in adjacency list of w
                            if (edge != -1) then triCount += 1;
                        }
                    }
                }
            }      
        }
        timer.stop();
        writeln("NESTED FORALL TRIANGLE COUNT TOOK: ", timer.elapsed());
        timer.clear();

        triCount = 0;
        timer.start();
        forall i in src.domain with (+ reduce triCount) { 
            var u = src[i];
            var v = dst[i];
            if u != v {
                var du = seg[u+1] - seg[u];
                var dv = seg[v+1] - seg[v];
                var s, l, ds, dl : int;
                if (du <= dv) { s = u; l = v; ds = du; dl = dv; } // u has smallest adjacency list
                else { s = v; l = u; ds = dv; dl = du; } // v has smallest adjacency list
                var nextStart = seg[s];
                var nextEnd = seg[s+1] - 1;
                if (ds > 0) {
                    for w in dst.localSlice(nextStart..nextEnd) {
                        // var w = dst[j]; // get every other neighbor of s
                        var edge:int;
                        if (l != w && s != w) { // don't process l itself
                            var dw = seg[w+1] - seg[w];
                            if (dl < dw) then edge = getEdgeId(l,w,graph); // l is smaller, search w in adjacency list of l
                            else edge = getEdgeId(w,l,graph); // w is smaller, search l in adjacency list of w
                            if (edge != -1) then triCount += 1;
                        }
                    }
                }
            }      
        }
        timer.stop();
        writeln("OUTER FORALL TRIANGLE COUNT TOOK: ", timer.elapsed());

        triCount = triCount / 2; // Each edge is processed twice, so divide by 2
        return triCount;
    } // end of minimum_search_triangle_count_kernel
}// end of TriangleCount module