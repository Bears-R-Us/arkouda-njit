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
    * Returns the triangle centrality for each vertex of the graph.
    *
    * :arg graph: SegGraph whose triangles we want to find.
    * :type graph: borrowed SegGraph
    *
    * :returns: int
    */
    proc minimum_search_triangle_centrality(graph: borrowed SegGraph, ref triangleCentralities) throws {
	    ref src = toSymEntry(graph.getComp("SRC"), int).a;
        ref dst = toSymEntry(graph.getComp("DST"), int).a;
        ref vertexMap = toSymEntry(graph.getComp("VERTEX_MAP"), int).a;
        ref seg = toSymEntry(graph.getComp("SEGMENTS"), int).a;

        var numOpenTriangles = makeDistArray(graph.n_vertices, atomic int);
        var numClosedTriangles = makeDistArray(graph.n_vertices, atomic int);
        var triangles = makeDistArray(graph.n_vertices, atomic int);
        var edgesWithTriangles = makeDistArray(graph.n_edges, bool);

        edgesWithTriangles = false;
        forall (x,y,z) in zip(numOpenTriangles, numClosedTriangles, triangles) {
            x.write(0); y.write(0); z.write(0);
        }

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
                    for (w,j) in zip(neighborhood,neighborhood.domain) { // get every neighbor of s
                        var edge:int;
                        if (l != w && s != w) { // don't process l itself in neighbors of s
                            var dw = seg[w+1] - seg[w];
                            if (dl < dw) then edge = getEdgeId(l,w,dst,seg); // l is smaller, search w in adjacency list of l
                            else edge = getEdgeId(w,l,dst,seg); // w is smaller, search l in adjacency list of w
                            if (edge != -1) {
                                triCount += 1;
                                triangles[s].add(1);
                                triangles[l].add(1);
                                triangles[w].add(1);
                                edgesWithTriangles[i] = true;
                                edgesWithTriangles[j] = true;
                                edgesWithTriangles[edge] = true;
                            }
                        }
                    }
                }
            }      
        }

        forall i in src.domain {
            var u = src[i];
            var v = dst[i];

            if edgesWithTriangles[i] {
                numOpenTriangles[u].add(triangles[v].read());
                numOpenTriangles[v].add(triangles[u].read());
            } else {
                numClosedTriangles[u].add(triangles[v].read());
                numClosedTriangles[v].add(triangles[u].read());
            }
        }

        forall u in vertexMap.domain {
            var cumNeighborTriangleSum = 0;
            ref neighborhood = dst[seg[u]..seg[u+1]-1];
            for w in neighborhood do cumNeighborTriangleSum += triangles[w].read();
            triangleCentralities[u] = 
                (   cumNeighborTriangleSum - 
                    (numOpenTriangles[u].read()+triangles[u].read()) + 
                    triangles[u].read()
                ) / triCount;
        }
    } // end of minimum_search_triangle_count_kernel
}// end of TriangleCentrality module