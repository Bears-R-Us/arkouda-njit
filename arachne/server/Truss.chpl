module Truss {
    // Chapel modules.
    use Atomics;
    use Set;

    // Arachne modules.
    use GraphArray;
    use Utils;

    // Arkouda modules.
    use AryUtil;
    use MultiTypeSymEntry;

    proc k_truss(graph, k, containedEdges) throws {
        ref src = toSymEntry(graph.getComp("SRC"), int).a;
        ref dst = toSymEntry(graph.getComp("DST"), int).a;
        ref seg = toSymEntry(graph.getComp("SEGMENTS"), int).a;

        var edgesDeleted = makeDistArray(src.size, int);
        edgesDeleted = -1;

        // Preprocess to remove edges with degrees less than k-1.
        forall (u,v,i) in zip(src,dst,src.domain) {
            if (seg[u+1]-seg[u] < k-1) || (seg[v+1]-seg[v] < k-1) || (u == v) {
                edgesDeleted[i] = k-1;
            }
        }

        var triCount = makeDistArray(src.size, atomic int);

        // Calculate the number of triangles per edge.
        forall i in src.domain { 
            triCount[i].write(0);
            var u = src[i];
            var v = dst[i];
            var count:int = 0;
            if (edgesDeleted[i] <= -1) { // ignore edges that were deleted by degree or self-loops
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
                        if (l != w && s != w && edgesDeleted[j] <= -1) { // don't process l itself with w's or if the edge is deleted
                            var dw = seg[w+1] - seg[w];
                            if (dl < dw) then edge = getEdgeId(l,w,dst,seg); // l is smaller, search w in adjacency list of l
                            else edge = getEdgeId(w,l,dst,seg); // w is smaller, search l in adjacency list of w
                            if (edge != -1 && edgesDeleted[edge] <= -1) then count += 1;
                        }
                    }
                }
            }
            triCount[i].write(count);     
        }

        var removedEdges = new set(int);
        var pendingDeleteEdges = true;

        // Further mark the edges that did not meet the k-2 requirement with 1-k. 
        forall i in triCount.domain with (ref removedEdges) {
            if edgesDeleted[i] == -1 then if triCount[i].read() < k-2 {edgesDeleted[i] = 1-k; removedEdges.add(i);}
        }

        writeln("BEFORE WHILE LOOP");
        writeln("edgesDeleted = ", edgesDeleted);
        writeln("src = ", src);
        writeln("dst = ", dst);
        writeln("tri = ", triCount);
        writeln();

        var iteration = 0;
        while pendingDeleteEdges {
            // As long as there are edges that were removed, recalculate triangles.
            while removedEdges.size > 0 {
                forall i in removedEdges {
                    var u = src[i];
                    var v = dst[i];
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
                            if (l != w && s != w && edgesDeleted[j] <= -1) { // don't process l itself with w's or if the edge is deleted
                                var dw = seg[w+1] - seg[w];
                                if (dl < dw) then edge = getEdgeId(l,w,dst,seg); // l is smaller, search w in adjacency list of l
                                else edge = getEdgeId(w,l,dst,seg); // w is smaller, search l in adjacency list of w
                                if (edge != -1 && edgesDeleted[edge] <= -1) {
                                    if edgesDeleted[j] == -1 && edgesDeleted[edge] == -1 {
                                        triCount[edge].sub(1);
                                        triCount[j].sub(1);
                                    }
                                    if edgesDeleted[j] == -1 then triCount[j].sub(1);
                                    if edgesDeleted[edge] == -1 then triCount[edge].sub(1);

                                }
                            }
                        }
                    }
                }

                forall i in removedEdges do edgesDeleted[i] = 1-k;
                removedEdges.clear();

                // Mark the edges that did not meet the k-2 requirement, with 1-k.
                forall i in triCount.domain with (ref removedEdges) {
                    if edgesDeleted[i] == -1 then if triCount[i].read() < k-2 {edgesDeleted[i] = 1-k; removedEdges.add(i);}
                }

                writeln("AFTER ITERATION ", iteration);
                writeln("edgesDeleted = ", edgesDeleted);
                writeln("src = ", src);
                writeln("dst = ", dst);
                writeln("tri = ", triCount);
                writeln();
            }
            if removedEdges.size <= 0 then pendingDeleteEdges = false;
            iteration += 1;
        }
    }

    proc truss_decomposition(graph, containedEdges) {
        writeln("n\n\n\n\nHello 2!n\n\n\n\n");
    }

    proc max_truss(graph, containedEdges) {
        writeln("n\n\n\n\nHello 3!n\n\n\n\n");
    }

} // end of Truss module
