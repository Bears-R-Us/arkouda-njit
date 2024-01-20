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

        proc writeArray(ref arr) {
            for u in arr {
                if u < 0 then write(u, " ");
                else write(" ", u, " ");
            }
            write("\n");
        }

        proc writeAtomicArray(ref arr) {
            for u in arr {
                if u.read() < 0 then write(u.read(), " ");
                else write(" ", u.read(), " ");
            }
            write("\n");
        }

        writeln("BEFORE FIRST TRIANGLE COUNT");
        write("src = "); writeArray(src);
        write("dst = "); writeArray(dst);
        write("tri = "); writeAtomicArray(triCount);
        write("del = "); writeArray(edgesDeleted);
        writeln();

        // Calculate the number of triangles per edge.
        forall i in src.domain { 
            triCount[i].write(0);
            var u = src[i];
            var v = dst[i];
            var count:int = 0;
            if (edgesDeleted[i] == -1) { // only process edges that have not been deleted
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
                        if (l != w && s != w && edgesDeleted[j] <= -1) { // don't process l or s with themselves
                            var dw = seg[w+1] - seg[w];
                            if (dl < dw) then edge = getEdgeId(l,w,dst,seg); // l is smaller, search w in adjacency list of l
                            else edge = getEdgeId(w,l,dst,seg); // w is smaller, search l in adjacency list of w
                            if (edge != -1) {
                                if (edgesDeleted[edge] == -1 && edgesDeleted[j] == -1) then count += 1;
                            }
                        }
                    }
                }
            }
            triCount[i].write(count);
        }

        var removedEdges = new set(int, parSafe=true);
        var pendingDeleteEdges = true;

        // Further mark the edges that did not meet the k-2 requirement with 1-k. 
        forall i in triCount.domain with (ref removedEdges) {
            if edgesDeleted[i] == -1 then if triCount[i].read() < k-2 {edgesDeleted[i] = 1-k; removedEdges.add(i);}
        }

        writeln("BEFORE WHILE LOOP");
        write("src = "); writeArray(src);
        write("dst = "); writeArray(dst);
        write("tri = "); writeAtomicArray(triCount);
        write("del = "); writeArray(edgesDeleted);
        writeln("rem = ", removedEdges);
        writeln();

        var iteration = 0;
        while removedEdges.size > 0 {
            writeln("ITERATION ", iteration, " $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");
            for i in removedEdges {
                var u = src[i];
                var v = dst[i];
                if u < v {
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
                            if (l != w && s != w && edgesDeleted[j] <= -1) { // don't process l or s with themselves
                                var dw = seg[w+1] - seg[w];
                                writeln("s = ", s, " l = ", l, " w = ", w, " ds = ", ds, " dl = ", dl, " dw = ", dw);
                                if (dl < dw) {
                                    edge = getEdgeId(l,w,dst,seg); // l is smaller, search w in adjacency list of l
                                } else {
                                    edge = getEdgeId(w,l,dst,seg); // w is smaller, search l in adjacency list of w
                                }
                                if (edge != -1) {
                                    var uedge = src[edge];
                                    var vedge = dst[edge];
                                    var uj = src[j];
                                    var vj = dst[j];
                                    writeln("i  = ", i, " j = ", j, " edge = ", edge);
                                    if uedge < vedge && uj < vj {
                                        if edgesDeleted[edge] <= -1 {
                                            if edgesDeleted[j] == -1 && edgesDeleted[edge] == -1 {
                                                triCount[edge].sub(1);
                                                triCount[j].sub(1);
                                                writeln("Deleting triangle case 1 for ", src[edge], "-", dst[edge]);
                                                writeln("Deleting triangle case 1 for ", src[j], "-", dst[j]);
                                            } else {
                                                if edgesDeleted[j] == -1 {
                                                    triCount[j].sub(1);
                                                    writeln("Deleting triangle case 2 for ", src[j], "-", dst[j]);
                                                }
                                                if edgesDeleted[edge] == -1 {
                                                    triCount[edge].sub(1);
                                                    writeln("Deleting triangle case 3 for ", src[edge], "-", dst[edge]);
                                                }
                                            }
                                        }
                                    }
                                    writeln();
                                }
                            }
                        }
                    }
                    writeln();
                }
            }
            writeln();
            writeln();
            writeln();

            forall i in removedEdges do edgesDeleted[i] = 1-k;
            removedEdges.clear();

            // Ensure that regular and reversed edges have the same triangle counts and are 
            // both properly removed.
            // NOTE: This loops over the whole edge set again, may be able to be done within the
            //       triangle counting above.
            forall (u, v, i) in zip(src, dst, src.domain) {
                if u < v {
                    var u2vTris = triCount[i].read();
                    var j = getEdgeId(v,u,dst,seg);
                    var v2uTris = triCount[j].read();

                    if u2vTris <= v2uTris then triCount[j].write(triCount[i].read());
                    else triCount[i].write(triCount[j].read());
                }
            }

            // Mark the edges that did not meet the k-2 requirement, with 1-k.
            forall i in triCount.domain with (ref removedEdges) {
                if edgesDeleted[i] == -1 then if triCount[i].read() < k-2 {edgesDeleted[i] = 1-k; removedEdges.add(i);}
            }

            write("src = "); writeArray(src);
            write("dst = "); writeArray(dst);
            write("tri = "); writeAtomicArray(triCount);
            write("del = "); writeArray(edgesDeleted);
            writeln("rem = ", removedEdges);
            writeln();
            iteration += 1;
        }

        var edgesKept = makeDistArray(src.domain, bool);
        forall i in edgesKept.domain do edgesKept[i] = if edgesDeleted[i] == -1 then true else false;
        return edgesKept;
    }

    proc truss_decomposition(graph, containedEdges) {
        writeln("n\n\n\n\nHello 2!n\n\n\n\n");
    }

    proc max_truss(graph, containedEdges) {
        writeln("n\n\n\n\nHello 3!n\n\n\n\n");
    }

} // end of Truss module
