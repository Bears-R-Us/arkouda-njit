module BFSMsg {
    // Arkouda Modules:
    use Logging;
    use Message;
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    
    // Chapel Modules:
    use Reflection;
    use DistributedBag;
    use Time;
    use ReplicatedVar;
    use GraphArray;
    use GraphMsg;
    use CopyAggregation;
    use AggregationPrimitives;

    // Oliver-Made Modules:
    use Utils; 

    // private config const logLevel = ServerConfig.logLevel;
    private config const logLevel = LogLevel.DEBUG;
    const smLogger = new Logger(logLevel);
  
    config const start_min_degree = 1000000;
    var tmpmindegree = start_min_degree;

    private proc xlocal(x : int, low : int, high : int) : bool {
        return low <= x && x <= high;
    }

    private proc xremote(x : int, low : int, high : int) : bool {
        return !xlocal(x, low, high);
    }

    // visit a graph using BFS method
    proc segBFSMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
        var repMsg : string;
        var (RCMs, n_verticesN, n_edgesN, directedN, weightedN, graphEntryName, restpart) = payload.splitMsgToTuple(7);
        var Nv = n_verticesN : int;
        var Ne = n_edgesN : int;
        var Directed = directedN : int;
        var Weighted = weightedN : int;
        var depthName : string;
        var RCMFlag = RCMs : int;
        var timer : Timer;

        // timer.start();
        // var depth=makeDistArray(Nv,int);
        // coforall loc in Locales  {
        //   on loc {
        //     forall i in depth.localSubdomain() {
        //       depth[i]=-1;
        //     }       
        //   }
        // }
        // timer.stop();
        // var outMsg = "Time elapsed for depth array initialization: " + timer.elapsed():string;
        // smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        var root : int;
        var srcN, dstN, startN, neighbourN,vweightN,eweightN, rootN : string;
        var srcRN, dstRN, startRN, neighbourRN : string;
        var gEntry : borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
        var ag = gEntry.graph;

        // Maintain on each locale the lows and highs of the src and srcR arrays.
        var block_locale_D : domain(1) dmapped Block(boundingBox=LocaleSpace) = LocaleSpace;
        var lows : [block_locale_D] int;
        var highs : [block_locale_D] int;
        var lowsR : [block_locale_D] int;
        var highsR : [block_locale_D] int;

        // Create arrays on each locale 
        var nei_local_vertices : [block_locale_D] RagArray;
        var neiR_local_vertices : [block_locale_D] RagArray;
        var start_i_local_vertices : [block_locale_D] RagArray;
        var start_iR_local_vertices : [block_locale_D] RagArray;

        // Copies of arrays to work with. 
        var nei1 = toSymEntry(ag.getNEIGHBOR(), int).a;
        var start_i1 = toSymEntry(ag.getSTART_IDX(), int).a;
        var src1 = toSymEntry(ag.getSRC(), int).a;
        var dst1 = toSymEntry(ag.getDST(), int).a;
        var neiR1 = toSymEntry(ag.getNEIGHBOR_R(), int).a;
        var start_iR1 = toSymEntry(ag.getSTART_IDX_R(), int).a;
        var srcR1 = toSymEntry(ag.getSRC_R(), int).a;
        var dstR1 = toSymEntry(ag.getDST_R(), int).a;

        // Replicated domain variables of one dimension that will be updated to the
        // proper size. 
        var D : [rcDomain] domain(1);
        var DR : [rcDomain] domain(1);
    
        // Generate the low and high vertex values from the src and srcR arrays.
        coforall loc in Locales with (ref D, ref DR) {
            on loc {
                lows[loc.id] = src1[src1.localSubdomain().lowBound];
                highs[loc.id] = src1[src1.localSubdomain().highBound];

                lowsR[loc.id] = srcR1[srcR1.localSubdomain().lowBound];
                highsR[loc.id] = srcR1[srcR1.localSubdomain().highBound];

                D[1] = {lows[loc.id]..highs[loc.id]};
                DR[1] = {lowsR[loc.id]..highsR[loc.id]};

                nei_local_vertices[loc.id].new_dom(D[1]);
                neiR_local_vertices[loc.id].new_dom(DR[1]);

                start_i_local_vertices[loc.id].new_dom(D[1]);
                start_iR_local_vertices[loc.id].new_dom(DR[1]);
            }
        }

        // Populate the "local" arrays with the values from the nei, neiR, start_i, and start_iR arrays.
        coforall loc in Locales {
            on loc {
                forall i in nei_local_vertices[loc.id].DO {
                    nei_local_vertices[loc.id].A[i] = nei1[i];
                }
                forall i in neiR_local_vertices[loc.id].DO {
                    neiR_local_vertices[loc.id].A[i] = neiR1[i];
                }
                forall i in start_i_local_vertices[loc.id].DO {
                    start_i_local_vertices[loc.id].A[i] = start_i1[i];
                }
                forall i in start_iR_local_vertices[loc.id].DO {
                    start_iR_local_vertices[loc.id].A[i] = start_iR1[i];
                }
            }
        }

        // Check the range on each locale. Ensure the proper values were read from nei, neiR, start_i, 
        // and start_iR arrays.
        // writeln("$$$$$ Check the range on each locale: ");
        // for loc in Locales {
        //     on loc {
        //         writeln("ON LOC ", loc.id, ":");
        //         writeln("lows..highs = ", lows[loc.id], "..", highs[loc.id]);
        //         writeln("lowsR..highsR = ", lowsR[loc.id], "..", highsR[loc.id]);
        //         writeln("nei_local_vertices[", loc.id, "] = ", nei_local_vertices[loc.id]);
        //         writeln("neiR_local_vertices[", loc.id, "] = ", neiR_local_vertices[loc.id]);
        //         writeln("start_i_local_vertices[", loc.id, "] = ", start_i_local_vertices[loc.id]);
        //         writeln("start_iR_local_vertices[", loc.id, "] = ", start_iR_local_vertices[loc.id]);
        //         writeln();
        //     }
        // }
        // writeln();

        proc fo_bag_bfs_kernel_u( nei : [?D1] int, start_i : [?D2] int, src : [?D3] int, dst : [?D4] int, 
                                  neiR : [?D11] int, start_iR : [?D12] int, srcR : [?D13] int, dstR : [?D14] int, 
                                  LF : int, GivenRatio : real) throws {
      
            // Initialize distributed depth array.
            var depth = makeDistArray(Nv, int);
            coforall loc in Locales  {
                on loc {
                    forall i in depth.localSubdomain() {
                        depth[i] = -1;
                    }       
                }
            }
      
            var cur_level = 0;
            var SetCurF = new DistBag(int, Locales); // use bag to keep the current frontier
            var SetNextF = new DistBag(int, Locales); // use bag to keep the next frontier
            SetCurF.add(root);
            var numCurF = 1 : int;
            var topdown = 0 : int;
            var bottomup = 0 : int;
            depth[root] = 0;
            while (numCurF > 0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                    on loc {
                        ref srcf = src;
                        ref df = dst;
                        ref nf = nei;
                        ref sf = start_i;

                        ref srcfR = srcR;
                        ref dfR = dstR;
                        ref nfR = neiR;
                        ref sfR = start_iR;

                        var edgeBegin = src.localSubdomain().low;
                        var edgeEnd = src.localSubdomain().high;
                        var vertexBegin = src[edgeBegin];
                        var vertexEnd = src[edgeEnd];
                        var vertexBeginR = srcR[edgeBegin];
                        var vertexEndR = srcR[edgeEnd];

                        var switchratio = (numCurF : real) / nf.size : real;
                        if (switchratio < GivenRatio) {//top down
                            topdown += 1;
                            forall i in SetCurF with (ref SetNextF) {
                                if((xlocal(i, vertexBegin, vertexEnd)) || (LF == 0)) { // current edge has the vertex
                                    var numNF = nf[i];
                                    var edgeId = sf[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                    ref NF = df[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF){
                                        if (depth[j] == -1) {
                                            depth[j] = cur_level + 1;
                                            SetNextF.add(j);
                                        }
                                    }
                                } 
                                if ((xlocal(i, vertexBeginR, vertexEndR)) || (LF == 0)) {
                                    var numNF = nfR[i];
                                    var edgeId = sfR[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                    ref NF = dfR[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF)  {
                                        if (depth[j] == -1) {
                                            depth[j] = cur_level+1;
                                            SetNextF.add(j);
                                        }
                                    }
                                }
                            } //end forall
                        } else { // bottom up
                            bottomup+=1;
                            forall i in vertexBegin..vertexEnd with (ref SetNextF) {
                                if (depth[i] == -1) {
                                    var numNF = nf[i];
                                    var edgeId = sf[i];
                                    var nextStart = max(edgeId,edgeBegin);
                                    var nextEnd = min(edgeEnd,edgeId+numNF-1);
                                    ref NF = df[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF){
                                        if (SetCurF.contains(j)) {
                                            depth[i] = cur_level+1;
                                            SetNextF.add(i);
                                        }
                                    }
                                 }
                            }
                            forall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                                if (depth[i] == -1) {
                                    var numNF = nfR[i];
                                    var edgeId = sfR[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId+numNF - 1);
                                    ref NF = dfR[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF)  {
                                        if (SetCurF.contains(j)) {
                                            depth[i] = cur_level+1;
                                            SetNextF.add(i);
                                        }
                                    }
                                }
                            }
                        }
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                numCurF = SetNextF.getSize();
                SetCurF <=> SetNextF;
                SetNextF.clear();
            }// end while  
            // var outMsg = "Search Radius = " + (cur_level + 1) : string;
            // smLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
            // outMsg = "number of top down = " + (topdown:string) + " number of bottom up = " + (bottomup:string);
            // smLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
            // return "success";
            return depth;
        }// end of fo_bag_bfs_kernel_u

        proc fo_bag_bfs_kernel( nei : [?D1] int, start_i : [?D2] int, src : [?D3] int, dst : [?D4] int,
                                LF : int, GivenRatio : real) throws {
      
            var depth = makeDistArray(Nv,int);
            coforall loc in Locales {
                on loc {
                    forall i in depth.localSubdomain() {
                        depth[i] = -1;
                    }
                }
            }
      
            var cur_level = 0;
            var SetCurF = new DistBag(int, Locales); // use bag to keep the current frontier
            var SetNextF = new DistBag(int, Locales); // use bag to keep the next frontier
            SetCurF.add(root);
            var numCurF = 1 : int;
            var topdown = 0 : int;
            var bottomup = 0 : int;

            while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF, + reduce topdown, + reduce bottomup) {
                    on loc {
                        ref srcf=src;
                        ref df=dst;
                        ref nf=nei;
                        ref sf=start_i;

                        var edgeBegin = src.localSubdomain().low;
                        var edgeEnd = src.localSubdomain().high;
                        var vertexBegin = src[edgeBegin];
                        var vertexEnd = src[edgeEnd];

                        var switchratio = (numCurF : real) / nf.size : real;
                        if (switchratio < GivenRatio) { // top down
                            topdown += 1;
                            forall i in SetCurF with (ref SetNextF) {
                                if ((xlocal(i, vertexBegin, vertexEnd)) || (LF == 0)) { // current edge has the vertex
                                    var numNF = nf[i];
                                    var edgeId = sf[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                    ref NF = df[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF) {
                                        if (depth[j] == -1) {
                                            depth[j] = cur_level + 1;
                                            SetNextF.add(j);
                                        }
                                    }
                                } 
                            } // end forall
                        } else { // bottom up
                            bottomup += 1;
                            forall i in vertexBegin..vertexEnd with (ref SetNextF) {
                                if depth[i] == -1 {
                                    var numNF = nf[i];
                                    var edgeId = sf[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                    ref NF = df[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF){
                                        if (SetCurF.contains(j)) {
                                            depth[i] = cur_level + 1;
                                            SetNextF.add(i);
                                        }
                                    }
                                }
                            }
                        }
                    } // end on loc
                } // end coforall loc
                cur_level += 1;
                numCurF = SetNextF.getSize();
                SetCurF <=> SetNextF;
                SetNextF.clear();
            }//end while  
            // var outMsg="Search Radius = "+ (cur_level+1):string;
            // smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            // outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
            // smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            return depth;
        }//end of fo_bag_bfs_kernel

        proc bfs_kernel_u( nei : [?D1] int, start_i : [?D2] int, src : [?D3] int, dst : [?D4] int,
                           neiR : [?D11] int, start_iR : [?D12] int, srcR : [?D13] int, 
                           dstR : [?D14] int) throws {
      
            // Initialize depth array.
            var depth = makeDistArray(Nv, int);
            coforall loc in Locales  {
                on loc {
                    forall i in depth.localSubdomain() {
                        depth[i] = -1;
                    }       
                }
            }
      
            // Needed variables for metrics.
            var num_visits = 0;
            var total_comm_time = 0.0;

            // The current and next frontiers for each locale. The frontiers hold the
            // vertex to process and its parent (i.e., the vertex who added it to the frontier
            // from the previous level).
            // var block_locale_D : domain(1) dmapped Block(boundingBox = LocaleSpace) = LocaleSpace;
            var comm_timers : [block_locale_D] Timer;

            var curr_frontiers : [block_locale_D] domain(int);
            var next_frontiers : [block_locale_D] domain(int);

            // Create global array to track the low subdomain of each locale so we know what locale
            // we must write the next frontier to. 
            var D_sbdmn = {0..numLocales-1} dmapped Replicated();
            var ranges : [D_sbdmn] int;
            var rangesR : [D_sbdmn] int;

            // Write the local subdomain low value to the sizes array.
            coforall loc in Locales {
                on loc {
                    var lowVertex = src[src.localSubdomain().low];
                    var lowVertexR = srcR[srcR.localSubdomain().low];

                    coforall rloc in Locales { 
                        on rloc {
                            ranges[loc.id] = lowVertex;
                            rangesR[loc.id] = lowVertexR;
                        }
                    }
                }
            }

            // Check that the above values were written correctly.
            // writeln("The range of the edges on the locales:");
            // writeln("ranges: ", ranges);
            // writeln("rangesR: ", rangesR);
            // writeln();

            // First, add root to curr_frontiers where root is located.
            for i in 1..numLocales - 1 {
                if (root >= ranges[i-1] && root < ranges[i]) {
                    curr_frontiers[i-1] += root;
                }
                if (i == numLocales - 1) {
                    if root >= ranges[i] {
                        curr_frontiers[i] += root;
                    }
                }
            }
            for i in 1..numLocales - 1 {
                if (root >= rangesR[i - 1] && root < rangesR[i]) {
                    curr_frontiers[i - 1] += root;
                }
                if (i == numLocales - 1) {
                    if root >= rangesR[i] {
                        curr_frontiers[i] += root;
                    }
                }
            }

            // Check to see what our frontiers look like.
            // writeln("The frontiers with only the root added in:");
            // writeln("curr_frontiers: ", curr_frontiers);
            // writeln("next_frontiers: ", next_frontiers);
            // writeln();

            // Start the BFS steps. 
            var cur_level = 0; 
            while true {
                // writeln("$$$$$ ITERATION ", cur_level, " $$$$$");
                // writeln("curr_frontiers = ", curr_frontiers);
                var pending_work : bool;
                coforall loc in Locales with (|| reduce pending_work, + reduce num_visits) {
                    on loc {
                        var curr_f = curr_frontiers[loc.id];
                        var edge_begin = src.localSubdomain().low;
                        var edge_end = src.localSubdomain().high;

                        forall u in curr_f with (|| reduce pending_work, + reduce num_visits) {
                            if depth[u] == -1 {
                                // Update depth and other variables.
                                depth[u] = cur_level;
                                pending_work = true;
                                num_visits += 1;
                
                                // Get neighbors from src and dst arrays.
                                var num_neighbors = nei[u];
                                var edge_id = start_i[u];
                                var next_start = max(edge_id, edge_begin);
                                var next_end = min(edge_end, edge_id + num_neighbors - 1);
                                var neighbors = dst[next_start..next_end];
                                // writeln("neighbors = ", neighbors);

                                // Get neighbors from srcR and dstR arrays.
                                var num_neighborsR = neiR[u];
                                var edge_idR = start_iR[u];
                                var next_startR = max(edge_idR, edge_begin);
                                var next_endR = min(edge_end, edge_idR + num_neighborsR - 1);
                                var neighborsR = dstR[next_startR..next_endR];
                                // writeln("neighborsR = ", neighborsR);

                                // Add neighbors from src and dst to the proper next_frontiers associative domain.
                                for n in neighbors {
                                    if depth[n] == -1 {
                                        for i in 1..numLocales - 1 {
                                            if (n >= ranges[i - 1] && n < ranges[i]) {
                                                next_frontiers[i - 1] += n;
                                            }
                                            if (i == numLocales -  1) {
                                                if n >= ranges[i] {
                                                    next_frontiers[i] += n;
                                                }
                                            }
                                        }
                                        for i in 1..numLocales - 1 {
                                            if (n >= rangesR[i - 1] && n < rangesR[i]) {
                                                next_frontiers[i - 1] += n;
                                            }
                                            if (i == numLocales - 1) {
                                                if n >= rangesR[i] {
                                                    next_frontiers[i] += n;
                                                }
                                            }
                                        }
                                    }
                                }

                                // Add neighbors from srcR and dstR to the proper next_frontiers associative domain.
                                forall nR in neighborsR {
                                    if depth[nR] == -1 {
                                        for i in 1..numLocales - 1 {
                                            if (nR >= ranges[i - 1] && nR < ranges[i]) {
                                                next_frontiers[i - 1] += nR;
                                            }
                                            if (i == numLocales-1) {
                                                if nR >= ranges[i] {
                                                    next_frontiers[i] += nR;
                                                }
                                            }
                                        }
                                        for i in 1..numLocales - 1 {
                                            if (nR >= rangesR[i - 1] && nR < rangesR[i]) {
                                                next_frontiers[i - 1] += nR;
                                            }
                                            if (i == numLocales - 1) {
                                                if nR >= rangesR[i] {
                                                    next_frontiers[i] += nR;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } /* end of forall u */
                    } /* end of on loc */
                } /* end of coforall loc in Locales */

                // Size of the frontiers.
                var size = 0;
                for curr in next_frontiers {
                    size += curr.size;
                }

                // writeln("next_frontiers = ", next_frontiers);

                // Break out if no pending work.
                if !pending_work {
                    break;
                }

                // Swap each locale's frontiers.
                coforall (curr_f, next_f) in zip(curr_frontiers, next_frontiers) do on curr_f {
                    curr_f <=> next_f;
                    next_f.clear();
                }
                cur_level += 1;
                // writeln();
            } /* end of while true */

            return depth;
        }//end of bfs_kernel_u

        proc fo_bag_bfs_kernel_u_local_vertices( nei : [?D1] RagArray, start_i : [?D2] RagArray, src : [?D3] int, dst : [?D4] int, 
                                                 neiR : [?D11] RagArray, start_iR : [?D12] RagArray, srcR : [?D13] int, dstR : [?D14] int, 
                                                 LF : int, GivenRatio : real) throws {
      
            // Initialize distributed depth array.
            var depth = makeDistArray(Nv, int);
            coforall loc in Locales  {
                on loc {
                    forall i in depth.localSubdomain() {
                        depth[i] = -1;
                    }       
                }
            }
      
            var cur_level = 0;
            var SetCurF = new DistBag(int, Locales); // use bag to keep the current frontier
            var SetNextF = new DistBag(int, Locales); // use bag to keep the next frontier
            SetCurF.add(root);
            var numCurF = 1 : int;
            var topdown = 0 : int;
            var bottomup = 0 : int;
            depth[root] = 0;
            while (numCurF > 0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                    on loc {
                        ref srcf = src;
                        ref df = dst;
                        ref nf = nei;
                        ref sf = start_i;

                        ref srcfR = srcR;
                        ref dfR = dstR;
                        ref nfR = neiR;
                        ref sfR = start_iR;

                        var edgeBegin = src.localSubdomain().low;
                        var edgeEnd = src.localSubdomain().high;
                        var vertexBegin = src[edgeBegin];
                        var vertexEnd = src[edgeEnd];
                        var vertexBeginR = srcR[edgeBegin];
                        var vertexEndR = srcR[edgeEnd];

                        // serial {
                        //     writeln("On loc ", loc.id, " vertexBegin = ", vertexBegin);
                        //     writeln("On loc ", loc.id, " vertexEnd = ", vertexEnd);
                        //     writeln("On loc ", loc.id, " vertexBeginR = ", vertexBeginR);
                        //     writeln("On loc ", loc.id, " vertexEndR = ", vertexEndR);


                        //     writeln("On loc ", loc.id, " neiBegin = ", nei1.localSubdomain().low);
                        //     writeln("On loc ", loc.id, " neiEnd = ", nei1.localSubdomain().high);
                        //     writeln("On loc ", loc.id, " neiBeginR = ", neiR1.localSubdomain().low);
                        //     writeln("On loc ", loc.id, " neiEndR = ", neiR1.localSubdomain().high);
                        // }

                        var switchratio = (numCurF : real) / nf[loc.id].size() : real;
                        if (switchratio < GivenRatio) {//top down
                            topdown += 1;
                            forall i in SetCurF with (ref SetNextF) {
                                if((xlocal(i, vertexBegin, vertexEnd)) || (LF == 0)) { // current edge has the vertex
                                    var numNF = nf[loc.id].A[i];
                                    var edgeId = sf[loc.id].A[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                    ref NF = df[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF){
                                        if (depth[j] == -1) {
                                            depth[j] = cur_level + 1;
                                            SetNextF.add(j);
                                        }
                                    }
                                } 
                                if ((xlocal(i, vertexBeginR, vertexEndR)) || (LF == 0)) {
                                    var numNF = nfR[loc.id].A[i];
                                    var edgeId = sfR[loc.id].A[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                                    ref NF = dfR[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF)  {
                                        if (depth[j] == -1) {
                                            depth[j] = cur_level+1;
                                            SetNextF.add(j);
                                        }
                                    }
                                }
                            } //end forall
                        } else { // bottom up
                            bottomup+=1;
                            forall i in vertexBegin..vertexEnd with (ref SetNextF) {
                                if (depth[i] == -1) {
                                    var numNF = nf[loc.id].A[i];
                                    var edgeId = sf[loc.id].A[i];
                                    var nextStart = max(edgeId,edgeBegin);
                                    var nextEnd = min(edgeEnd,edgeId+numNF-1);
                                    ref NF = df[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF){
                                        if (SetCurF.contains(j)) {
                                            depth[i] = cur_level+1;
                                            SetNextF.add(i);
                                        }
                                    }
                                 }
                            }
                            forall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                                if (depth[i] == -1) {
                                    var numNF = nfR[loc.id].A[i];
                                    var edgeId = sfR[loc.id].A[i];
                                    var nextStart = max(edgeId, edgeBegin);
                                    var nextEnd = min(edgeEnd, edgeId+numNF - 1);
                                    ref NF = dfR[nextStart..nextEnd];
                                    forall j in NF with (ref SetNextF)  {
                                        if (SetCurF.contains(j)) {
                                            depth[i] = cur_level+1;
                                            SetNextF.add(i);
                                        }
                                    }
                                }
                            }
                        }
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                numCurF = SetNextF.getSize();
                SetCurF <=> SetNextF;
                SetNextF.clear();
            }// end while  
            // var outMsg = "Search Radius = " + (cur_level + 1) : string;
            // smLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
            // outMsg = "number of top down = " + (topdown:string) + " number of bottom up = " + (bottomup:string);
            // smLogger.debug(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
            // return "success";
            return depth;
        }// end of fo_bag_bfs_kernel_u_local_vertices

        proc bfs_kernel_u_local_vertices( nei : [?D1] RagArray, start_i : [?D2] RagArray, src : [?D3] int, dst : [?D4] int,
                                          neiR : [?D11] RagArray, start_iR : [?D12] RagArray, srcR : [?D13] int, 
                                          dstR : [?D14] int) throws {
      
            // Initialize depth array.
            var depth = makeDistArray(Nv, int);
            coforall loc in Locales  {
                on loc {
                    forall i in depth.localSubdomain() {
                        depth[i] = -1;
                    }       
                }
            }
      
            // Needed variables for metrics.
            var num_visits = 0;
            var total_comm_time = 0.0;

            // The current and next frontiers for each locale. The frontiers hold the
            // vertex to process and its parent (i.e., the vertex who added it to the frontier
            // from the previous level).
            var block_locale_D : domain(1) dmapped Block(boundingBox = LocaleSpace) = LocaleSpace;
            var comm_timers : [block_locale_D] Timer;

            var curr_frontiers : [block_locale_D] domain(int);
            var next_frontiers : [block_locale_D] domain(int);

            // Create global array to track the low subdomain of each locale so we know what locale
            // we must write the next frontier to. 
            var D_sbdmn = {0..numLocales-1} dmapped Replicated();
            var ranges : [D_sbdmn] int;
            var rangesR : [D_sbdmn] int;

            // Write the local subdomain low value to the sizes array.
            coforall loc in Locales {
                on loc {
                    var lowVertex = src[src.localSubdomain().low];
                    var lowVertexR = srcR[srcR.localSubdomain().low];

                    coforall rloc in Locales { 
                        on rloc {
                            ranges[loc.id] = lowVertex;
                            rangesR[loc.id] = lowVertexR;
                        }
                    }
                }
            }

            // Check that the above values were written correctly.
            // writeln("The range of the edges on the locales:");
            // writeln("ranges: ", ranges);
            // writeln("rangesR: ", rangesR);
            // writeln();

            // First, add root to curr_f where root is located.
            for i in 1..numLocales - 1 {
                if (root >= ranges[i-1] && root < ranges[i]) {
                    curr_frontiers[i-1] += root;
                }
                if (i == numLocales - 1) {
                    if root >= ranges[i] {
                        curr_frontiers[i] += root;
                    }
                }
            }
            for i in 1..numLocales - 1 {
                if (root >= rangesR[i - 1] && root < rangesR[i]) {
                    curr_frontiers[i - 1] += root;
                }
                if (i == numLocales - 1) {
                    if root >= rangesR[i] {
                        curr_frontiers[i] += root;
                    }
                }
            }

            // Check to see what our frontiers look like.
            // writeln("The frontiers with only the root added in:");
            // writeln("curr_frontiers: ", curr_frontiers);
            // writeln("next_frontiers: ", next_frontiers);
            // writeln();

            // Start the BFS steps. 
            var cur_level = 0; 
            while true {
                // writeln("$$$$$ ITERATION ", cur_level, " $$$$$");
                // writeln("curr_frontiers = ", curr_frontiers);
                var pending_work : bool;
                coforall loc in Locales with (|| reduce pending_work, + reduce num_visits) {
                    on loc {
                    //coforall curr_f in curr_frontiers with (|| reduce pending_work, + reduce num_visits) do on curr_f {
                        var curr_f = curr_frontiers[loc.id];
                        var edge_begin = src.localSubdomain().low;
                        var edge_end = src.localSubdomain().high;

                        forall u in curr_f with (|| reduce pending_work, + reduce num_visits) {
                            if depth[u] == -1 {
                                // Update depth and other variables.
                                depth[u] = cur_level;
                                pending_work = true;
                                num_visits += 1;
                
                                // Get neighbors from src and dst arrays.
                                var num_neighbors = nei[loc.id].A[u];
                                var edge_id = start_i[loc.id].A[u];
                                var next_start = max(edge_id, edge_begin);
                                var next_end = min(edge_end, edge_id + num_neighbors - 1);
                                var neighbors = dst[next_start..next_end];
                                // writeln("neighbors = ", neighbors);

                                // Get neighbors from srcR and dstR arrays.
                                var num_neighborsR = neiR[loc.id].A[u];
                                var edge_idR = start_iR[loc.id].A[u];
                                var next_startR = max(edge_idR, edge_begin);
                                var next_endR = min(edge_end, edge_idR + num_neighborsR - 1);
                                var neighborsR = dstR[next_startR..next_endR];
                                // writeln("neighborsR = ", neighborsR);

                                // Add neighbors from src and dst to the proper next_frontiers associative domain.
                                for n in neighbors {
                                    if depth[n] == -1 {
                                        for i in 1..numLocales - 1 {
                                            if (n >= ranges[i - 1] && n < ranges[i]) {
                                                next_frontiers[i - 1] += n;
                                            }
                                            if (i == numLocales -  1) {
                                                if n >= ranges[i] {
                                                    next_frontiers[i] += n;
                                                }
                                            }
                                        }
                                        for i in 1..numLocales - 1 {
                                            if (n >= rangesR[i - 1] && n < rangesR[i]) {
                                                next_frontiers[i - 1] += n;
                                            }
                                            if (i == numLocales - 1) {
                                                if n >= rangesR[i] {
                                                    next_frontiers[i] += n;
                                                }
                                            }
                                        }
                                    }
                                }

                                // Add neighbors from srcR and dstR to the proper next_frontiers associative domain.
                                forall nR in neighborsR {
                                    if depth[nR] == -1 {
                                        for i in 1..numLocales - 1 {
                                            if (nR >= ranges[i - 1] && nR < ranges[i]) {
                                                next_frontiers[i - 1] += nR;
                                            }
                                            if (i == numLocales-1) {
                                                if nR >= ranges[i] {
                                                    next_frontiers[i] += nR;
                                                }
                                            }
                                        }
                                        for i in 1..numLocales - 1 {
                                            if (nR >= rangesR[i - 1] && nR < rangesR[i]) {
                                                next_frontiers[i - 1] += nR;
                                            }
                                            if (i == numLocales - 1) {
                                                if nR >= rangesR[i] {
                                                    next_frontiers[i] += nR;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } /* end of forall u */
                    } /* end of on loc */
                } /* end of coforall */

                // Size of the frontiers.
                var size = 0;
                for curr in next_frontiers {
                    size += curr.size;
                }

                // writeln("next_frontiers = ", next_frontiers);

                // Break out if no pending work.
                if !pending_work {
                    break;
                }

                // Swap each locale's frontiers.
                coforall (curr_f, next_f) in zip(curr_frontiers, next_frontiers) do on curr_f {
                    curr_f <=> next_f;
                    next_f.clear();
                }
                cur_level += 1;
                // writeln();
            } /* end of while true */

            return depth;
        }//end of bfs_kernel_u_local_vertices

        proc return_depth(depth): string throws{
            var depthName = st.nextName();
            var depthEntry = new shared SymEntry(depth);
            st.addEntry(depthName, depthEntry);

            var depMsg = 'created ' + st.attrib(depthName);
            return depMsg;
        }

        var overarchingTimer:Timer;

        // Directed graphs. 
        if (Directed != 0) {
            // Weighted graphs.
            if (Weighted != 0) {
                var ratios : string;
                (rootN, ratios) = restpart.splitMsgToTuple(2);
                root = rootN : int;
                var GivenRatio = ratios:real;
                if (RCMFlag > 0) {
                    root = 0;
                }
                // depth[root] = 0;
                var depth = fo_bag_bfs_kernel (
                    toSymEntry(ag.getNEIGHBOR(), int).a,
                    toSymEntry(ag.getSTART_IDX(), int).a,
                    toSymEntry(ag.getSRC(), int).a,
                    toSymEntry(ag.getDST(), int).a,
                    1, GivenRatio
                );
                repMsg=return_depth(depth);
            // Unweighted graphs.
            } else {
                var ratios : string;
                (rootN, ratios) = restpart.splitMsgToTuple(2);
                root = rootN : int;
                var GivenRatio = ratios : real;
                if (RCMFlag>0) {
                    root = 0;
                }
                // depth[root] = 0;
                var depth = fo_bag_bfs_kernel (
                    toSymEntry(ag.getNEIGHBOR(), int).a,
                    toSymEntry(ag.getSTART_IDX(), int).a,
                    toSymEntry(ag.getSRC(), int).a,
                    toSymEntry(ag.getDST(), int).a,
                    1, GivenRatio
                );
                repMsg=return_depth(depth);
            }
        // Undirected graphs.
        } else {
            // Weighted graphs.
            if (Weighted != 0) {
                var ratios : string;
                (rootN, ratios) = restpart.splitMsgToTuple(2);
                root = rootN : int;
                if (RCMFlag>0) {
                    root = 0;
                }
                //depth = -1;
                //depth[root] = 0;
                var Flag = 0 : int;
                var GivenRatio = ratios : real;
                if (GivenRatio < 0) { //do default call
                    GivenRatio = -1.0 * GivenRatio;
                    var depth = fo_bag_bfs_kernel_u(
                        toSymEntry(ag.getNEIGHBOR(), int).a,
                        toSymEntry(ag.getSTART_IDX(), int).a,
                        toSymEntry(ag.getSRC(), int).a,
                        toSymEntry(ag.getDST(), int).a,
                        toSymEntry(ag.getNEIGHBOR_R(), int).a,
                        toSymEntry(ag.getSTART_IDX_R(), int).a,
                        toSymEntry(ag.getSRC_R(), int).a,
                        toSymEntry(ag.getDST_R(), int).a,
                        1, GivenRatio
                    );
                    repMsg = return_depth(depth);
                // Ratio greater than or equal to 0. 
                } else { // do batch test
                    // depth = -1;
                    // depth[root] = 0;
                    var depth = fo_bag_bfs_kernel_u(
                        toSymEntry(ag.getNEIGHBOR(), int).a,
                        toSymEntry(ag.getSTART_IDX(), int).a,
                        toSymEntry(ag.getSRC(), int).a,
                        toSymEntry(ag.getDST(), int).a,
                        toSymEntry(ag.getNEIGHBOR_R(), int).a,
                        toSymEntry(ag.getSTART_IDX_R(), int).a,
                        toSymEntry(ag.getSRC_R(), int).a,
                        toSymEntry(ag.getDST_R(), int).a,
                        1, GivenRatio
                    );
                    repMsg = return_depth(depth);
                } // end of batch test
            // Unweighted graphs.
            } else {
                var ratios : string;
                (rootN, ratios) = restpart.splitMsgToTuple(2);
                root = rootN : int;
                if (RCMFlag>0) {
                    root = 0;
                }
                //depth = -1;
                //depth[root] = 0;
                var Flag = 0 : int;
                var GivenRatio = ratios : real;
                if (GivenRatio < 0 ) { // do default call
                    GivenRatio = -1.0 * GivenRatio;
                    var depth = fo_bag_bfs_kernel_u(
                        toSymEntry(ag.getNEIGHBOR(), int).a,
                        toSymEntry(ag.getSTART_IDX(), int).a,
                        toSymEntry(ag.getSRC(), int).a,
                        toSymEntry(ag.getDST(), int).a,
                        toSymEntry(ag.getNEIGHBOR_R(), int).a,
                        toSymEntry(ag.getSTART_IDX_R(), int).a,
                        toSymEntry(ag.getSRC_R(), int).a,
                        toSymEntry(ag.getDST_R(), int).a,
                        1, GivenRatio
                    );
                    repMsg=return_depth(depth);
                // Ratio greater than or equal to 0. 
                } else { // do batch test
                    overarchingTimer.start(); 
                    var depth = fo_bag_bfs_kernel_u(
                        toSymEntry(ag.getNEIGHBOR(), int).a,
                        toSymEntry(ag.getSTART_IDX(), int).a,
                        toSymEntry(ag.getSRC(), int).a,
                        toSymEntry(ag.getDST(), int).a,
                        toSymEntry(ag.getNEIGHBOR_R(), int).a,
                        toSymEntry(ag.getSTART_IDX_R(), int).a,
                        toSymEntry(ag.getSRC_R(), int).a,
                        toSymEntry(ag.getDST_R(), int).a,
                        1, GivenRatio
                    );
                    overarchingTimer.stop();
                    outMsg = "high-level BFS takes: " + overarchingTimer.elapsed():string + " secs";
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    overarchingTimer.clear();
                    overarchingTimer.start(); 
                    var depth1 = fo_bag_bfs_kernel_u_local_vertices(
                        nei_local_vertices,
                        start_i_local_vertices,
                        toSymEntry(ag.getSRC(), int).a,
                        toSymEntry(ag.getDST(), int).a,
                        neiR_local_vertices,
                        start_iR_local_vertices,
                        toSymEntry(ag.getSRC_R(), int).a,
                        toSymEntry(ag.getDST_R(), int).a,
                        1, GivenRatio
                    );
                    overarchingTimer.stop();
                    outMsg = "high-level BFS with local vertices takes: " + overarchingTimer.elapsed():string + " secs";
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          
                    overarchingTimer.clear();
                    overarchingTimer.start();
                    var depth2 = bfs_kernel_u(
                        toSymEntry(ag.getNEIGHBOR(), int).a,
                        toSymEntry(ag.getSTART_IDX(), int).a,
                        toSymEntry(ag.getSRC(), int).a,
                        toSymEntry(ag.getDST(), int).a,
                        toSymEntry(ag.getNEIGHBOR_R(), int).a,
                        toSymEntry(ag.getSTART_IDX_R(), int).a,
                        toSymEntry(ag.getSRC_R(), int).a,
                        toSymEntry(ag.getDST_R(), int).a
                    );
                    overarchingTimer.stop();
                    outMsg = "low-level BFS takes: " + overarchingTimer.elapsed():string + " secs";
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    overarchingTimer.clear();
                    overarchingTimer.start();
                    var depth3 = bfs_kernel_u_local_vertices(
                        nei_local_vertices,
                        start_i_local_vertices,
                        toSymEntry(ag.getSRC(), int).a,
                        toSymEntry(ag.getDST(), int).a,
                        neiR_local_vertices,
                        start_iR_local_vertices,
                        toSymEntry(ag.getSRC_R(), int).a,
                        toSymEntry(ag.getDST_R(), int).a
                    );
                    overarchingTimer.stop();
                    outMsg = "low-level BFS with local vertices takes: " + overarchingTimer.elapsed():string + " secs";
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    writeln("$$$$$ depths $$$$$");
                    writeln("depth  = ", depth);
                    writeln("depth1 = ", depth1);
                    writeln("depth2 = ", depth2);
                    writeln("depth3 = ", depth3);
                    
                    repMsg = return_depth(depth);
                }
            }
        }
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    } // end of SegBFSMsg

    use CommandMap;
    registerFunction("segmentedGraphBFS", segBFSMsg);
}
