module BFSMsg {
    // Chapel modules.
    use IO;
    use Reflection;
    use Set;
    use Time; 
    use Sort; 

    // Modules contributed to Chapel. 
    use DistributedBag; 
    
    // Arachne Modules.
    use GraphArray;
    use Utils;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use ArgSortMsg;
    use AryUtil;
    use Logging;
    use Message;
    
    // Server message logger. 
    private config const logLevel = LogLevel.DEBUG;
    const smLogger = new Logger(logLevel);
    var outMsg:string;

    /**
    * Check if a particular value x is local in an array. It is local if it is between or equal to 
    * the low and high values passed. 
    *
    * x: value we are searching for. 
    * low: lower value of subdomain. 
    * high: higher value of subdomain. 
    *
    * returns: true if local, false otherwise. 
    */
    private proc xlocal(x: int, low: int, high: int):bool {
        return low <= x && x <= high;
    }

    /**
    * Check if a particular value x is remote in an array. It is remote if it is not between or 
    * equal to the low and high values passed. 
    *
    * x: value we are searching for. 
    * low: lower value of subdomain. 
    * high: higher value of subdomain. 
    *
    * returns: true if remote, false otherwise. 
    */
    private proc xremote(x: int, low: int, high: int):bool {
        return !xlocal(x, low, high);
    }

    /**
    * Run BFS on a(n) (un)directed or (un)weighted graph. 
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc segBFSMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        var repMsg: string;
        var depthName:string;

        var n_verticesN = msgArgs.getValueOf("NumOfVertices");
        var n_edgesN = msgArgs.getValueOf("NumOfEdges");
        var directedN = msgArgs.getValueOf("Directed");
        var weightedN = msgArgs.getValueOf("Weighted");
        var graphEntryName = msgArgs.getValueOf("GraphName");

        var Nv = n_verticesN:int;
        var Ne = n_edgesN:int;
        var directed = directedN:int;
        var weighted = weightedN:int;
        var timer:stopwatch;

        var root:int; 
        var srcN, dstN, startN, neighborN, eweightN, rootN: string; 
        var srcRN, dstRN, startRN, neighborRN: string; 
        var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
        var ag = gEntry.graph; 

        timer.start();

        // Create empty depth array to return at the end of execution. 
        var depth = makeDistArray(Nv, int);
        coforall loc in Locales  {
            on loc {
                forall i in depth.localSubdomain() {
                    depth[i] = -1;
                }       
            }
        }

        /**
        * BFS kernel for undirected graphs. 
        *
        * nei: neighbor array
        * start_i: starting edge array location given vertex v
        * src: source array
        * dst: destination array
        * neiR: reversed neighbor array
        * start_iR: reversed starting edge array location given vertex v
        * srcR: reversed source array
        * dstR: reversed destination array
        *
        * returns: message back to Python.
        */
        proc fo_bag_bfs_kernel_und(nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, dst: [?D4] int, 
                                neiR: [?D5] int, start_iR: [?D6] int, srcR: [?D7] int, 
                                dstR: [?D8] int):string throws {
            
            
            var tmp1: [D1] real;
            var tmp2: [D1] real;
            
            var cur_level = 0;
            var SetCurF = new DistBag(int, Locales); // use bag to keep the current frontier
            var SetNextF = new DistBag(int, Locales); // use bag to keep the next frontier
            SetCurF.add(root);
            var numCurF = 1 : int;
            depth[root] = 0;
            while (numCurF > 0) {
                coforall loc in Locales  with (ref SetNextF) {
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

                        forall i in SetCurF with (ref SetNextF) {
                            // current edge has the vertex
                            if((xlocal(i, vertexBegin, vertexEnd))) { 
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
                            if ((xlocal(i, vertexBeginR, vertexEndR))) {
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
                    } // end on loc
                }// end coforall loc
                cur_level += 1;
                numCurF = SetNextF.getSize();
                SetCurF <=> SetNextF;
                SetNextF.clear();
            }// end while 
            return "success";
        }// end of fo_bag_bfs_kernel_u

        /**
        * BFS kernel for directed graphs. 
        *
        * nei: neighbor array
        * start_i: starting edge array location given vertex v
        * src: source array
        * dst: destination array
        *
        * returns: message back to Python.
        */
        proc fo_bag_bfs_kernel_dir( nei: [?D1] int, start_i: [?D2] int, src: [?D3] int, 
                                  dst: [?D4] int): string throws {
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
                        forall i in SetCurF with (ref SetNextF) {
                            if ((xlocal(i, vertexBegin, vertexEnd))) { // current edge has the vertex
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
                    } // end on loc
                } // end coforall loc
                cur_level += 1;
                numCurF = SetNextF.getSize();
                SetCurF <=> SetNextF;
                SetNextF.clear();
            }//end while  
            return "success";
        }//end of fo_bag_bfs_kernel_d

        rootN = msgArgs.getValueOf("Source");
        root = rootN:int;
        depth[root]=0;

        proc return_depth(): string throws{
            var depthName = st.nextName();
            var depthEntry = new shared SymEntry(depth);
            st.addEntry(depthName, depthEntry);

            var depMsg =  'created ' + st.attrib(depthName);
            return depMsg;
        }

        if(directed) {
            fo_bag_bfs_kernel_dir(
                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a
            );
            repMsg=return_depth();
        } else {
            fo_bag_bfs_kernel_und(
                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a
            );
            repMsg=return_depth();
        }
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    use CommandMap;
    registerFunction("segmentedGraphBFS", segBFSMsg, getModuleName());
}