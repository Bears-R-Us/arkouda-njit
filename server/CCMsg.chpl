module CCMsg {
  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  use ServerErrorStrings;
  use ServerConfig;
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use RandArray;
  use IO;

  use SymArrayDmap;
  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use ArgSortMsg;
  use Time;
  use CommAggregation;
  use Sort;
  use Map;
  use DistributedDeque;

  use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;

  // private config const logLevel = ServerConfig.logLevel;
  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  
  config const start_min_degree = 1000000;
  var tmpmindegree=start_min_degree;

  private proc xlocal(x :int, low:int, high:int):bool {
    return low<=x && x<=high;
  }

  private proc xremote(x :int, low:int, high:int):bool {
    return !xlocal(x, low, high);
  }

  proc segCCMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
    // Get the values passeed to Python and now, Chapel. 
    var (n_verticesN, n_edgesN, directedN, weightedN, graphEntryName, restpart) = payload.splitMsgToTuple(6);
    
    // Initialize the variables with graph data. 
    var Nv = n_verticesN:int; 
    var Ne = n_edgesN:int; 
    var Directed = directedN:int; 
    var Weighted = weightedN:int; 
    
    // Declare the other variables to be used. 
    var CCName:string; 
    var srcN, dstN, startN, neighbourN, vweightN, eweightN, rootN:string;
    var srcRN, dstRN, startRN, neighbourRN:string;
    
    // Initialize the distributed visited array. 
    var visited = makeDistArray(Nv, int); 
    
    // Initialize the timer to track the execution of the implementation. 
    // var timer:Timer;

    // Get our graph information. 
    var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
    var ag = gEntry.graph;

    // Implementation of the algorithm for undirected graphs, they can be 
    // weighted or unweighted. 
    proc cc_kernel_und(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws { 
      // Look for the first instance of -1 and get the first vertex to
      // start BFS at. The first component is obviously component 1. 

      // Change the visited array to all -1. 
      coforall loc in Locales {
        on loc {
          forall i in visited.localSubdomain() {
            visited[i] = -1; 
          }
        }
      }

      var finder = visited.find(-1); 
      var unvisited:bool = finder[0]; 
      var nextVertex:int = finder[1];
      var component:int = 0; 

      // writeln("src=", src);
      // writeln("dst=", dst);
      // writeln("nei=", nei);
      // writeln("start_i=", start_i);

      // writeln("srcR=", srcR);
      // writeln("dstR=", dstR);
      // writeln("neiR=", neiR);
      // writeln("start_iR=", start_iR);

      while(unvisited) {
        // Current level starts at 0.
        var cur_level = 0; 

        // Distributed bags used to keep the current and the next frontiers
        // during the execution of the BFS steps. 
        var SetCurF = new DistBag(int, Locales);
        var SetNextF = new DistBag(int, Locales); 

        // Initialize the current frontier. 
        SetCurF.add(nextVertex); 

        // Size of the current frontier. 
        var numCurF:int = 1; 

        // Top-down and bottom-up counters. 
        var topdown:int = 0; 
        var bottomup:int = 0; 

        // Make the depth array. 
        var depth = makeDistArray(Nv, int); 

        // Initialize the depth array. 
        coforall loc in Locales {
          on loc {
            forall i in visited.localSubdomain() {
              depth[i] = -1; 
            }
          }
        }

        // The BFS loop for while the number of vertices in the current 
        // frontier is greater than 0. 
        while(numCurF > 0) {
          coforall loc in Locales with (ref SetNextF, + reduce topdown, + reduce bottomup) {
            on loc {
              // Get references to the arrays we will be using so 
              // data is not copied.
              ref srcf = src; 
              ref df = dst; 
              ref nf = nei; 
              ref sf = start_i; 

              ref srcfR = srcR; 
              ref dfR = dstR; 
              ref nfR = neiR; 
              ref sfR = start_iR;

              // Get from edge arrays the low and high indices. 
              var edgeBegin = src.localSubdomain().lowBound; 
              var edgeEnd = src.localSubdomain().highBound; 

              // Test variables.
              var arrBegin = nei.localSubdomain().lowBound; 
              var arrEnd = nei.localSubdomain().highBound; 

              // writeln("On loc ", loc, " src=", src[edgeBegin..edgeEnd]);
              // writeln("On loc ", loc, " dst=", dst[edgeBegin..edgeEnd]); 
              // writeln("On loc ", loc, " srcR=", srcR[edgeBegin..edgeEnd]);
              // writeln("On loc ", loc, " dstR=", dstR[edgeBegin..edgeEnd]); 
              // writeln("On loc ", loc, " nei=", nei[arrBegin..arrEnd]);
              // writeln("On loc ", loc, " neiR=", neiR[arrBegin..arrEnd]); 
              // writeln("On loc ", loc, " start_i=", start_i[arrBegin..arrEnd]);
              // writeln("On loc ", loc, " start_iR=", start_iR[arrBegin..arrEnd]);
                      
              // Get the start and end vertices from the edge arrays.
              var vertexBegin=src[edgeBegin];
              var vertexEnd=src[edgeEnd];
              var vertexBeginR=srcR[edgeBegin];
              var vertexEndR=srcR[edgeEnd];

              // Check to see if x is local, between low and high. 
              // Helper method for the BFS traversal. 
              proc xlocal(x:int, low:int, high:int) : bool {
                if (low <= x && x <= high) {
                  return true;
                } 
                else {
                  return false;
                }
              }
                      
              // These steps I do manually here wheras in the BFS
              // code they are done before the calling of the 
              // procedure. This is a temporary workaround! 
              var GivenRatio = -0.6 * -1;
              var LF = 1; 
                      
              // If the ratio is ever greater than 0.6, bottom-up is
              // activated. 
              var switchratio = (numCurF:real) / nf.size:real;
                      
              /****************** TOP DOWN ********************/
              if (switchratio < GivenRatio) {
                topdown+=1;
                forall i in SetCurF with (ref SetNextF) {
                  // Current edge has the vertex. 
                  if ((xlocal(i, vertexBegin, vertexEnd)) || (LF == 0)) {
                    var numNF = nf[i];
                    var edgeId = sf[i];
                    var nextStart = max(edgeId, edgeBegin);
                    var nextEnd = min(edgeEnd, edgeId+numNF-1);
                    ref NF = df[nextStart..nextEnd];
                    forall j in NF with (ref SetNextF){
                      if (depth[j] == -1) {
                        depth[j] = cur_level+1;
                        SetNextF.add(j);
                      }
                      if (visited[i] == -1) {
                        visited[i] = component; 
                      }
                    }
                  } 
                  if ((xlocal(i, vertexBeginR, vertexEndR)) || (LF == 0))  {
                    var numNF = nfR[i];
                    var edgeId = sfR[i];
                    var nextStart = max(edgeId, edgeBegin);
                    var nextEnd = min(edgeEnd, edgeId+numNF-1);
                    ref NF = dfR[nextStart..nextEnd];
                    forall j in NF with (ref SetNextF) {
                      if (depth[j] == -1) {
                        depth[j] = cur_level+1;
                        SetNextF.add(j);
                      }
                      if (visited[i] == -1) {
                        visited[i] = component; 
                      }
                    }
                  }
                }//end forall
              } 
              /****************** BOTTOM UP ********************/
              else {
                bottomup+=1;
                forall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                  if (depth[i] == -1) {
                    var numNF = nf[i];
                    var edgeId = sf[i];
                    var nextStart = max(edgeId, edgeBegin);
                    var nextEnd = min(edgeEnd, edgeId + numNF - 1);
                    ref NF = df[nextStart..nextEnd];
                    forall j in NF with (ref SetNextF){
                      if (SetCurF.contains(j)) {
                        depth[i] = cur_level+1;
                        SetNextF.add(i);
                      }
                      if (visited[i] == -1) {
                        visited[i] = component; 
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
                      if (visited[i] == -1) {
                        visited[i] = component; 
                      }
                    }
                  }
                }
              }
            }//end on loc
          }//end coforall loc
          cur_level+=1;
          numCurF=SetNextF.getSize();
          SetCurF<=>SetNextF;
          SetNextF.clear();
        }//end while  

        // Increase the component number to find the next component, if it exists.
        finder = visited.find(-1);
        unvisited = finder[0]; 
        nextVertex = finder[1];
        component += 1; 
      } // end outermost while
      // writeln("Serial visited = ", visited);

      // var maxC = max reduce visited; 
      // writeln("max value = ", maxC); 

      // var hist = makeDistArray(maxC + 1, atomic int); 

      // forall i in visited {
      //   hist[i].fetchAdd(1);
      // }
      // writeln("hist = ", hist); 
      return "success";
    }//end of cc_kernel_und

    // Implementation of a second algorithm for undirected graphs, 
    // they can be weighted or unweighted. 
    proc cc_kernel_und_1(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws { 
      // Initialize the distributed loop over the locales. All the work is going to be split
      // amongst how many locales are available in a cluster. 
      var startVertex: [0..numLocales-1] int = 0;
      var endVertex: [0..numLocales-1] int = 0;
      var MaxComponent:int;
      MaxComponent = 100;
      var BeyondLevel = MaxComponent*(numLocales+1):int;
      var ReplaceAry = makeDistArray(MaxComponent*numLocales, atomic int);
      var depth = makeDistArray(Nv, atomic int);

      proc minLevel(l):int {
        var repv=ReplaceAry[l].read();
        if (repv==-1) {
          return l;
        } else {
          return minLevel(repv);
        }
      }

      proc updateLevel(l: int, m:int) {
        var repv=ReplaceAry[l].read();
        ReplaceAry[l].write(m);
        while (repv!=-1) {
          var nextv=ReplaceAry[repv].read();
          ReplaceAry[repv].write(m);
          repv=nextv;
        }
      }

      coforall loc in Locales {
        on loc {
          var low = src.localSubdomain().lowBound; 
          var high = src.localSubdomain().highBound; 

          //Firstly, we get the vertex based on partitioned edges.
          startVertex[here.id]=src[low];
          endVertex[here.id]=src[high];
          if (here.id==0) {
            startVertex[0]=0;
          }
          if (here.id==numLocales-1){
            endVertex[numLocales-1]=Nv-1;
          }
          //Then, we modify the first and the last vertex 
        }
      }

      coforall loc in Locales {
        on loc {
          if (here.id <numLocales-1) {
            if (endVertex[here.id]<=startVertex[here.id+1]) {
              endVertex[here.id]=startVertex[here.id+1]-1;  
            }
          }
          var cur_level:int;
          cur_level=here.id*MaxComponent;

          forall i in depth.localSubdomain() {
            depth[i].write(-1);
          }

          forall i in ReplaceAry.localSubdomain() {
            ReplaceAry[i].write(-1);
          }

          var cur_vertex=startVertex[here.id];
          var dlow = dst.localSubdomain().lowBound; 
          var dhigh = dst.localSubdomain().highBound; 
          var MergedAry:[0..MaxComponent*numLocales-1] int = -1;
          while (cur_vertex<=endVertex[here.id]) {
            var depcur=depth[cur_vertex].read();
            cur_level=here.id*MaxComponent+cur_vertex-startVertex[here.id];
            if (depcur!=-1 ){
              cur_level=depcur;
            }
            var root = cur_vertex; 
            

            var SetCurF = new set(int, parSafe=true);
            var SetNextF = new set(int, parSafe=true);

            SetCurF.add(root); 

	          var numCurF=1:int; 

            while(numCurF > 0) {
              ref srcf = src; 
              ref df = dst; 
              ref nf = nei; 
              ref sf = start_i; 

              ref srcfR = srcR; 
              ref dfR = dstR; 
              ref nfR = neiR; 
              ref sfR = start_iR;

              forall i in SetCurF with (ref SetNextF) {
                var numNF = nf[i];
                var edgeId = sf[i];
                var nextStart = edgeId;
                var nextEnd = edgeId+numNF-1;
                ref NF = df[nextStart..nextEnd];
                
                forall j in NF with (ref SetNextF) {
                  var depj=depth[j].read();
                  if (depj == -1) {
                    depth[j].write(cur_level);
                    if ( (j>=startVertex[here.id]) && (j<=endVertex[here.id])) {
                      SetNextF.add(j);
                    }
                  } 
                  else {
                    if ((BeyondLevel*here.id+cur_level !=depj) && (depj!=cur_level)) {
                      // the visited vertex has been revisited from other component
                      if (depj>=BeyondLevel) {
                        depj=mod(depj,BeyondLevel);
                      }
                      var prepc=minLevel(cur_level);
                      var prepj=minLevel(depj);
                      if (prepc>prepj) {
                        updateLevel(cur_level,prepj);
                      } 
                      else {
                        if (prepj>prepc) {
                          updateLevel(depj,prepc);
                        }
                      }
                      depth[j].write(BeyondLevel*here.id+cur_level);
                    }
                  }
                }
                numNF = nfR[i];
                edgeId = sfR[i];
                nextStart = edgeId;
                nextEnd = edgeId+numNF-1;
                ref NF2 = dfR[nextStart..nextEnd];
                forall j in NF2 with (ref SetNextF) {
                  var depj=depth[j].read();
                  if (depj == -1) {
                    depth[j].write(cur_level);
                    if ((j>=startVertex[here.id]) && (j<=endVertex[here.id])) {
                      SetNextF.add(j);
                    }
                  }
                  else {
                    if ((BeyondLevel*here.id+cur_level !=depj) && (depj!=cur_level)) {
                      // the visited vertex has been revisited from other component
                      if (depj>=BeyondLevel) {
                        depj=mod(depj,BeyondLevel);
                      }  
                      var prepc=minLevel(cur_level);
                      var prepj=minLevel(depj);
                      if (prepc > prepj) {
                        updateLevel(cur_level,prepj);
                      } 
                      else {
                        if (prepj>prepc) {
                          updateLevel(depj,prepc);
                        }
                      }
                      depth[j].write(BeyondLevel*here.id+cur_level);
                    }
                  }
                }
              }//end forall
              numCurF=SetNextF.size;
              SetCurF=SetNextF;
              SetNextF.clear();
            }//end while 
            cur_vertex+=1;
          }//end of visit
          
          forall i in depth.localSubdomain() {
            var tmpvar1=depth[i].read();
            tmpvar1=mod(tmpvar1,BeyondLevel);
            var tmpvar2=ReplaceAry[tmpvar1].read();
            if (tmpvar2!=-1) {
              var tmpvar3=ReplaceAry[tmpvar2].read();
              while (tmpvar3!=-1) {
                tmpvar2=tmpvar3;
                tmpvar3=ReplaceAry[tmpvar2].read();
              }
              depth[i].write(tmpvar2);
            }
          }
        }//end on loc
      }//end coforall
      // writeln("Parallel visited = ", depth);
      return "success";
    }//end of cc_kernel_und_1

    // Third implemention of the fast shiloach-vishkin algorithm for connected components proposed 
    // by Yongzhe Zhang, Ariful Azad, and Zhenjiang Hu.
    proc cc_fast_sv(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_next = makeDistArray(Nv, int); 

      forall i in 0..Nv {
        f[i] = i;
        f_next[i] = i;
      }

      // writeln("$$$$$ Iteration 0 $$$$$");
      // writeln("f               = ", f);
      // writeln("f_next          = ", f_next);

      var converged = false;
      var gf = f;
      var itera = 1;
      while(!converged) {
        // Duplicate of gf.
        var dup = gf;

        // Stochastic hooking.
        // writeln("Stochastic hooking:");
        forall x in 0..Ne {
          // Get edges from src, dst, srcR, and dstR.
          var u = src[x];
          var v = dst[x];

          var uf = srcR[x];
          var vf = dstR[x];
          
          if(f[f[v]] < f_next[f[u]]) {
            // writeln("inner u v = ", u, " ", v);
            f_next[f[u]] = f[f[v]];
          }

          if(f[f[vf]] < f_next[f[uf]]) {
            // writeln("inner uf vf = ", uf, " ", vf);
            f_next[f[uf]] = f[f[vf]];
          }
        }
        // writeln();

        // Aggresive hooking.
        // writeln("Aggresive hooking:");
        forall x in 0..Ne {
          var u = src[x];
          var v = dst[x];

          var uf = srcR[x];
          var vf = dstR[x];

          if(f[f[v]] < f_next[u]) {
            // writeln("inner u v = ", u, " ", v);
            f_next[u] = f[f[v]];
          }

          if(f[f[vf]] < f_next[uf]) {
            // writeln("inner uf vf = ", uf, " ", vf);
            f_next[uf] = f[f[vf]];
          }
        }
        // writeln();

        // Shortcutting.
        // writeln("Shortcutting:");
        forall u in 0..Nv {
          if(f[f[u]] < f_next[u]) {
            // writeln("inner u v = ", u, " ", v);
            f_next[u] = f[f[u]];
          }
        }
        // writeln();

        // writeln("$$$$$ Iteration ", itera," $$$$$");
        // writeln("f               = ", f);
        // writeln("f_next          = ", f_next);
        
        f = f_next; 

        // Recompute gf.
        forall x in 0..Nv {
          gf[x] = f[f[x]];
        }

        // Check if gf converged.
        var diff = makeDistArray(Nv, int);
        forall x in 0..Nv {
          diff[x] = gf[x] - dup[x];
        }
        var sum = + reduce diff;

        // writeln("sum = ", sum);

        if(sum == 0) {
          converged = true;
        }
        else {
          converged = false;
        }
        itera += 1;
      }
      //writeln("Fast sv visited =      ", f, " Number of iterations = ", itera);

      return f;
    }

    // Fourth implemention of the fast shiloach-vishkin algorithm for connected components proposed 
    // by Yongzhe Zhang, Ariful Azad, and Zhenjiang Hu. Made to be distributed.
    proc cc_fast_sv_dist(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_next = makeDistArray(Nv, int); 
      var gf = makeDistArray(Nv, int);
      var dup = makeDistArray(Nv, int);
      var diff = makeDistArray(Nv, int);

      // Initialize f and f_next in distributed memory.
      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f[i] = i;
            f_next[i] = i;
          }
        }
      }

      var converged = false;
      var itera = 1;
      gf = f;
      while(!converged) {
        // Duplicate of gf.
        dup = gf;

        // Stochastic hooking.
        // writeln("Stochastic hooking:");
        coforall loc in Locales {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd {
              // Get edges from src, dst, srcR, and dstR.
              var u = src[x];
              var v = dst[x];

              var uf = srcR[x];
              var vf = dstR[x];
              
              if(f[f[v]] < f_next[f[u]]) {
                // writeln("inner u v = ", u, " ", v);
                f_next[f[u]] = f[f[v]];
              }

              if(f[f[vf]] < f_next[f[uf]]) {
                // writeln("inner uf vf = ", uf, " ", vf);
                f_next[f[uf]] = f[f[vf]];
              }
            }
          }
        }
        // writeln();

        // Aggresive hooking.
        // writeln("Aggresive hooking:");
        coforall loc in Locales {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd {
              var u = src[x];
              var v = dst[x];

              var uf = srcR[x];
              var vf = dstR[x];

              if(f[f[v]] < f_next[u]) {
                // writeln("inner u v = ", u, " ", v);
                f_next[u] = f[f[v]];
              }

              if(f[f[vf]] < f_next[uf]) {
                // writeln("inner uf vf = ", uf, " ", vf);
                f_next[uf] = f[f[vf]];
              }
            }
          }
        }
        // writeln();

        // Shortcutting.
        // writeln("Shortcutting:");

        coforall loc in Locales {
          on loc {
            var vertexBegin = f.localSubdomain().lowBound;
            var vertexEnd = f.localSubdomain().highBound;
            forall u in vertexBegin..vertexEnd {
              if(f[f[u]] < f_next[u]) {
                // writeln("inner u v = ", u, " ", v);
                f_next[u] = f[f[u]];
              }
            }
          }
        }
        // writeln();

        // writeln("$$$$$ Iteration ", itera," $$$$$");
        // writeln("f               = ", f);
        // writeln("f_next          = ", f_next);
        
        f = f_next; 

        // Recompute gf.
        coforall loc in Locales {
          on loc {
            var vertexBegin = f.localSubdomain().lowBound;
            var vertexEnd = f.localSubdomain().highBound;
            forall x in vertexBegin..vertexEnd {
              gf[x] = f[f[x]];
            }
          }
        }

        // Check if gf converged.
        coforall loc in Locales {
          on loc {
            var vertexBegin = f.localSubdomain().lowBound;
            var vertexEnd = f.localSubdomain().highBound;
            forall x in vertexBegin..vertexEnd {
              diff[x] = gf[x] - dup[x];
            }
          }
        }
        var sum = + reduce diff;

        if(sum == 0) {
          converged = true;
        }
        else {
          converged = false;
        }
        itera += 1;
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);

      return f;
    }




    // FastSpread: a  propogation based connected components algorithm
    proc cc_fs_dist(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_next = makeDistArray(Nv, int); 
      var gf = makeDistArray(Nv, int);
      var dup = makeDistArray(Nv, int);
      var diff = makeDistArray(Nv, int);

      // Initialize f and f_next in distributed memory.
      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f[i] = i;
            f_next[i] = i;
          }
        }
      }

      var converged:bool = false;
      var itera = 1;
      while(!converged) {
        var count:int=0;
        coforall loc in Locales with ( + reduce count) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
              var u = src[x];
              var v = dst[x];


              var minindex=min(f[u],f[v],f[f[u]],f[f[v]]);
              //we may include more f[f[f[u]]] and f[f[f[v]]] to accelerate the convergence speed
              if(minindex < f_next[f[u]]) {
                f_next[f[u]] = minindex;
                count+=1;
              }
              if(minindex < f_next[f[v]]) {
                f_next[f[v]] = minindex;
                count+=1;
              }
              if(minindex < f_next[u]) {
                f_next[u] = minindex;
                count+=1;
              }
              if(minindex < f_next[v]) {
                f_next[v] = minindex;
                count+=1;
              }

              
            }
          }
        }


        f = f_next; 


        if(count == 0) {
          converged = true;
        }
        else {
          converged = false;
        }
        itera += 1;
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);

      return f;
    }


    var timer:Timer;
    // We only care for undirected graphs, they can be weighted or unweighted. 
    if (Weighted == 0)  {
      if (Directed == 0) {
        (srcN, dstN, startN, neighbourN, srcRN, dstRN, startRN, neighbourRN) = restpart.splitMsgToTuple(8);
        timer.clear();
        timer.start(); 
        var f1 = cc_fast_sv_dist( toSymEntry(ag.getNEIGHBOR(), int).a, 
                                toSymEntry(ag.getSTART_IDX(), int).a, 
                                toSymEntry(ag.getSRC(), int).a, 
                                toSymEntry(ag.getDST(), int).a, 
                                toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                                toSymEntry(ag.getSTART_IDX_R(), int).a, 
                                toSymEntry(ag.getSRC_R(), int).a, 
                                toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for fast sv dist cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        var f2 = cc_fast_sv(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for fast sv cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        var f3 = cc_fs_dist(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for simple fs cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        coforall loc in Locales {
          on loc {
            var vertexStart = f1.localSubdomain().lowBound;
            var vertexEnd = f1.localSubdomain().highBound;
            forall i in vertexStart..vertexEnd {
              if (f2[i] != f3[i]) {
                var outMsg = "!!!!!CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                exit(0);
              }
            }
          }
        } 

        // timer.clear();
        // timer.start(); 
        // temp = cc_kernel_und_1( toSymEntry(ag.getNEIGHBOR(), int).a, 
        //                         toSymEntry(ag.getSTART_IDX(), int).a, 
        //                         toSymEntry(ag.getSRC(), int).a, 
        //                         toSymEntry(ag.getDST(), int).a, 
        //                         toSymEntry(ag.getNEIGHBOR_R(), int).a, 
        //                         toSymEntry(ag.getSTART_IDX_R(), int).a, 
        //                         toSymEntry(ag.getSRC_R(), int).a, 
        //                         toSymEntry(ag.getDST_R(), int).a);
        // timer.stop(); 
        // outMsg = "Time elapsed for du cc: " + timer.elapsed():string;
        // smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        // timer.clear();
        // timer.start(); 
        // var temp = cc_kernel_und(  toSymEntry(ag.getNEIGHBOR(), int).a, 
        //                     toSymEntry(ag.getSTART_IDX(), int).a, 
        //                     toSymEntry(ag.getSRC(), int).a, 
        //                     toSymEntry(ag.getDST(), int).a, 
        //                     toSymEntry(ag.getNEIGHBOR_R(), int).a, 
        //                     toSymEntry(ag.getSTART_IDX_R(), int).a, 
        //                     toSymEntry(ag.getSRC_R(), int).a, 
        //                     toSymEntry(ag.getDST_R(), int).a);
        // timer.stop(); 
        // outMsg = "Time elapsed for serial cc: " + timer.elapsed():string;
        // smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      }
    }
    else {
      if (Directed == 0) {
        (srcN, dstN, startN, neighbourN, srcRN, dstRN, startRN, neighbourRN, vweightN, eweightN) = restpart.splitMsgToTuple(10);
        timer.clear();
        timer.start();
        var f1 = cc_fast_sv_dist( toSymEntry(ag.getNEIGHBOR(), int).a, 
                                    toSymEntry(ag.getSTART_IDX(), int).a, 
                                    toSymEntry(ag.getSRC(), int).a, 
                                    toSymEntry(ag.getDST(), int).a, 
                                    toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                                    toSymEntry(ag.getSTART_IDX_R(), int).a, 
                                    toSymEntry(ag.getSRC_R(), int).a, 
                                    toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for fast sv dist cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        var f2 = cc_fast_sv(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for fast sv cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        var f3 = cc_fs_dist(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for simple fs cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        coforall loc in Locales {
          on loc {
            var vertexStart = f1.localSubdomain().lowBound;
            var vertexEnd = f1.localSubdomain().highBound;
            forall i in vertexStart..vertexEnd {
              if (f2[i] != f3[i]) {
                var outMsg = "!!!!!CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                exit(0);
              }
            }
          }
        } 

        // timer.clear();
        // timer.start(); 
        // temp = cc_kernel_und_1( toSymEntry(ag.getNEIGHBOR(), int).a, 
        //                         toSymEntry(ag.getSTART_IDX(), int).a, 
        //                         toSymEntry(ag.getSRC(), int).a, 
        //                         toSymEntry(ag.getDST(), int).a, 
        //                         toSymEntry(ag.getNEIGHBOR_R(), int).a, 
        //                         toSymEntry(ag.getSTART_IDX_R(), int).a, 
        //                         toSymEntry(ag.getSRC_R(), int).a, 
        //                         toSymEntry(ag.getDST_R(), int).a);
        // timer.stop(); 
        // outMsg = "Time elapsed for du cc: " + timer.elapsed():string;
        // smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        // timer.clear();
        // timer.start(); 
        // var temp = cc_kernel_und(  toSymEntry(ag.getNEIGHBOR(), int).a, 
        //                     toSymEntry(ag.getSTART_IDX(), int).a, 
        //                     toSymEntry(ag.getSRC(), int).a, 
        //                     toSymEntry(ag.getDST(), int).a, 
        //                     toSymEntry(ag.getNEIGHBOR_R(), int).a, 
        //                     toSymEntry(ag.getSTART_IDX_R(), int).a, 
        //                     toSymEntry(ag.getSRC_R(), int).a, 
        //                     toSymEntry(ag.getDST_R(), int).a);
        // timer.stop(); 
        // outMsg = "Time elapsed for serial cc: " + timer.elapsed():string;
        // smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      }
    }
    
    // The message that is sent back to the Python front-end. 
    proc return_CC(): string throws {
      CCName = st.nextName();
      var CCEntry = new shared SymEntry(visited);
      st.addEntry(CCName, CCEntry);

      var CCMsg =  'created ' + st.attrib(CCName);
      return CCMsg;
    }

    var repMsg = return_CC();
    return new MsgTuple(repMsg, MsgType.NORMAL);
  }

  use CommandMap;
  registerFunction("segmentedGraphCC", segCCMsg);
}
