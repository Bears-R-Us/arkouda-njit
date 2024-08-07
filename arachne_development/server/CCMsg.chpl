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

  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use ArgSortMsg;
  use Time;
  use CommAggregation;
  use Sort;
  use Map;
  use DistributedDeque;

  //use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;

  use Set;

  // private config const logLevel = ServerConfig.logLevel;
  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  
  config const start_min_degree = 1000000;
  var tmpmindegree=start_min_degree;

  const JumpSteps=6;
  const FirstOrderIters=4;
  const SecondOrderIters=6;
  var  ORDERH:int=512;
  const LargeScale=1000000;
  const LargeEdgeEfficiency=100;
  const MultiLocale=0;

  private proc xlocal(x :int, low:int, high:int):bool {
    return low<=x && x<=high;
  }

  private proc xremote(x :int, low:int, high:int):bool {
    return !xlocal(x, low, high);
  }

  proc segCCMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
    // Get the values passeed to Python and now, Chapel. 
    //var (n_verticesN, n_edgesN, directedN, weightedN, graphEntryName, restpart) = payload.splitMsgToTuple(6);
    
    //var msgArgs = parseMessageArgs(payload, argSize);
    var n_verticesN=msgArgs.getValueOf("NumOfVertices");
    var n_edgesN=msgArgs.getValueOf("NumOfEdges");
    var directedN=msgArgs.getValueOf("Directed");
    var weightedN=msgArgs.getValueOf("Weighted");
    var graphEntryName=msgArgs.getValueOf("GraphName");


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
    // var timer:stopwatch;

    // Get our graph information. 
    var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
    var ag = gEntry.graph;




    // Third implemention of the fast shiloach-vishkin algorithm for connected components proposed 
    // by Yongzhe Zhang, Ariful Azad, and Zhenjiang Hu.
    proc cc_fast_sv(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_low = makeDistArray(Nv, int); 
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      forall i in 0..Nv-1 with (ref f, ref f_low ) {
        f[i] = i;
        f_low[i] = i;
      }

      // writeln("$$$$$ Iteration 0 $$$$$");
      // writeln("f               = ", f);
      // writeln("f_low          = ", f_low);

      var converged = false;
      var gf = f;
      var itera = 1;
      while(!converged) {
        localtimer.clear();
        localtimer.start(); 
        // Duplicate of gf.
        var dup = gf;

        // Stochastic hooking.
        // writeln("Stochastic hooking:");
        forall x in 0..Ne-1 with (ref f_low) {
          // Get edges from src, dst, srcR, and dstR.
          var u = src[x];
          var v = dst[x];

          var uf = srcR[x];
          var vf = dstR[x];
          
          if(f[f[v]] < f_low[f[u]]) {
            // writeln("inner u v = ", u, " ", v);
            f_low[f[u]] = f[f[v]];
          }

          if(f[f[vf]] < f_low[f[uf]]) {
            // writeln("inner uf vf = ", uf, " ", vf);
            f_low[f[uf]] = f[f[vf]];
          }
        }
        // writeln();

        // Aggresive hooking.
        // writeln("Aggresive hooking:");
        forall x in 0..Ne-1 with (ref f_low) {
          var u = src[x];
          var v = dst[x];

          var uf = srcR[x];
          var vf = dstR[x];

          if(f[f[v]] < f_low[u]) {
            // writeln("inner u v = ", u, " ", v);
            f_low[u] = f[f[v]];
          }

          if(f[f[vf]] < f_low[uf]) {
            // writeln("inner uf vf = ", uf, " ", vf);
            f_low[uf] = f[f[vf]];
          }
        }
        // writeln();

        // Shortcutting.
        // writeln("Shortcutting:");
        forall u in 0..Nv-1 with (ref f_low) {
          if(f[f[u]] < f_low[u]) {
            // writeln("inner u v = ", u, " ", v);
            f_low[u] = f[f[u]];
          }
        }
        // writeln();

        // writeln("$$$$$ Iteration ", itera," $$$$$");
        // writeln("f               = ", f);
        // writeln("f_low          = ", f_low);
        
        f = f_low; 

        // Recompute gf.
        forall x in 0..Nv-1 with (ref gf) {
          gf[x] = f[f[x]];
        }

        // Check if gf converged.
        var diff = makeDistArray(Nv, int);
        forall x in 0..Nv-1 with (ref diff){
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
        localtimer.stop(); 
        executime=localtimer.elapsed();
        myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        writeln("Efficiency is ", myefficiency, " time is ",executime);
      }
      writeln("Number of iterations = ", itera-1);

      return f;
    }



    inline proc find_split(u:int,  ref parents:[?D1] int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                parents[i]= w;
                i = v;
          }
      }
      return v;
    }

    inline proc find_naive(u:int,  parents:[?D1] int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                //parents[i]= w;
                i = v;
          }
      }
      return v;
    }

    inline proc find_naive_atomic(u:int,  ref parents:[?D1] atomic int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                //parents[i]= w;
                i = v;
          }
      }
      return v;
    }

    proc find_naive_atomic_h(u:int,  ref parents:[?D1] atomic int,h:int):int {
       var t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                i = v;
          }
          t=t+1;
       }
       return v;
    }

    proc find_naive_h(u:int,  ref parents:[?D1] int,h:int):int {
       var t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                i = v;
          }
          t=t+1;
       }
       return v;
    }


    inline proc find_split_atomic(u:int,  ref parents:[?D1] atomic int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                parents[i].write(w);
                i = v;
          }
      }
      return v;
    }


    inline proc find_split_h(u:int, ref  parents:[?D1] int, h:int):int {
       var  t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i];
          w = parents[v];
          if (v <= w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                parents[i]= w;
                i = v;
          }
          t=t+1;
      }
      return v;
    }
    inline proc find_split_atomic_h(u:int, ref  parents:[?D1] atomic int, h:int):int {
       var t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                parents[i].compareAndSwap(v, w);
                i = v;
          }
          t=t+1;
      }
      return v;
    }

    proc find_half(u:int,  ref parents:[?D1] int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                parents[i]= w;
                i = parents[i];
          }
       }
       return v;
    }
    proc find_half_h(u:int,  ref parents:[?D1] int,h:int):int {
       var t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                parents[i]= w;
                i = parents[i];
          }
          t=t+1;
       }
       return v;
    }

    proc find_half_atomic_h(u:int,  ref parents:[?D1] atomic int,h:int):int {
       var t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                parents[i].compareAndSwap(v, w);
                i = parents[i].read();
          }
          t=t+1;
       }
       return v;
    }


    proc find_half_atomic(u:int,  ref parents:[?D1] atomic int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                parents[i].compareAndSwap(v, w);
                i = parents[i].read();
          }
       }
       return v;
    }



    proc unite(u:int, v:int,  ref parents:[?D1] int):int {
       var rx=u;
       var ry=v;
       var p_ry = parents[ry];
       var p_rx = parents[rx];
       while (p_ry!=p_rx){
          if (p_rx > p_ry) {
               rx<=>ry;
               p_rx<=> p_ry;
          }
          if (ry == p_ry ) {
                 parents[ry]= p_rx;
                 while (parents[parents[u]]<parents[u]) {
                      parents[u]=parents[parents[u]];
                 }
                 while (parents[parents[v]]<parents[v]) {
                      parents[v]=parents[parents[v]];
                 }
                 //compress(x, parents);
                 //compress(y, parents);
                 return rx;
          } else {
                    //rx = splice(rx, ry, parents);
                    parents[ry]= p_ry;
          }
          p_ry = parents[ry];
          p_rx = parents[rx];
       }
       return rx;
    }



    proc unite_atomic(u:int, v:int,  ref parents:[?D1] atomic int):int {
       var ru=u;
       var rv=v;
       var p_rv = parents[rv].read() ;
       var p_ru = parents[ru].read();
       while (p_rv!=p_ru) {
          if (p_ru < p_rv) {
               ru<=>rv;
               p_ru<=> p_rv;
          }

          if ( (ru == p_ru) && (parents[ru].compareAndSwap(p_ru,p_rv) ) ) {
                 return ru;
          } else {
                    var g_u=parents[p_ru].read();
                    while (p_ru>g_u) {
                         parents[ru].compareAndSwap(p_ru,g_u);
                         p_ru=parents[ru].read();
                    }
                    ru=g_u;
                    p_ru = parents[ru].read();
          }
       }
       return ru;
    }



    // Contour: a minimum mapping based connected components algorithm, a mixed method
    proc cc_contour(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;


      localtimer.clear();
      localtimer.start(); 
      coforall loc in Locales with (ref f) {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd with (ref f) {
            f[i] = i;
            if (nei[i] >0) {
                var tmpv=dst[start_i[i]];
                if ( tmpv <i ) {
                     f[i]=tmpv;
                }
            }
            if (neiR[i] >0) {
                var tmpv=dstR[start_iR[i]];
                if ( tmpv <f[i] ) {
                     f[i]=tmpv;
                }
            }
          }
        }
      }


      localtimer.stop(); 
      executime=localtimer.elapsed();
      myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;

      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      //we first check with order=1 mapping method
      while( (!converged) && (itera<FirstOrderIters) && 
               ( (Ne/here.numPUs() < LargeScale) )) {
        localtimer.clear();
        localtimer.start(); 
        coforall loc in Locales with ( + reduce count, ref f) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
              var u = src[x];
              var v = dst[x];

                         var TmpMin:int;
                         TmpMin=min(f[u],f[v]);
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count=count+1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count=count+1;
                         }
                  
            }//end of forall
          }
        }


        if( (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
          count=0;
        }
        itera += 1;
        writeln("My Order is 1"); 
        localtimer.stop(); 
        executime=localtimer.elapsed();
        //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
      }




      if (Ne/here.numPUs() < LargeScale) {
           ORDERH=2;
      }else {
           ORDERH=1024;
      }  
      // then we use 1m1m method
      while( (!converged) ) {
        localtimer.clear();
        localtimer.start(); 
        coforall loc in Locales with ( + reduce count, ref f) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
              var u = src[x];
              var v = dst[x];

                         var TmpMin:int;
                         TmpMin=min(f[u],f[v]);
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count=count+1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count=count+1;
                         }
                  
            }//end of forall
          }
        }


        itera += 1;
        //writeln("My Order is 1"); 
        localtimer.stop(); 
        executime=localtimer.elapsed();
        //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
        if( (count==0) ) {
          converged = true;
          continue;
        }
        else {
          converged = false;
          count=0;
        }

        // In the second step, we employ high order mapping
        localtimer.clear();
        localtimer.start(); 
        if (ORDERH==2) {
            coforall loc in Locales with ( + reduce count, ref f ) {
              on loc {
                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;

                forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
                  var u = src[x];
                  var v = dst[x];

                  var TmpMin:int;

                  TmpMin=min(f[f[u]],f[f[v]]);
                  if(TmpMin < f[f[u]]) {
                     f[f[u]] = TmpMin;
                  }
                  if(TmpMin < f[f[v]]) {
                     f[f[v]] = TmpMin;
                  }
                  if(TmpMin < f[u]) {
                    f[u] = TmpMin;
                  }
                  if(TmpMin < f[v]) {
                    f[v] = TmpMin;
                  }
                }//end of forall
                forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
                  var u = src[x];
                  var v = dst[x];
                  if (count==0) {
                        if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                            count=1;
                        } 
                  }
                }
              }// end of on loc 
            }// end of coforall loc 
        } else {
            coforall loc in Locales with ( + reduce count , ref f) {
              on loc {
                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;

                forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
                  var u = src[x];
                  var v = dst[x];

                  var TmpMin:int;
                  if (itera==1) {
                      TmpMin=min(u,v);
                  } else{
                      TmpMin=min(find_split_h(u,f,ORDERH),find_split_h(v,f,ORDERH));
                  }
                  if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                      var myx=u;
                      var lastx=u;
                      while (f[myx] >TmpMin ) {
                          lastx=f[myx];
                          f[myx]=TmpMin;
                          myx=lastx;
                      }
                      myx=v;
                      while (f[myx] >TmpMin ) {
                          lastx=f[myx];
                          f[myx]=TmpMin;
                          myx=lastx;
                      }
                  }
                  
                }//end of forall

                forall x in edgeBegin..edgeEnd  with ( + reduce count )  {
                  var u = src[x];
                  var v = dst[x];
                  if (count==0) {
                    if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                        count=1;
                    } 
                  }
                }
              }// end of on loc 
            }// end of coforall loc 

        }


        if( (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
          count=0;
        }
        itera += 1;
        writeln("My Order is ",ORDERH); 
        localtimer.stop(); 
        executime=localtimer.elapsed();
        //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
      }



      writeln("Number of iterations = ", itera-1);

      return f;
    }














    // union-find
    proc cc_unionfind(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 

      // Initialize f and f_low in distributed memory.

      coforall loc in Locales with (ref f) {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd with (ref f) {
            f[i] = i;
            if (nei[i] >0) {
                var tmpv=dst[start_i[i]];
                if ( tmpv <i ) {
                     f[i]=tmpv;
                }
            }
            if (neiR[i] >0) {
                var tmpv=dstR[start_iR[i]];
                if ( tmpv <f[i] ) {
                     f[i]=tmpv;
                }
            }
          }
        }
      }



      var converged:bool = false;
      var itera = 1;
      {
        var count:int=0;
        var count1:int=0;
        coforall loc in Locales with ( + reduce count, + reduce count1, ref f) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with (ref f)   {
              var u = src[x];
              var v = dst[x];
              unite(u,v,f);
            }//end of forall
            forall x in edgeBegin..edgeEnd  with (ref f)  {
              var u = src[x];
              var v = dst[x];
              var l=find_half(u,f);
              var t=u;
              var ft=f[t];
              while (f[t]>l) {
                  ft=f[t];
                  f[t]=l;
                  t=ft;
              }
              l=find_half(v,f);
              t=v;
              while (f[t]>l) {
                  ft=f[t];
                  f[t]=l;
                  t=ft;
              }
            }//end of forall
          }
        }
      }
      writeln("Number of iterations = ", itera);

      return f;
    }






    // Fourth implemention of the fast shiloach-vishkin algorithm for connected components proposed 
    // by Yongzhe Zhang, Ariful Azad, and Zhenjiang Hu. Made to be distributed.
    proc cc_fast_sv_dist(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_low = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 

      var gf = makeDistArray(Nv, int);
      var dup = makeDistArray(Nv, int);
      var diff = makeDistArray(Nv, int);
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      var count:int=0;
      var converged:bool=false;
      var itera:int=1;

      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
                on loc {
                    forall i in f.localSubdomain()  with (ref af) {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count ,ref af) {
                     on loc {
                             var localf:[0..Nv-1] int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref localf) {
                                 localf[i]=af[i].read();
                             }
                             var localfu=localf;
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount, ref localfu)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    if localfu[localf[u]]>localf[localf[v]] {
                                         localfu[localf[u]]=localf[localf[v]];
                                         lcount+=1;
                                    }
                                }
                                forall x in src.localSubdomain()  with ( + reduce lcount, ref localfu)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    if localfu[localf[v]]>localf[localf[u]] {
                                         localfu[localf[v]]=localf[localf[u]];
                                         lcount+=1;
                                    }
                                }
                                forall x in src.localSubdomain()  with ( + reduce lcount, ref localfu)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    if localfu[u]>localf[localf[v]] {
                                         localfu[u]=localf[localf[v]];
                                         lcount+=1;
                                    }
                                }
                                forall x in src.localSubdomain()  with ( + reduce lcount, ref localfu)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    if localfu[v]>localf[localf[u]] {
                                         localfu[v]=localf[localf[u]];
                                         lcount+=1;
                                    }
                                }
                                forall x in src.localSubdomain()  with ( + reduce lcount, ref localfu)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    if localfu[u]>localf[localf[u]] {
                                         localfu[u]=localf[localf[u]];
                                              lcount+=1;
                                    }
                                }

                                forall x in src.localSubdomain()  with ( + reduce lcount, ref localfu)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    if localfu[v]>localf[localf[v]] {
                                         localfu[v]=localf[localf[v]];
                                              lcount+=1;
                                    }
                                }
                                localf=localfu;
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count, ref af) {
                                 var old=af[i].read();
                                 var newval=localfu[i];
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count, ref f) {
                 f[i]=af[i].read();
           }

      } else {
      // Initialize f and f_low in distributed memory.
      coforall loc in Locales with (ref f, ref f_low) {
        on loc {
          forall i in f.localSubdomain() with (ref f, ref f_low) {
            f[i] = i;
            f_low[i] = i;
          }
        }
      }

      //var converged = false;
      //var itera = 1;
      gf = f;
      while(!converged) {
        localtimer.clear();
        localtimer.start(); 
        // Duplicate of gf.
        dup = gf;

        // Stochastic hooking.
        // writeln("Stochastic hooking:");
        coforall loc in Locales with (ref f_low) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd {
              // Get edges from src, dst, srcR, and dstR.
              var u = src[x];
              var v = dst[x];

              var uf = srcR[x];
              var vf = dstR[x];
              var fu=f[u];
              var fv=f[v];
              var fuf=f[fu];
              var fvf=f[fv];
              
              if(f[fv] < f_low[fu]) {
                // writeln("inner u v = ", u, " ", v);
                f_low[fu] = f[fv];
              }

              if(f[fvf] < f_low[fuf]) {
                // writeln("inner uf vf = ", uf, " ", vf);
                f_low[fuf] = f[fvf];
              }
            }
          }
        }
        // writeln();

        // Aggresive hooking.
        // writeln("Aggresive hooking:");
        coforall loc in Locales with (ref f_low) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd {
              var u = src[x];
              var v = dst[x];

              var uf = srcR[x];
              var vf = dstR[x];

              if(f[f[v]] < f_low[u]) {
                // writeln("inner u v = ", u, " ", v);
                f_low[u] = f[f[v]];
              }

              if(f[f[vf]] < f_low[uf]) {
                // writeln("inner uf vf = ", uf, " ", vf);
                f_low[uf] = f[f[vf]];
              }
            }
          }
        }
        // writeln();

        // Shortcutting.
        // writeln("Shortcutting:");

        coforall loc in Locales with (ref f_low) {
          on loc {
            var vertexBegin = f.localSubdomain().lowBound;
            var vertexEnd = f.localSubdomain().highBound;
            forall u in vertexBegin..vertexEnd {
              if(f[f[u]] < f_low[u]) {
                // writeln("inner u v = ", u, " ", v);
                f_low[u] = f[f[u]];
              }
            }
          }
        }
        // writeln();

        // writeln("$$$$$ Iteration ", itera," $$$$$");
        // writeln("f               = ", f);
        // writeln("f_low          = ", f_low);
        
        f = f_low; 

        // Recompute gf.
        coforall loc in Locales with (ref gf) {
          on loc {
            var vertexBegin = f.localSubdomain().lowBound;
            var vertexEnd = f.localSubdomain().highBound;
            forall x in vertexBegin..vertexEnd {
              gf[x] = f[f[x]];
            }
          }
        }

        // Check if gf converged.
        coforall loc in Locales with (ref diff) {
          on loc {
            var vertexBegin = f.localSubdomain().lowBound;
            var vertexEnd = f.localSubdomain().highBound;
            forall x in vertexBegin..vertexEnd  with (ref diff){
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
        localtimer.stop(); 
        executime=localtimer.elapsed();
        //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
      }
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);

      return f;
    }

    // distance=1;
    proc cc_1(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var count1:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      if (numLocales>1 && MultiLocale==1) {
           coforall loc in Locales with (ref af)  {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count,ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref localf) {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(fu,fv);
                                        var oldx=localf[u].read();
                                        while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[v].read();
                                        while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  v=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }

                                }
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count, ref af) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count) {
                 f[i]=af[i].read();
           }
      } else {
      // Initialize f and f_low in distributed memory.
          coforall loc in Locales with (ref f) {
            on loc {
              var vertexBegin = f.localSubdomain().lowBound;
              var vertexEnd = f.localSubdomain().highBound;
              forall i in vertexBegin..vertexEnd  with (ref f){
                f[i] = i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <f[i] ) {
                         f[i]=tmpv;
                    }
                }
              }
            }
          }  

          while(!converged) {
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count, ref f) {
              on loc {
  
                forall x in src.localSubdomain()  with ( + reduce count, ref f)  {
                  var u = src[x];
                  var v = dst[x];
                  {
                     var TmpMin:int;
                     TmpMin=min(f[u],f[v]);
                     if(TmpMin < f[u]) {
                        f[u] = TmpMin;
                        count+=1;
                     }  
                     if(TmpMin < f[v]) {
                        f[v] = TmpMin;
                        count+=1;
                     }
                  }//end if       
                }//end of forall
              }
            }

            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);

            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
          }
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);

      return f;
    }


    // distance=1;
    proc cc_1_atomic(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var count1:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      if (numLocales>1 && MultiLocale==1) {
           coforall loc in Locales with (ref af)  {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count,ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref localf) {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(fu,fv);
                                        var oldx=localf[u].read();
                                        while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[v].read();
                                        while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  v=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }

                                }
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count, ref af) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count) {
                 f[i]=af[i].read();
           }
      } else {
      // Initialize f and f_low in distributed memory.
          coforall loc in Locales with (ref f) {
            on loc {
              var vertexBegin = f.localSubdomain().lowBound;
              var vertexEnd = f.localSubdomain().highBound;
              forall i in  f.localSubdomain() with (ref af){
                af[i].write(i);
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         af[i].write(tmpv);
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <af[i].read() ) {
                         af[i].write(tmpv);
                    }
                }
              }
            }
          }  

          while(!converged) {
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count, ref af) {
              on loc {
                forall x in src.localSubdomain()  with ( + reduce count, ref af)  {
                  var u = src[x];
                  var v = dst[x];
                  {
                     var TmpMin:int;
                     var oldu=af[u].read();
                     var oldv=af[v].read();
                     TmpMin=min(oldu,oldv);
                     if oldu>TmpMin {
                           af[u].compareAndSwap(oldu,TmpMin);
                           count+=1;
                     }
                     if oldv>TmpMin {
                           af[v].compareAndSwap(oldv,TmpMin);
                           count+=1;
                     }
                  }//end if       
                }//end of forall
              }
            }

            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);

            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
          }
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);
      coforall loc in Locales with ( ref f) {
              on loc {
                forall x in f.localSubdomain()  with (ref f)  {
                     f[x]=af[x].read();    
                }
              }
      }

      return f;
    }


    // distance=1;
    proc cc_1_assign(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var count1:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      if (numLocales>1 && MultiLocale==1) {
           coforall loc in Locales with (ref af)  {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count,ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref localf) {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(fu,fv);
                                        var oldx=localf[u].read();
                                        while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[v].read();
                                        while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  v=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }

                                }
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count, ref af) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count) {
                 f[i]=af[i].read();
           }
      } else {
      // Initialize f and f_low in distributed memory.
          coforall loc in Locales with (ref f, ref af) {
            on loc {
              var vertexBegin = f.localSubdomain().lowBound;
              var vertexEnd = f.localSubdomain().highBound;
              forall i in  f.localSubdomain() with (ref af){
                af[i].write(i);
                f[i]=i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         af[i].write(tmpv);
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <af[i].read() ) {
                         af[i].write(tmpv);
                         f[i]=tmpv;
                    }
                }
              }
            }
          }  

          while(!converged) {
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count, ref af) {
              on loc {
                forall x in src.localSubdomain()  with ( + reduce count, ref af)  {
                  var u = src[x];
                  var v = dst[x];
                  {
                     var TmpMin:int;
                     var oldu=f[u];
                     var oldv=f[v];
                     TmpMin=min(oldu,oldv);
                     oldu=af[u].read();
                     if oldu>TmpMin {
                           af[u].compareAndSwap(oldu,TmpMin);
                           count+=1;
                     }
                     oldv=af[v].read();
                     if oldv>TmpMin {
                           af[v].compareAndSwap(oldv,TmpMin);
                           count+=1;
                     }
                  }//end if       
                }//end of forall
                forall x in f.localSubdomain()  with (ref f)  {
                     f[x]=af[x].read();    
                }
              }
            }

            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);

            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
          }
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);

      return f;
    }





    // distance=1;
    proc cc_1e(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var count1:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      var srcD=src;
      var dstD=dst;
      if (numLocales>1 && MultiLocale==1) {
           coforall loc in Locales with (ref af)  {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count,ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref localf) {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = srcD[x];
                                        var v = dstD[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(fu,fv);
                                        var oldx=localf[u].read();
                                        if (oldx>TmpMin) {
                                              localf[u].write(TmpMin);
                                              lcount+=1;
                                              dstD[x]=TmpMin;
                                        } else {
                                            oldx=localf[v].read();
                                            if (oldx>TmpMin) {
                                                  localf[v].write(TmpMin);
                                                  lcount+=1;
                                                  srcD[x]=TmpMin;
                                            }
                                        }

                                }
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count, ref af) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count) {
                 f[i]=af[i].read();
           }
      } else {
      // Initialize f and f_low in distributed memory.
          coforall loc in Locales with (ref f) {
            on loc {
              var vertexBegin = f.localSubdomain().lowBound;
              var vertexEnd = f.localSubdomain().highBound;
              forall i in vertexBegin..vertexEnd  with (ref f){
                f[i] = i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <f[i] ) {
                         f[i]=tmpv;
                    }
                }
              }
            }
          }  

          while(!converged) {
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count, ref f) {
              on loc {
  
                forall x in src.localSubdomain()  with ( + reduce count, ref f)  {
                  var u = srcD[x];
                  var v = dstD[x];
                  {
                     var TmpMin:int;
                     TmpMin=min(f[u],f[v]);
                     if(TmpMin < f[u]) {
                        f[u] = TmpMin;
                        count+=1;
                        dstD[x]=TmpMin;

                     } else {
                         if(TmpMin < f[v]) {
                            f[v] = TmpMin;
                            count+=1;
                            srcD[x]=TmpMin;               
                         }
                     }
                  }//end if       
                }//end of forall
              }
            }

            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);

            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
          }
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);

      return f;
    }






    // distance=2;
    proc cc_2(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref af)  {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(localf[fu].read(),localf[fv].read());
                                        var oldx=localf[u].read();
                                        while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[v].read();
                                        while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  v=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[fu].read();
                                        while (oldx>TmpMin) {
                                              if (localf[fu].compareAndSwap(oldx,TmpMin)) {
                                                  fu=oldx;
                                              }
                                              oldx=localf[fu].read();
                                              lcount+=1;
                                        }


                                        oldx=localf[fv].read();
                                        while (oldx>TmpMin) {
                                              if (localf[fv].compareAndSwap(oldx,TmpMin)) {
                                                  fv=oldx;
                                              }
                                              oldx=localf[fv].read();
                                              lcount+=1;
                                        }


                                }// forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }

      } else {

      // Initialize f and f_low in distributed memory.

          coforall loc in Locales with (ref f){
            on loc {
              forall i in f.localSubdomain()  {
                f[i] = i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <f[i] ) {
                         f[i]=tmpv;
                    }
                }
              }
            }
          }


          while(!converged) {
            var count:int=0;
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count,ref f ) {
              on loc {
                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;

                forall x in edgeBegin..edgeEnd  with ( + reduce count )  {
                  var u = src[x];
                  var v = dst[x];

                  var TmpMin:int;
                  if (itera==1) {
                         TmpMin=min(u,v);
                  } else {
                    TmpMin=min(f[f[u]],f[f[v]]);
                  }
                  if(TmpMin < f[f[u]]) {
                         f[f[u]] = TmpMin;
                  }
                  if(TmpMin < f[f[v]]) {
                         f[f[v]] = TmpMin;
                  }
                  if(TmpMin < f[u]) {
                    f[u] = TmpMin;
                  }
                  if(TmpMin < f[v]) {
                    f[v] = TmpMin;
                  }
                }//end of forall
                forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
                  var u = src[x];
                  var v = dst[x];
                  if (count==0) {
                        if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                            count=1;
                        } 
                  }
                }
              }
            }



            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
            }
            itera += 1;
          }
      }
      writeln("Number of iterations = ", itera-1);

      return f;
    }


    // distance=2;
    proc cc_2_atomic(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref af)  {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(localf[fu].read(),localf[fv].read());
                                        var oldx=localf[u].read();
                                        while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[v].read();
                                        while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  v=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[fu].read();
                                        while (oldx>TmpMin) {
                                              if (localf[fu].compareAndSwap(oldx,TmpMin)) {
                                                  fu=oldx;
                                              }
                                              oldx=localf[fu].read();
                                              lcount+=1;
                                        }


                                        oldx=localf[fv].read();
                                        while (oldx>TmpMin) {
                                              if (localf[fv].compareAndSwap(oldx,TmpMin)) {
                                                  fv=oldx;
                                              }
                                              oldx=localf[fv].read();
                                              lcount+=1;
                                        }


                                }// forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }

      } else {

      // Initialize f and f_low in distributed memory.

          coforall loc in Locales with (ref af){
            on loc {
              forall i in af.localSubdomain() {
                af[i].write(i);
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         af[i].write(tmpv);
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <af[i].read() ) {
                         af[i].write(tmpv);
                    }
                }
              }
            }
          }


          while(!converged) {
            var count:int=0;
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count,ref af ) {
              on loc {

                forall x in src.localSubdomain()  with ( + reduce count, ref af )  {
                  var u = src[x];
                  var v = dst[x];

                  var fu=af[u].read();
                  var fv=af[v].read();
                  var gu=af[fu].read();
                  var gv=af[fv].read();
                  var TmpMin=min(gu,gv);
                  if (gu>TmpMin) {
                     af[fu].compareAndSwap(gu,TmpMin);
                  }
                  if (gv>TmpMin) {
                     af[fv].compareAndSwap(gv,TmpMin);
                  }
                  if (fu>TmpMin) {
                     af[u].compareAndSwap(fu,TmpMin);
                  }
                  if (fv>TmpMin) {
                     af[v].compareAndSwap(fv,TmpMin);
                  }

                }//end of forall
                forall x in src.localSubdomain() with ( + reduce count)  {
                  var u = src[x];
                  var v = dst[x];
                  if (count==0) {
                        if (af[u].read()!=af[af[u].read()].read() || 
                            af[v].read()!=af[af[v].read()].read() || 
                            af[af[u].read()].read()!=af[af[v].read()].read()) {
                            count=1;
                        } 
                  }
                }
              }
            }



            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
            }
            itera += 1;
          }
      }
      writeln("Number of iterations = ", itera-1);

      coforall loc in Locales with ( ref f) {
              on loc {
                forall x in f.localSubdomain()  with (ref f)  {
                     f[x]=af[x].read();    
                }
              }
      }
      return f;
    }


    // distance=2;
    proc cc_2_assign(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref af)  {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(localf[fu].read(),localf[fv].read());
                                        var oldx=localf[u].read();
                                        while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[v].read();
                                        while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  v=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[fu].read();
                                        while (oldx>TmpMin) {
                                              if (localf[fu].compareAndSwap(oldx,TmpMin)) {
                                                  fu=oldx;
                                              }
                                              oldx=localf[fu].read();
                                              lcount+=1;
                                        }


                                        oldx=localf[fv].read();
                                        while (oldx>TmpMin) {
                                              if (localf[fv].compareAndSwap(oldx,TmpMin)) {
                                                  fv=oldx;
                                              }
                                              oldx=localf[fv].read();
                                              lcount+=1;
                                        }


                                }// forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }

      } else {

      // Initialize f and f_low in distributed memory.

          coforall loc in Locales with (ref af){
            on loc {
              forall i in af.localSubdomain() {
                af[i].write(i);
                f[i]=i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         af[i].write(tmpv);
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <af[i].read() ) {
                         af[i].write(tmpv);
                         f[i]=tmpv;
                    }
                }
              }
            }
          }


          while(!converged) {
            var count:int=0;
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count,ref af ) {
              on loc {

                forall x in src.localSubdomain()  with ( + reduce count, ref af )  {
                  var u = src[x];
                  var v = dst[x];

                  var fu=f[u];
                  var fv=f[v];
                  var gu=f[fu];
                  var gv=f[fv];
                  var TmpMin=min(gu,gv);
                  gu=af[fu].read();
                  if (gu>TmpMin) {
                     af[fu].compareAndSwap(gu,TmpMin);
                  }
                  gv=af[fv].read();
                  if (gv>TmpMin) {
                     af[fv].compareAndSwap(gv,TmpMin);
                  }
                  fu=af[u].read();
                  if (fu>TmpMin) {
                     af[u].compareAndSwap(fu,TmpMin);
                  }
                  fv=af[v].read();
                  if (fv>TmpMin) {
                     af[v].compareAndSwap(fv,TmpMin);
                  }

                }//end of forall
                forall x in src.localSubdomain() with ( + reduce count)  {
                  var u = src[x];
                  var v = dst[x];
                  if (count==0) {
                        if (af[u].read()!=af[af[u].read()].read() || 
                            af[v].read()!=af[af[v].read()].read() || 
                            af[af[u].read()].read()!=af[af[v].read()].read()) {
                            count=1;
                        } 
                  }
                }

                forall x in f.localSubdomain()  with (ref f)  {
                     f[x]=af[x].read();    
                }



              }
            }



            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
            }
            itera += 1;
          }
      }
      writeln("Number of iterations = ", itera-1);

      return f;
    }




    // distance=2;
    proc cc_2e(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      var srcD=src;
      var dstD=dst;
      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref af)  {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = srcD[x];
                                        var v = dstD[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(localf[fu].read(),localf[fv].read());
                                        if TmpMin<localf[fu].read() {
                                                  dstD[x]=TmpMin;
                                        } else {
                                              srcD[x]=TmpMin;
                                        }
                                        var oldx=localf[fu].read();
                                        if (oldx>TmpMin) {
                                              localf[fu].write(TmpMin);
                                              lcount+=1;
                                        } else {
                                            oldx=localf[fv].read();
                                            if (oldx>TmpMin) {
                                              localf[fv].write(TmpMin);
                                              lcount+=1;
                                            }
                                        }
                                        if (fu>TmpMin ) {
                                              localf[u].write(TmpMin);
                                              lcount+=1;
                                        } else {
                                            if (fv>TmpMin) {
                                              localf[v].write(TmpMin);
                                              lcount+=1;
                                            }
                                        }


                                }// forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while
           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }

      } else {

      // Initialize f and f_low in distributed memory.

          coforall loc in Locales with (ref f){
            on loc {
              var vertexBegin = f.localSubdomain().lowBound;
              var vertexEnd = f.localSubdomain().highBound;
              forall i in vertexBegin..vertexEnd {
                f[i] = i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <f[i] ) {
                         f[i]=tmpv;
                    }
                }
              }
            }
          }


          while(!converged) {
            var count:int=0;
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count,ref f ) {
              on loc {

                forall x in srcD.localSubdomain()   with ( + reduce count )  {
                  var u = srcD[x];
                  var v = dstD[x];

                  var TmpMin:int;
                  if (itera==1) {
                         TmpMin=min(u,v);
                  } else {
                    TmpMin=min(f[f[u]],f[f[v]]);
                  }
                  if(TmpMin < f[f[u]]) {
                             dstD[x] = TmpMin;
                  } else {
                             srcD[x] = TmpMin;
                  } 
                  if(TmpMin < f[f[u]]) {
                         f[f[u]] = TmpMin;
                  }
                  if(TmpMin < f[f[v]]) {
                         f[f[v]] = TmpMin;
                  }
                  if(TmpMin < f[u]) {
                    f[u] = TmpMin;
                  }
                  if(TmpMin < f[v]) {
                    f[v] = TmpMin;
                  }
                }//end of forall
                forall  x in srcD.localSubdomain()  with ( + reduce count)  {
                  var u = srcD[x];
                  var v = dstD[x];
                  if (count==0) {
                        if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                            count=1;
                        } 
                  }
                }
              }
            }



            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
            }
            itera += 1;
          }
      }
      writeln("Number of iterations = ", itera-1);

      return f;
    }




    // Contour variant: a  mapping based connected components algorithm
    proc cc_mm(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
              on loc {
                forall i in f.localSubdomain()  with (ref af){
                  af[i].write(i);
                }
              }
           }

           if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
           }else {
                ORDERH=1024;
           }  
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count , ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in src.localSubdomain() with ( + reduce lcount)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    var TmpMin:int;

                                    var fu=find_split_atomic_h(u,localf,ORDERH);
                                    var fv=find_split_atomic_h(v,localf,ORDERH);
                                    TmpMin=min(fu,fv);
                                    if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                                        var myx=u;
                                        var lastx=u;
                                        while (f[myx] >TmpMin ) {
                                            lastx=f[myx];
                                            f[myx]=TmpMin;
                                            myx=lastx;
                                            lcount+=1;
                                        }
                                        myx=v;
                                        while (f[myx] >TmpMin ) {
                                            lastx=f[myx];
                                            f[myx]=TmpMin;
                                            myx=lastx;
                                            lcount+=1;
                                        }
                                    }
                                    /* 
                                    var oldx=localf[u].read();
                                    while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                    }
                                    oldx=localf[v].read();
                                    while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                    }
                                    */
                   
                                }//end of forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);


           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {


          coforall loc in Locales with (ref f)  {
            on loc {
              forall i in f.localSubdomain() {
                f[i] = i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <f[i] ) {
                         f[i]=tmpv;
                    }
                }
              }
            }
          }
    
    

          if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
          }else {
               ORDERH=1024;
          }  
          //we first check with order=1 mapping method
          while( (!converged) ) {
            // In the second step, we employ high order mapping
            localtimer.clear();
            localtimer.start(); 




            if (ORDERH==2) {
                coforall loc in Locales with ( + reduce count, ref f ) {
                  on loc {

                    forall x in src.localSubdomain()   with ( + reduce count)  {
                      var u = src[x];
                      var v = dst[x];

                      var TmpMin:int;

                      TmpMin=min(f[f[u]],f[f[v]]);
                      if(TmpMin < f[f[u]]) {
                         f[f[u]] = TmpMin;
                      }
                      if(TmpMin < f[f[v]]) {
                         f[f[v]] = TmpMin;
                      }
                      if(TmpMin < f[u]) {
                        f[u] = TmpMin;
                      }
                      if(TmpMin < f[v]) {
                        f[v] = TmpMin;
                      }
                    }//end of forall
                    forall x in src.localSubdomain()  with ( + reduce count)  {
                      var u = src[x];
                      var v = dst[x];
                      if (count==0) {
                            if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                                count=1;
                            } 
                      }
                    }
                  }// end of on loc 
                }// end of coforall loc 
            } else {
                coforall loc in Locales with ( + reduce count, ref f) {
                  on loc {
                    var edgeBegin = src.localSubdomain().lowBound;
                    var edgeEnd = src.localSubdomain().highBound;
    
                    forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
                      var u = src[x];
                      var v = dst[x];
    
                      var TmpMin:int;
                      if (itera==1) {
                          TmpMin=min(u,v);
                      } else{
                          TmpMin=min(find_split_h(u,f,ORDERH),find_split_h(v,f,ORDERH));
                      }
                      if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                          var myx=u;
                          var lastx=u;
                          while (f[myx] >TmpMin ) {
                              lastx=f[myx];
                              f[myx]=TmpMin;
                              myx=lastx;
                          }
                          myx=v;
                          while (f[myx] >TmpMin ) {
                              lastx=f[myx];
                              f[myx]=TmpMin;
                              myx=lastx;
                          }
                      }
                  
                    }//end of forall

                    forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
                      var u = src[x];
                      var v = dst[x];
                      if (count==0) {
                        if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                            count=1;
                        }     
                      }
                    }
                  }// end of on loc 
                }// end of coforall loc 

            }


            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
            //writeln("My Order is ",ORDERH); 
            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }

      }
      writeln("Number of iterations = ", itera-1);

      return f;
    }



    // Contour variant: a  mapping based connected components algorithm
    proc cc_mm_atomic(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
              on loc {
                forall i in f.localSubdomain()  with (ref af){
                  af[i].write(i);
                }
              }
           }

           if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
           }else {
                ORDERH=1024;
           }  
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count , ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in src.localSubdomain() with ( + reduce lcount)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    var TmpMin:int;

                                    var fu=find_split_atomic_h(u,localf,ORDERH);
                                    var fv=find_split_atomic_h(v,localf,ORDERH);
                                    TmpMin=min(fu,fv);
                                    if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                                        var myx=u;
                                        var lastx=u;
                                        while (f[myx] >TmpMin ) {
                                            lastx=f[myx];
                                            f[myx]=TmpMin;
                                            myx=lastx;
                                            lcount+=1;
                                        }
                                        myx=v;
                                        while (f[myx] >TmpMin ) {
                                            lastx=f[myx];
                                            f[myx]=TmpMin;
                                            myx=lastx;
                                            lcount+=1;
                                        }
                                    }
                                    /* 
                                    var oldx=localf[u].read();
                                    while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                    }
                                    oldx=localf[v].read();
                                    while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                    }
                                    */
                   
                                }//end of forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);


           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {


          coforall loc in Locales with (ref af)  {
            on loc {
              forall i in af.localSubdomain() {
                af[i].write(i);
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         af[i].write(tmpv);
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <af[i].read() ) {
                         af[i].write(tmpv);
                    }
                }
              }
            }
          }
    
    

          if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
          }else {
               ORDERH=1024;
          }  
          //we first check with order=1 mapping method
          while( (!converged) ) {
            // In the second step, we employ high order mapping
            localtimer.clear();
            localtimer.start(); 




            if (ORDERH==2) {



                coforall loc in Locales with ( + reduce count,ref af ) {
                  on loc {

                    forall x in src.localSubdomain()  with ( + reduce count, ref af )  {
                      var u = src[x];
                      var v = dst[x];

                      var fu=af[u].read();
                      var fv=af[v].read();
                      var gu=af[fu].read();
                      var gv=af[fv].read();
                      var TmpMin=min(gu,gv);
                      if (gu>TmpMin) {
                         af[fu].compareAndSwap(gu,TmpMin);
                      }
                      if (gv>TmpMin) {
                         af[fv].compareAndSwap(gv,TmpMin);
                      }
                      if (fv>TmpMin) {
                         af[v].compareAndSwap(fv,TmpMin);
                      }
                      if (fu>TmpMin) {
                         af[u].compareAndSwap(fu,TmpMin);
                      }

                    }//end of forall
                    forall x in src.localSubdomain() with ( + reduce count, ref af)  {
                      var u = src[x];
                      var v = dst[x];
                      if (count==0) {
                            if (af[u].read()!=af[af[u].read()].read() || 
                                af[v].read()!=af[af[v].read()].read() || 
                                af[af[u].read()].read()!=af[af[v].read()].read()) {
                                count=1;
                            } 
                      }
                    }

                  }//on local
                }//coforall




            } else {
                coforall loc in Locales with ( + reduce count, ref af) {
                  on loc {
    
                    forall x in src.localSubdomain()   with ( + reduce count, ref af)  {
                      var u = src[x];
                      var v = dst[x];
    
                      var hu=find_naive_atomic_h(u,af,ORDERH);
                      var hv=find_naive_atomic_h(v,af,ORDERH);
                      var TmpMin=min(hu,hv);
                      if ( (af[u].read()!=TmpMin) || (af[v].read()!=TmpMin)) {
                          var myx=u;
                          var lastx=u;
                          while (af[myx].read() >TmpMin ) {
                              lastx=af[myx].read();
                              af[myx].compareAndSwap(lastx,TmpMin);
                              myx=lastx;
                          }
                          myx=v;
                          while (af[myx].read() >TmpMin ) {
                              lastx=af[myx].read();
                              af[myx].compareAndSwap(lastx,TmpMin);
                              myx=lastx;
                          }
                      }
                  
                    }//end of forall

                    forall x in src.localSubdomain()  with ( + reduce count, ref af)  {
                      var u = src[x];
                      var v = dst[x];
                      if (count==0) {
                        if (af[u].read()!=af[af[u].read()].read() || 
                            af[v].read()!=af[af[v].read()].read() || 
                            af[af[u].read()].read()!=af[af[v].read()].read()) {
                            count=1;
                        }     
                      }
                    }
                  }// end of on loc 
                }// end of coforall loc 

            }


            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
            //writeln("My Order is ",ORDERH); 
            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }

      }
      writeln("Number of iterations = ", itera-1);
      coforall loc in Locales with ( ref f) {
              on loc {
                forall x in f.localSubdomain()  with (ref f)  {
                     f[x]=af[x].read();    
                }
              }
      }

      return f;
    }




    // Contour variant: a  mapping based connected components algorithm
    proc cc_mm_assign(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
              on loc {
                forall i in f.localSubdomain()  with (ref af){
                  af[i].write(i);
                }
              }
           }

           if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
           }else {
                ORDERH=1024;
           }  
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count , ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in src.localSubdomain() with ( + reduce lcount)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    var TmpMin:int;

                                    var fu=find_split_atomic_h(u,localf,ORDERH);
                                    var fv=find_split_atomic_h(v,localf,ORDERH);
                                    TmpMin=min(fu,fv);
                                    if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                                        var myx=u;
                                        var lastx=u;
                                        while (f[myx] >TmpMin ) {
                                            lastx=f[myx];
                                            f[myx]=TmpMin;
                                            myx=lastx;
                                            lcount+=1;
                                        }
                                        myx=v;
                                        while (f[myx] >TmpMin ) {
                                            lastx=f[myx];
                                            f[myx]=TmpMin;
                                            myx=lastx;
                                            lcount+=1;
                                        }
                                    }
                                    /* 
                                    var oldx=localf[u].read();
                                    while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                    }
                                    oldx=localf[v].read();
                                    while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                    }
                                    */
                   
                                }//end of forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);


           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {


          coforall loc in Locales with (ref af)  {
            on loc {
              forall i in af.localSubdomain() {
                af[i].write(i);
                f[i]=i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         af[i].write(tmpv);
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <af[i].read() ) {
                         af[i].write(tmpv);
                         f[i]=tmpv;
                    }
                }
              }
            }
          }
    
    

          if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
          }else {
               ORDERH=1024;
          }  
          //we first check with order=1 mapping method
          while( (!converged) ) {
            // In the second step, we employ high order mapping
            localtimer.clear();
            localtimer.start(); 




            if (ORDERH==2) {



                coforall loc in Locales with ( + reduce count,ref af ) {
                  on loc {

                    forall x in src.localSubdomain()  with ( + reduce count, ref af )  {
                      var u = src[x];
                      var v = dst[x];

                      var fu=f[u];
                      var fv=f[v];
                      var gu=f[fu];
                      var gv=f[fv];
                      var TmpMin=min(gu,gv);
                      gu=af[fu].read();
                      if (gu>TmpMin) {
                         af[fu].compareAndSwap(gu,TmpMin);
                      }
                      gv=af[fv].read();
                      if (gv>TmpMin) {
                         af[fv].compareAndSwap(gv,TmpMin);
                      }
                      fv=af[v].read();
                      if (fv>TmpMin) {
                         af[v].compareAndSwap(fv,TmpMin);
                      }
                      fu=af[u].read();
                      if (fu>TmpMin) {
                         af[u].compareAndSwap(fu,TmpMin);
                      }

                    }//end of forall
                    forall x in src.localSubdomain() with ( + reduce count, ref af)  {
                      var u = src[x];
                      var v = dst[x];
                      if (count==0) {
                            if (af[u].read()!=af[af[u].read()].read() || 
                                af[v].read()!=af[af[v].read()].read() || 
                                af[af[u].read()].read()!=af[af[v].read()].read()) {
                                count=1;
                            } 
                      }
                    }
                    forall x in f.localSubdomain()  with (ref f)  {
                         f[x]=af[x].read();    
                    }

                  }//on local
                }//coforall




            } else {
                coforall loc in Locales with ( + reduce count, ref af) {
                  on loc {
    
                    forall x in src.localSubdomain()   with ( + reduce count, ref af)  {
                      var u = src[x];
                      var v = dst[x];
    
                      var hu=find_naive_h(u,f,ORDERH);
                      var hv=find_naive_h(v,f,ORDERH);
                      var TmpMin=min(hu,hv);
                      if ( (af[u].read()!=TmpMin) || (af[v].read()!=TmpMin)) {
                          var myx=u;
                          var lastx=u;
                          while (af[myx].read() >TmpMin ) {
                              lastx=af[myx].read();
                              af[myx].compareAndSwap(lastx,TmpMin);
                              myx=lastx;
                          }
                          myx=v;
                          while (af[myx].read() >TmpMin ) {
                              lastx=af[myx].read();
                              af[myx].compareAndSwap(lastx,TmpMin);
                              myx=lastx;
                          }
                      }
                  
                    }//end of forall

                    forall x in src.localSubdomain()  with ( + reduce count, ref af)  {
                      var u = src[x];
                      var v = dst[x];
                      if (count==0) {
                        if (af[u].read()!=af[af[u].read()].read() || 
                            af[v].read()!=af[af[v].read()].read() || 
                            af[af[u].read()].read()!=af[af[v].read()].read()) {
                            count=1;
                        }     
                      }
                    }

                    forall x in f.localSubdomain()  with (ref f)  {
                        f[x]=af[x].read();    
                    }


                  }// end of on loc 
                }// end of coforall loc 

            }


            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
            //writeln("My Order is ",ORDERH); 
            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }

      }
      writeln("Number of iterations = ", itera-1);

      return f;
    }










    // Contour variant: a  mapping based connected components algorithm
    proc cc_mme(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      var srcD=src;
      var dstD=dst;

      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
              on loc {
                forall i in f.localSubdomain()  with (ref af){
                  af[i].write(i);
                }
              }
           }

           if (Ne/here.numPUs() < LargeScale) {
                ORDERH=2;
           }else {
                ORDERH=1024;
           }  
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count , ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in srcD.localSubdomain() with ( + reduce lcount)  {
                                    var u = srcD[x];
                                    var v = dstD[x];
                                    var TmpMin:int;

                                    var fu=find_split_atomic_h(u,localf,ORDERH);
                                    var fv=find_split_atomic_h(v,localf,ORDERH);
                                    TmpMin=min(fu,fv);
                                    var oldx=localf[u].read();
                                    if ( (localf[u].read()!=TmpMin) || (localf[v].read()!=TmpMin)) {
                                        var myx=u;
                                        var lastx=u;
                                        while (localf[myx].read() >TmpMin ) {
                                            lastx=localf[myx].read();
                                            localf[myx].write(TmpMin);
                                            myx=lastx;
                                            lcount+=1;
                                        }
                                        myx=v;
                                        while (localf[myx].read() >TmpMin ) {
                                            lastx=localf[myx].read();
                                            localf[myx].write(TmpMin);
                                            myx=lastx;
                                            lcount+=1;
                                        }
                                    }
                                    if (fu>TmpMin && fv==TmpMin) {
                                              dstD[x]=TmpMin;
                                    } else {
                                        if fv>TmpMin {
                                              srcD[x]=TmpMin;
                                        }
                                    }
                                    /*
                                    if (oldx>TmpMin) {
                                              localf[u].write(TmpMin);
                                              lcount+=1;
                                              dstD[x]=TmpMin;
                                    }
                                    oldx=localf[v].read();
                                    if (oldx>TmpMin) {
                                              localf[v].write(TmpMin);
                                              lcount+=1;
                                              srcD[x]=TmpMin;
                                    }
                                    */
                   
                                }//end of forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);


           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {


          coforall loc in Locales with (ref f)  {
            on loc {
              forall i in f.localSubdomain() {
                f[i] = i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <f[i] ) {
                         f[i]=tmpv;
                    }
                }
              }
            }
          }
    
    

          if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
          }else {
               ORDERH=1024;
          }  
          //we first check with order=1 mapping method
          while( (!converged) ) {
            // In the second step, we employ high order mapping
            localtimer.clear();
            localtimer.start(); 




            if (ORDERH==2) {
                coforall loc in Locales with ( + reduce count, ref f ) {
                  on loc {

                    forall x in src.localSubdomain()  with ( + reduce count)  {
                      var u = srcD[x];
                      var v = dstD[x];

                      var TmpMin:int;

                      TmpMin=min(f[f[u]],f[f[v]]);
                      if(TmpMin < f[f[u]]) {
                         f[f[u]] = TmpMin;
                         if TmpMin==f[f[v]] {
                             dstD[x] = TmpMin;
                         }
                      }
                      if(TmpMin < f[f[v]]) {
                         f[f[v]] = TmpMin;
                         srcD[x] = TmpMin;
                      }
                      if(TmpMin < f[u]) {
                        f[u] = TmpMin;
                      }
                      if(TmpMin < f[v]) {
                        f[v] = TmpMin;
                      }
                    }//end of forall
                    forall x in srcD.localSubdomain()  with ( + reduce count)  {
                      var u = srcD[x];
                      var v = dstD[x];
                      if (count==0) {
                            if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                                count=1;
                            } 
                      }
                    }
                  }// end of on loc 
                }// end of coforall loc 
            } else {
                coforall loc in Locales with ( + reduce count, ref f) {
                  on loc {
    
                    forall x in srcD.localSubdomain()   with ( + reduce count, ref f)  {
                      var u = srcD[x];
                      var v = dstD[x];
                      var fu=u;
                      var fv=v;
                      var TmpMin:int;
                      if (itera==1) {
                          TmpMin=min(u,v);
                      } else{
                          fu=find_split_h(u,f,ORDERH);
                          fv=find_split_h(v,f,ORDERH);
                          //TmpMin=min(find_split_h(u,f,ORDERH),find_split_h(v,f,ORDERH));
                          TmpMin=min(fu,fv);
                      }
                      if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                          var myx=u;
                          var lastx=u;
                          while (f[myx] >TmpMin ) {
                              lastx=f[myx];
                              f[myx]=TmpMin;
                              myx=lastx;
                          }
                          myx=v;
                          while (f[myx] >TmpMin ) {
                              lastx=f[myx];
                              f[myx]=TmpMin;
                              myx=lastx;
                          }
                          if f[v]>TmpMin && fu==TmpMin {
                              srcD[x] = TmpMin;
                          } else {
                              if f[u]>TmpMin {
                                  dstD[x] = TmpMin;
                              }
                          }
                      }
                  
                    }//end of forall

                    forall x in srcD.localSubdomain() with ( + reduce count)  {
                      var u = srcD[x];
                      var v = dstD[x];
                      if (count==0) {
                        if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                            count=1;
                        }     
                      }
                    }
                  }// end of on loc 
                }// end of coforall loc 

            }


            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
            //writeln("My Order is ",ORDERH); 
            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }

      }
      writeln("Number of iterations = ", itera-1);

      return f;
    }


    // Contour variant: a  mapping based connected components algorithm
    proc cc_11mm(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv,atomic int); 
      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;


      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
              on loc {
                forall i in f.localSubdomain() with (ref af) {
                  af[i].write(i);
                }
              }
           }

           if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
           }else {
                ORDERH=1024;
           }  
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged && litera<FirstOrderIters) {

                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(fu,fv);
                                        var oldx=localf[u].read();
                                        while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[v].read();
                                        while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }
                   
                                }
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             while (!lconverged) {

                                forall x in src.localSubdomain()   with ( + reduce lcount)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    var TmpMin:int;

                                    var fu=find_split_atomic_h(u,localf,ORDERH);
                                    var fv=find_split_atomic_h(v,localf,ORDERH);
                                    TmpMin=min(fu,fv);
                                    var oldx=localf[u].read();
                                    while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                    }
                                    oldx=localf[v].read();
                                    while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                    }
                   
                                }//end of forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);


           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {

          localtimer.clear();
          localtimer.start(); 
          coforall loc in Locales with (ref f) {
            on loc {
              var vertexBegin = f.localSubdomain().lowBound;
              var vertexEnd = f.localSubdomain().highBound;
              forall i in vertexBegin..vertexEnd {
                f[i] = i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <f[i] ) {
                         f[i]=tmpv;
                    }
                }
              }
            }
          }



          //we first check with order=1 mapping method
          localtimer.stop(); 
          var executime=localtimer.elapsed();
          var myefficiency:real =(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
          while( (!converged) && 
                 (itera<FirstOrderIters) && 
                 ( (Ne/here.numPUs() < LargeScale) || (itera==1) || (myefficiency>LargeEdgeEfficiency)) ) {
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count, ref f) {
              on loc {
                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;

                forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
                  var u = src[x];
                  var v = dst[x];

                         var TmpMin:int;
                         TmpMin=min(f[u],f[v]);
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count=count+1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count=count+1;
                         }
                  
                }//end of forall
              }
            }


            itera += 1;
            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            //writeln("My Order is 1"); 
            localtimer.stop(); 
            executime=localtimer.elapsed();
            //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }

          if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
          }else {
               ORDERH=1024;
          }  
          // In the second step, we employ high order mapping
          while(!converged) {
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count, ref f ) {
              on loc {
                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;

                forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
                  var u = src[x];
                  var v = dst[x];

                  var TmpMin:int;
                  if (itera==1) {
                      TmpMin=min(u,v);
                  } else{
                      TmpMin=min(find_split_h(u,f,ORDERH),find_split_h(v,f,ORDERH));
                  }
                  if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                      var myx=u;
                      var lastx=u;
                      while (f[myx] >TmpMin ) {
                          lastx=f[myx];
                          f[myx]=TmpMin;
                          myx=lastx;
                      }
                      myx=v;
                      while (f[myx] >TmpMin ) {
                          lastx=f[myx];
                          f[myx]=TmpMin;
                          myx=lastx;
                      }
                  }
                  
                }//end of forall
                forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
                  var u = src[x];
                  var v = dst[x];
                  if (count==0) {
                        if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                            count=1;
                        } 
                  }
                }
              }
            }


            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
            //writeln("My Order is ",ORDERH); 
            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }
      }

      writeln("Number of iterations = ", itera-1);

      return f;
    }






    // Contour variant: a  mapping based connected components algorithm
    proc cc_1m1m(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv,atomic int); 

      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;


      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
              on loc {
                forall i in f.localSubdomain()  with (ref af){
                  af[i].write(i);
                }
              }
           }

           if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
           }else {
                ORDERH=1024;
           }  
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count ,ref af) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged ) {

                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(fu,fv);
                                        var oldx=localf[u].read();
                                        while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[v].read();
                                        while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }
                                }

                                forall x in src.localSubdomain()   with ( + reduce lcount)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    var TmpMin:int;

                                    var fu=find_split_atomic_h(u,localf,ORDERH);
                                    var fv=find_split_atomic_h(v,localf,ORDERH);
                                    TmpMin=min(fu,fv);
                                    var oldx=localf[u].read();
                                    while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                    }
                                    oldx=localf[v].read();
                                    while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                    }
                   
                                }//end of forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {





      coforall loc in Locales with (ref f) {
        on loc {
          forall i in f.localSubdomain()  with (ref f){
            f[i] = i;
            if (nei[i] >0) {
                var tmpv=dst[start_i[i]];
                if ( tmpv <i ) {
                     f[i]=tmpv;
                }
            }
            if (neiR[i] >0) {
                var tmpv=dstR[start_iR[i]];
                if ( tmpv <f[i] ) {
                     f[i]=tmpv;
                }
            }
          }
        }
      }



      if (Ne/here.numPUs() < LargeScale) {
           ORDERH=2;
      }else {
           ORDERH=1024;
      }  
      //we first check with order=1 mapping method
      while( (!converged) ) {
        localtimer.clear();
        localtimer.start(); 
        coforall loc in Locales with ( + reduce count, ref f) {
          on loc {

            forall x in src.localSubdomain()   with ( + reduce count, ref f)  {
              var u = src[x];
              var v = dst[x];

                         var TmpMin:int;
                         TmpMin=min(f[u],f[v]);
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count=count+1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count=count+1;
                         }
                  
            }//end of forall
          }
        }


        itera += 1;
        //writeln("My Order is 1"); 
        localtimer.stop(); 
        executime=localtimer.elapsed();
        myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
        if( (count==0) ) {
          converged = true;
          continue;
        }
        else {
          converged = false;
        }

        // In the second step, we employ high order mapping
        localtimer.clear();
        localtimer.start(); 
        if (ORDERH==2) {
            coforall loc in Locales with ( + reduce count, ref f ) {
              on loc {

                forall x in src.localSubdomain()  with ( + reduce count, ref f)  {
                  var u = src[x];
                  var v = dst[x];

                  var TmpMin:int;

                  TmpMin=min(f[f[u]],f[f[v]]);
                  if(TmpMin < f[f[u]]) {
                     f[f[u]] = TmpMin;
                  }
                  if(TmpMin < f[f[v]]) {
                     f[f[v]] = TmpMin;
                  }
                  if(TmpMin < f[u]) {
                    f[u] = TmpMin;
                  }
                  if(TmpMin < f[v]) {
                    f[v] = TmpMin;
                  }
                }//end of forall
                forall x in src.localSubdomain()  with ( + reduce count, ref f)  {
                  var u = src[x];
                  var v = dst[x];
                  if (count==0) {
                        if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                            count=1;
                        } 
                  }
                }
              }// end of on loc 
            }// end of coforall loc 
        } else {
            coforall loc in Locales with ( + reduce count, ref f ) {
              on loc {

                forall x in src.localSubdomain()  with ( + reduce count, ref f)  {
                  var u = src[x];
                  var v = dst[x];

                  var TmpMin:int;
                  if (itera==1) {
                      TmpMin=min(u,v);
                  } else{
                      TmpMin=min(find_split_h(u,f,ORDERH),find_split_h(v,f,ORDERH));
                  }
                  if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                      var myx=u;
                      var lastx=u;
                      while (f[myx] >TmpMin ) {
                          lastx=f[myx];
                          f[myx]=TmpMin;
                          myx=lastx;
                      }
                      myx=v;
                      while (f[myx] >TmpMin ) {
                          lastx=f[myx];
                          f[myx]=TmpMin;
                          myx=lastx;
                      }
                  }
                  
                }//end of forall

                forall x in src.localSubdomain()  with ( + reduce count, ref f)  {
                  var u = src[x];
                  var v = dst[x];
                  if (count==0) {
                    if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                        count=1;
                    } 
                  }
                }
              }// end of on loc 
            }// end of coforall loc 

        }


        if( (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
          count=0;
        }
        itera += 1;
        //writeln("My Order is ",ORDERH); 
        localtimer.stop(); 
        executime=localtimer.elapsed();
        myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
      }
      }


      writeln("Number of iterations = ", itera-1);

      return f;
    }


    proc cc_syn(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var f_low = makeDistArray(Nv, int); 

      var count:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      var converged:bool=false;
      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af, ref f)  {
                on loc {
                    forall i in f.localSubdomain()  with (ref af, ref f) {
                         af[i].write(i);
                         f[i]=i;
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                             var localf:[0..Nv-1]  int;
                             var localfu:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 localf[i]=af[i].read();
                                 localfu[i].write(localf[i]);
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u];
                                        var fv=localf[v];
                                        TmpMin=min(localf[fu],localf[fv]);
                                        var oldx=localfu[u].read();
                                        while (oldx>TmpMin) {
                                              if (localfu[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localfu[u].read();
                                              lcount+=1;
                                        }
                                        oldx=localfu[v].read();
                                        while (oldx>TmpMin) {
                                              if (localfu[v].compareAndSwap(oldx,TmpMin)) {
                                                  v=oldx;
                                              }
                                              oldx=localfu[v].read();
                                              lcount+=1;
                                        }
                                        oldx=localfu[fu].read();
                                        while (oldx>TmpMin) {
                                              if (localfu[fu].compareAndSwap(oldx,TmpMin)) {
                                                  fu=oldx;
                                              }
                                              oldx=localfu[fu].read();
                                              lcount+=1;
                                        }


                                        oldx=localfu[fv].read();
                                        while (oldx>TmpMin) {
                                              if (localfu[fv].compareAndSwap(oldx,TmpMin)) {
                                                  fv=oldx;
                                              }
                                              oldx=localfu[fv].read();
                                              lcount+=1;
                                        }

                                }//forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                    forall i in 0..Nv-1 {
                                        localf[i]=localfu[i].read();
                                    }
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localfu[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {

      coforall loc in Locales with (ref f, ref f_low) {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd  with (ref f, ref f_low){
            f[i] = i;
            f_low[i] = i;
            if (nei[i] >0) {
                var tmpv=dst[start_i[i]];
                if ( tmpv <i ) {
                     f[i]=tmpv;
                     f_low[i]=tmpv;
                }
            }
            if (neiR[i] >0) {
                var tmpv=dstR[start_iR[i]];
                if ( tmpv <f[i] ) {
                     f[i]=tmpv;
                     f_low[i]=tmpv;
                }
            }
          }
        }
      }


      while(!converged) {
        localtimer.clear();
        localtimer.start();

        var count1:int=0;
        coforall loc in Locales with ( + reduce count, ref f_low  ) {
          on loc {

            forall x in src.localSubdomain()   with ( + reduce count)  {
              var u = src[x];
              var v = dst[x];

              var TmpMin:int;
                  {
                     TmpMin=min(f[f[u]],f[f[v]]);
                     if(TmpMin < f_low[f[u]]) {
                         f_low[f[u]] = TmpMin;
                         count+=1;
                     }
                     if(TmpMin < f_low[f[v]]) {
                         f_low[f[v]] = TmpMin;
                         count+=1;
                     }
                     if(TmpMin < f_low[u]) {
                         f_low[u] = TmpMin;
                         count+=1;
                     }
                     if(TmpMin < f_low[v]) {
                         f_low[v] = TmpMin;
                         count+=1;
                     }
                  } 
            }//end of forall
          }
        }
        f=f_low;


        if( (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
          count=0;
        }
        itera += 1;
        localtimer.stop();
        executime=localtimer.elapsed();
        myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);

      }
      }
      writeln("Number of iterations = ", itera-1);

      return f;
    }



    // the atomic method for union find implementation
    proc cc_connectit(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var f_low = makeDistArray(Nv, atomic int); 
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      // Initialize f and f_low in distributed memory.
      coforall loc in Locales  with (ref af, ref f, ref f_low){
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd with (ref af, ref f, ref f_low) {
            f_low[i].write(i);
            f[i]=i;
            af[i].write(i);
          }
        }
      }


      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var count1:int=0;


      if (numLocales>1 && MultiLocale==1) {

           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                                var localf_low:[0..Nv-1] atomic int;
                                var lconverged:bool = false;
                                var litera = 1;
                                var lcount:int=0;
                                forall i in 0..Nv-1 {
                                    localf_low[i].write(af[i].read());
                                }

                                forall x in src.localSubdomain()    {
                                    var u = src[x];
                                    var v = dst[x];
                                    unite_atomic(u,v,localf_low);
                                }
                                forall x in src.localSubdomain()    {
                                     var u = src[x];
                                     var v = dst[x];
                                     var l=find_naive_atomic(u,localf_low);
                                     var oldx=localf_low[u].read();
                                     while (oldx>l) {
                                           if (localf_low[u].compareAndSwap(oldx,l)) {
                                               u=oldx;
                                           }
                                           oldx=localf_low[u].read();
                                     }
                                     //l=find_naive_atomic(v,localf_low);
                                     oldx=localf_low[v].read();
                                     while (oldx>l) {
                                           if (localf_low[v].compareAndSwap(oldx,l)) {
                                               v=oldx;
                                           }
                                           oldx=localf_low[v].read();
                                     }

                                }//end of forall

                                writeln("Converge local ------------------------------------------");
                                forall i in 0..Nv-1 with (+ reduce count) {
                                    var old=af[i].read();
                                    var newval=localf_low[i].read();
                                    while old>newval {
                                        af[i].compareAndSwap(old,newval);
                                        old=af[i].read();
                                        count+=1;
                                    }
                                }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {

      {
        coforall loc in Locales with ( + reduce count, + reduce count1, ref f_low) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd    {
              var u = src[x];
              var v = dst[x];

              unite_atomic(u,v,f_low);
            }
            forall x in edgeBegin..edgeEnd    {
              var u = src[x];
              var v = dst[x];
              var l=find_naive_atomic(u,f_low);
              var oldx=f_low[u].read();
              while (oldx>l) {
                    if (f_low[u].compareAndSwap(oldx,l)) {
                        u=oldx;
                    }
                    oldx=f_low[u].read();
              }
              //l=find_naive_atomic(v,f_low);
              oldx=f_low[v].read();
              while (oldx>l) {
                    if (f_low[v].compareAndSwap(oldx,l)) {
                        v=oldx;
                    }
                    oldx=f_low[v].read();
              }

            }//end of forall
          }
        }
        
      }


      itera+=1;
      coforall loc in Locales with (ref f) {
        on loc {
          forall i in f.localSubdomain() {
            f[i] = f_low[i].read();
          }
        }
      }
      }

      writeln("Number of iterations = ", itera-1);
      return f;
    }





    // UPS: Paul's min update, label propogation and symmetrization method
    proc cc_ups(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var l = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var src2 = makeDistArray(Ne*2, int); 
      var dst2 = makeDistArray(Ne*2, int); 
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      var lu = makeDistArray(Nv, atomic int); 

      localtimer.clear();
      localtimer.start(); 
      coforall loc in Locales with (ref l, ref lu, ref af) {
        on loc {
          var vertexBegin = l.localSubdomain().lowBound;
          var vertexEnd = l.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd  with (ref l, ref lu, ref af){
            l[i] = i;
            lu[i].write(l[i]);
            af[i].write(l[i]);
          }
        }
      }
      var count:int=0;
      
      coforall loc in Locales with (ref src2, ref dst2) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;
            forall x in src.localSubdomain()  with (ref src2, ref dst2){
                  src2[x*2]=src[x];
                  dst2[x*2]=dst[x];
                  src2[x*2+1]=dst[x];
                  dst2[x*2+1]=src[x];
            }


          }
      }

      localtimer.stop(); 
      //executime=localtimer.elapsed();
      //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;

      var converged:bool = false;
      var itera = 1;

      if (numLocales>1 && MultiLocale==1) {
           while (!converged)  {
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref src2, ref dst2, ref af ) {
                     on loc {
                             var locall:[0..Nv-1] int;
                             var locallu:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 locall[i]=af[i].read();
                                 locallu[i].write(locall[i]);
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                    var u = src2[2*x];
                                    var v = dst2[2*x];
                                    if (v!=locall[u]) {
                                        var old=locallu[v].read();
                                        var tmp =min(old,locall[u]);
                                        while (old>tmp) {
                                          locallu[v].compareAndSwap(old,tmp);
                                          old=locallu[v].read();
                                          lcount+=1;
                                        }
                                        src2[2*x]=v;
                                        dst2[2*x]=locall[u];
                                    } else {
                                        src2[2*x]=v;
                                        dst2[2*x]=u;
                                    }


                                    u = src2[2*x+1];
                                    v = dst2[2*x+1];
                                    if (v!=locall[u]) {
                                        var old=locallu[v].read();
                                        var tmp =min(old,locall[u]);
                                        while (old>tmp) {
                                          locallu[v].compareAndSwap(old,tmp);
                                          old=locallu[v].read();
                                          lcount+=1;
                                        }
                                        src2[2*x+1]=v;
                                        dst2[2*x+1]=locall[u];
                                    } else {
                                        src2[2*x+1]=v;
                                        dst2[2*x+1]=u;
                                    }
                                    //writeln("2 Myid=",here.id," <",u,",",v,">-><",src2[2*x+1],",",dst2[2*x+1],">", " L[",u,"]=",locall[u]," L[",v,"]=",locall[v], " Lu[",v,"]=",locallu[v].read());

                                }//end forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                    forall x in 0..Nv-1    {
                                         var val=locallu[x].read();
                                         if locall[x]>val {
                                             locall[x]=val;
                                         }
                                    }
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=locall[i];
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    l[i]=af[i].read();
           }
      } else {


          while (!converged) {
                localtimer.clear();
                localtimer.start(); 
                coforall loc in Locales with ( + reduce count, ref lu, ref src2, ref dst2) {
                  on loc {

                    forall x in src.localSubdomain()  with ( + reduce count)  {
                      var u = src2[2*x];
                      var v = dst2[2*x];
                      if (v!=l[u]) {
                          var old=lu[v].read();
                          var tmp =min(old,l[u]);
                          while (old>tmp) {
                            lu[v].compareAndSwap(old,tmp);
                            old=lu[v].read();
                            count+=1;
                          }
                          src2[2*x]=v;
                          dst2[2*x]=l[u];         
                      } else {
                          src2[2*x]=v;
                          dst2[2*x]=u;         
                      }
                      u = src2[2*x+1];
                      v = dst2[2*x+1];
                      if (v!=l[u]) {
                          src2[2*x+1]=v;
                          dst2[2*x+1]=l[u];         
                          var old=lu[v].read();
                          var tmp =min(old,l[u]);
                          while (old>tmp) {
                            lu[v].compareAndSwap(old,tmp);
                            old=lu[v].read();
                            count+=1;
                          }
                      } else {
                          src2[2*x+1]=v;
                          dst2[2*x+1]=u;         
                      }

                    }//end of forall
                  }//loc
                }//coforall


                if( (count==0) ) {
                  converged = true;
                }
                else {
                  converged = false;
                  count=0;
                  coforall loc in Locales with ( + reduce count, ref l) {
                    on loc {
                        forall x in l.localSubdomain() with (ref l) {
                           l[x]=lu[x].read();
                        }
                    }
                  }
                }
                itera += 1;
                localtimer.stop(); 
                executime=localtimer.elapsed();
                //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
                //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }//while
      }//else


      writeln("Number of iterations = ", itera-1);

      return l;
    }





    // UP: variant of Paul's UPS without S
    proc cc_up(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var l = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var src2 = makeDistArray(Ne*2, int); 
      var dst2 = makeDistArray(Ne*2, int); 
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      //var lu = makeDistArray(Nv, atomic int); 
      var lu=l;
      localtimer.clear();
      localtimer.start(); 
      coforall loc in Locales with (ref l, ref lu, ref af) {
      //coforall loc in Locales with (ref l, ref af) {
        on loc {
          var vertexBegin = l.localSubdomain().lowBound;
          var vertexEnd = l.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd  with (ref l, ref lu, ref af){
          //forall i in vertexBegin..vertexEnd  with (ref l, ref af){
            l[i] = i;
            lu[i]=i;
            af[i].write(l[i]);
          }
        }
      }
      var count:int=0;
      
      coforall loc in Locales with (ref src2, ref dst2) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;
            forall x in src.localSubdomain()  with (ref src2, ref dst2){
                  src2[x*2]=src[x];
                  dst2[x*2]=dst[x];
                  src2[x*2+1]=dst[x];
                  dst2[x*2+1]=src[x];
            }


          }
      }

      localtimer.stop(); 
      //executime=localtimer.elapsed();
      //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;

      var converged:bool = false;
      var itera = 1;

      if (numLocales>1 && MultiLocale==1) {
           while (!converged)  {
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref src2, ref dst2, ref af ) {
                     on loc {
                             var locall:[0..Nv-1] int;
                             //var locallu:[0..Nv-1] atomic int;
                             var n_locallu:[0..Nv-1] int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 locall[i]=af[i].read();
                                 //locallu[i].write(locall[i]);
                                 n_locallu[i]=locall[i];
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                    var u = src2[2*x];
                                    var v = dst2[2*x];
                                    if (v!=locall[u]) {
                                        //var old=locallu[v].read();
                                        var old=n_locallu[v];
                                        var tmp =min(old,locall[u]);
                                        //while (old>tmp) {
                                        if (old>tmp) {
                                          //locallu[v].compareAndSwap(old,tmp);
                                          n_locallu[v]=tmp;
                                          //old=locallu[v].read();
                                          lcount+=1;
                                        }
                                        src2[2*x]=v;
                                        dst2[2*x]=locall[u];
                                    } else {
                                        //var tmp=locallu[v].read();
                                        var tmp=n_locallu[v];
                                        var old =v;
                                        //while (old>tmp) {
                                        if (old>tmp) {
                                          //locallu[u].compareAndSwap(old,tmp);
                                          n_locallu[u]=tmp;
                                          //old=locallu[u].read();
                                          lcount+=1;
                                        }
                                        src2[2*x]=tmp;
                                        dst2[2*x]=u;
                                    }


                                    u = src2[2*x+1];
                                    v = dst2[2*x+1];
                                    if (v!=locall[u]) {
                                        //var old=locallu[v].read();
                                        var old=n_locallu[v];
                                        var tmp =min(old,locall[u]);
                                        //while (old>tmp) {
                                        if (old>tmp) {
                                          //locallu[v].compareAndSwap(old,tmp);
                                          n_locallu[v]=tmp;
                                          //old=locallu[v].read();
                                          lcount+=1;
                                        }
                                        src2[2*x+1]=v;
                                        dst2[2*x+1]=locall[u];
                                    } else {
                                        //var tmp=locallu[v].read();
                                        var tmp=n_locallu[v];
                                        var old =v;
                                        //while (old>tmp) {
                                        if  (old>tmp) {
                                          //locallu[u].compareAndSwap(old,tmp);
                                          n_locallu[u]=tmp;
                                          //old=locallu[u].read();
                                          lcount+=1;
                                        }
                                        src2[2*x+1]=tmp;

                                        //src2[2*x+1]=v;
                                        dst2[2*x+1]=u;
                                    }
                                    //writeln("2 Myid=",here.id," <",u,",",v,">-><",src2[2*x+1],",",dst2[2*x+1],">", " L[",u,"]=",locall[u]," L[",v,"]=",locall[v], " Lu[",v,"]=",locallu[v].read());

                                }//end forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                    forall x in 0..Nv-1    {
                                         //var val=locallu[x].read();
                                         var val=n_locallu[x];
                                         if locall[x]>val {
                                             locall[x]=val;
                                         }
                                    }
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=locall[i];
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    l[i]=af[i].read();
           }
      } else {


          while (!converged) {
                localtimer.clear();
                localtimer.start(); 
                coforall loc in Locales with ( + reduce count, ref lu, ref src2, ref dst2) {
                //coforall loc in Locales with ( + reduce count,  ref src2, ref dst2) {
                  on loc {

                    forall x in src.localSubdomain()  with ( + reduce count)  {
                      var u = src2[2*x];
                      var v = dst2[2*x];
                      if (v!=l[u]) {
                          //var old=lu[v].read();
                          var old=lu[v];
                          var tmp =min(old,l[u]);
                          //while (old>tmp) {
                          if (old>tmp) {
                            lu[v]=tmp;
                            //old=lu[v].read();
                            count+=1;
                          }
                          src2[2*x]=v;
                          dst2[2*x]=l[u];         
                      } else {
                          //var tmp=lu[v].read();
                          var tmp=lu[v];
                          var old =v;
                          //while (old>tmp) {
                          if (old>tmp) {
                            //lu[u].compareAndSwap(old,tmp);
                            lu[u]=tmp;
                            //old=lu[u].read();
                            count+=1;
                          }
                          src2[2*x]=tmp;
                          //src2[2*x]=v;
                          dst2[2*x]=u;         
                      }
                      u = src2[2*x+1];
                      v = dst2[2*x+1];
                      if (v!=l[u]) {
                          src2[2*x+1]=v;
                          dst2[2*x+1]=l[u];         
                          //var old=lu[v].read();
                          var old=lu[v];
                          var tmp =min(old,l[u]);
                          //while (old>tmp) {
                          if (old>tmp) {
                            //lu[v].compareAndSwap(old,tmp);
                            lu[v]=tmp;
                            //old=lu[v].read();
                            count+=1;
                          }
                      } else {
                          //var tmp=lu[v].read();
                          var tmp=lu[v];
                          var old =v;
                          //while (old>tmp) {
                          if (old>tmp) {
                            //lu[u].compareAndSwap(old,tmp);
                            lu[u]=tmp;
                            //old=lu[u].read();
                            count+=1;
                          }
                          src2[2*x+1]=tmp;
                          //src2[2*x+1]=v;
                          dst2[2*x+1]=u;         
                      }

                    }//end of forall
                  }//loc
                }//coforall


                if( (count==0) ) {
                  converged = true;
                }
                else {
                  converged = false;
                  count=0;
                  coforall loc in Locales with ( + reduce count, ref l) {
                    on loc {
                        forall x in l.localSubdomain() with (ref l) {
                           if l[x]>lu[x] {
                               l[x]=lu[x];
                           }
                        }
                    }
                  }
                }
                itera += 1;
                localtimer.stop(); 
                executime=localtimer.elapsed();
                //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
                //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }//while
      }//else


      writeln("Number of iterations = ", itera-1);

      return l;
    }




    // UPS Asyn: variant of Paul's UPS without atomic update
    proc cc_ups_asyn(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var l = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var src2 = makeDistArray(Ne*2, int); 
      var dst2 = makeDistArray(Ne*2, int); 
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      //var lu = makeDistArray(Nv, atomic int); 
      var lu=l;
      localtimer.clear();
      localtimer.start(); 
      coforall loc in Locales with (ref l, ref lu, ref af) {
      //coforall loc in Locales with (ref l, ref af) {
        on loc {
          var vertexBegin = l.localSubdomain().lowBound;
          var vertexEnd = l.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd  with (ref l, ref lu, ref af){
          //forall i in vertexBegin..vertexEnd  with (ref l, ref af){
            l[i] = i;
            lu[i]=i;
            af[i].write(l[i]);
          }
        }
      }
      var count:int=0;
      
      coforall loc in Locales with (ref src2, ref dst2) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;
            forall x in src.localSubdomain()  with (ref src2, ref dst2){
                  src2[x*2]=src[x];
                  dst2[x*2]=dst[x];
                  src2[x*2+1]=dst[x];
                  dst2[x*2+1]=src[x];
            }


          }
      }

      localtimer.stop(); 
      //executime=localtimer.elapsed();
      //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;

      var converged:bool = false;
      var itera = 1;

      if (numLocales>1 && MultiLocale==1) {
           while (!converged)  {
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref src2, ref dst2, ref af ) {
                     on loc {
                             var locall:[0..Nv-1] int;
                             //var locallu:[0..Nv-1] atomic int;
                             var n_locallu:[0..Nv-1] int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 locall[i]=af[i].read();
                                 //locallu[i].write(locall[i]);
                                 n_locallu[i]=locall[i];
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                    var u = src2[2*x];
                                    var v = dst2[2*x];
                                    if (v!=locall[u]) {
                                        //var old=locallu[v].read();
                                        var old=n_locallu[v];
                                        var tmp =min(old,locall[u]);
                                        //while (old>tmp) {
                                        if (old>tmp) {
                                          //locallu[v].compareAndSwap(old,tmp);
                                          n_locallu[v]=tmp;
                                          //old=locallu[v].read();
                                          lcount+=1;
                                        }
                                        src2[2*x]=v;
                                        dst2[2*x]=locall[u];
                                    } else {
                                        src2[2*x]=v;
                                        dst2[2*x]=u;
                                    }


                                    u = src2[2*x+1];
                                    v = dst2[2*x+1];
                                    if (v!=locall[u]) {
                                        //var old=locallu[v].read();
                                        var old=n_locallu[v];
                                        var tmp =min(old,locall[u]);
                                        //while (old>tmp) {
                                        if (old>tmp) {
                                          //locallu[v].compareAndSwap(old,tmp);
                                          n_locallu[v]=tmp;
                                          //old=locallu[v].read();
                                          lcount+=1;
                                        }
                                        src2[2*x+1]=v;
                                        dst2[2*x+1]=locall[u];
                                    } else {
                                        src2[2*x+1]=v;
                                        dst2[2*x+1]=u;
                                    }
                                    //writeln("2 Myid=",here.id," <",u,",",v,">-><",src2[2*x+1],",",dst2[2*x+1],">", " L[",u,"]=",locall[u]," L[",v,"]=",locall[v], " Lu[",v,"]=",locallu[v].read());

                                }//end forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                    forall x in 0..Nv-1    {
                                         //var val=locallu[x].read();
                                         var val=n_locallu[x];
                                         if locall[x]>val {
                                             locall[x]=val;
                                         }
                                    }
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=locall[i];
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);

           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    l[i]=af[i].read();
           }
      } else {


          while (!converged) {
                localtimer.clear();
                localtimer.start(); 
                coforall loc in Locales with ( + reduce count, ref lu, ref src2, ref dst2) {
                //coforall loc in Locales with ( + reduce count,  ref src2, ref dst2) {
                  on loc {

                    forall x in src.localSubdomain()  with ( + reduce count)  {
                      var u = src2[2*x];
                      var v = dst2[2*x];
                      if (v!=l[u]) {
                          //var old=lu[v].read();
                          var old=lu[v];
                          var tmp =min(old,l[u]);
                          //while (old>tmp) {
                          if (old>tmp) {
                            lu[v]=tmp;
                            //old=lu[v].read();
                            count+=1;
                          }
                          src2[2*x]=v;
                          dst2[2*x]=l[u];         
                      } else {
                          src2[2*x]=v;
                          dst2[2*x]=u;         
                      }
                      u = src2[2*x+1];
                      v = dst2[2*x+1];
                      if (v!=l[u]) {
                          src2[2*x+1]=v;
                          dst2[2*x+1]=l[u];         
                          //var old=lu[v].read();
                          var old=lu[v];
                          var tmp =min(old,l[u]);
                          //while (old>tmp) {
                          if (old>tmp) {
                            //lu[v].compareAndSwap(old,tmp);
                            lu[v]=tmp;
                            //old=lu[v].read();
                            count+=1;
                          }
                      } else {
                          src2[2*x+1]=v;
                          dst2[2*x+1]=u;         
                      }

                    }//end of forall
                  }//loc
                }//coforall


                if( (count==0) ) {
                  converged = true;
                }
                else {
                  converged = false;
                  count=0;
                  coforall loc in Locales with ( + reduce count, ref l) {
                    on loc {
                        forall x in l.localSubdomain() with (ref l) {
                           if l[x]>lu[x] {
                               l[x]=lu[x];
                           }
                        }
                    }
                  }
                }
                itera += 1;
                localtimer.stop(); 
                executime=localtimer.elapsed();
                //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
                //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }//while
      }//else


      writeln("Number of iterations = ", itera-1);

      return l;
    }



    var timer:stopwatch;
    // We only care for undirected graphs, they can be weighted or unweighted. 
    var f1 = makeDistArray(Nv, int);
    var f2 = makeDistArray(Nv, int);
    var f3 = makeDistArray(Nv, int);
    var f4 = makeDistArray(Nv, int);
    var f5 = makeDistArray(Nv, int);
    var f6 = makeDistArray(Nv, int);
    var f7 = makeDistArray(Nv, int);
    var f8 = makeDistArray(Nv, int);
    var f9 = makeDistArray(Nv, int);
    var f10 = makeDistArray(Nv, int);
    var loopnum=5;
    if (Directed == 0) {

        timer.clear();
        timer.start(); 
        for i in 1..loopnum {
        f1 = cc_fast_sv_dist( toSymEntry(ag.getNEIGHBOR(), int).a, 
                                toSymEntry(ag.getSTART_IDX(), int).a, 
                                toSymEntry(ag.getSRC(), int).a, 
                                toSymEntry(ag.getDST(), int).a, 
                                toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                                toSymEntry(ag.getSTART_IDX_R(), int).a, 
                                toSymEntry(ag.getSRC_R(), int).a, 
                                toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fast sv dist cc: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);



        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f2 = cc_connectit(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for ConnectIt cc: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f3 = cc_1_assign(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs 1 cc assign: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);



        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f6 = cc_1_atomic(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs 1 cc atomic: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f4 = cc_2_assign(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs 2 cc assign: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f5 = cc_2_atomic(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs 2 atomic cc: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        /*
        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f6 = cc_1m1m(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs 1m1m cc: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        */



        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f7 = cc_mm_assign( toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs mm cc: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f8 = cc_mm_atomic( toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs mm atomic cc: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f9 = cc_up(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs up cc: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);


        timer.clear();
        timer.start();
        for i in 1..loopnum {
        f10 = cc_ups(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        }
        timer.stop(); 
        outMsg = "Time elapsed for fs ups cc: " + (timer.elapsed()/(1.0*loopnum)):string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        coforall loc in Locales {
          on loc {
            var vertexStart = f1.localSubdomain().lowBound;
            var vertexEnd = f1.localSubdomain().highBound;
            forall i in vertexStart..vertexEnd {
              if ((f1[i] != f2[i]) ) {
                var outMsg = "!!!!!f1<->f2 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f2[",i,"]=",f2[i]);
              }
              if ((f1[i] != f3[i]) ) {
                var outMsg = "!!!!!f1<->f3 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f3[",i,"]=",f3[i]);
              }
              if ( (f1[i]!=f4[i]) ) {
                var outMsg = "!!!!!f1<->f4 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f4[",i,"]=",f4[i]);
              }
              if ( (f1[i]!=f5[i]) ) {
                var outMsg = "!!!!!f1<->f5 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f5[",i,"]=",f5[i]);
              }
              if ( (f1[i]!=f6[i]) ) {
                var outMsg = "!!!!!f1<->f6 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f6[",i,"]=",f6[i]);
              }
              if ( (f1[i]!=f7[i]) ) {
                var outMsg = "!!!!!f1<->f7 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f7[",i,"]=",f7[i]);
              }
              if ( (f1[i]!=f8[i]) ) {
                var outMsg = "!!!!!f1<->f8 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f8[",i,"]=",f8[i]);
              }
              if ( (f1[i]!=f9[i]) ) {
                var outMsg = "!!!!!f1<->f9 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f9[",i,"]=",f9[i]);
              }
              if ( (f1[i]!=f10[i]) ) {
                var outMsg = "!!!!!f1<->f10 CONNECTED COMPONENT MISMATCH!!!!!";
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                writeln("f1[",i,"]=",f1[i]," f10[",i,"]=",f10[i]);
              }
            }
          }
        } 

    }
   

    // The message that is sent back to the Python front-end. 
    var comps = new set(int);
    for x in f2 {
      comps.add(x);
    }
    var num_comps = makeDistArray(numLocales, int); 
    num_comps[0] = comps.size;
    proc return_CC(ary:[?d] int): string throws {
      CCName = st.nextName();
      var CCEntry =createSymEntry (ary);
      st.addEntry(CCName, CCEntry);

      var CCMsg =  'created ' + st.attrib(CCName);
      return CCMsg;
    }

    var repMsg = return_CC(num_comps);
    return new MsgTuple(repMsg, MsgType.NORMAL);
  }

  use CommandMap;
  registerFunction("segmentedGraphCC", segCCMsg,getModuleName());
}




        /*
        f5=f1;
        f6=f1;

        if (ag.hasA_START_IDX()) {
                       timer.clear();
                       timer.start();
                       f5=cc_fs_aligned0(
                           toSymEntry(ag.getNEIGHBOR(), int).a,
                           toSymEntry(ag.getSTART_IDX(), int).a,
                           toSymEntry(ag.getSRC(), int).a,
                           toSymEntry(ag.getDST(), int).a,
                           toSymEntry(ag.getNEIGHBOR_R(), int).a,
                           toSymEntry(ag.getSTART_IDX_R(), int).a,
                           toSymEntry(ag.getSRC_R(), int).a,
                           toSymEntry(ag.getDST_R(), int).a,
                           toDomArraySymEntry(ag.getA_NEIGHBOR()).domary,
                           toDomArraySymEntry(ag.getA_START_IDX()).domary,
                           toDomArraySymEntry(ag.getA_NEIGHBOR_R()).domary,
                           toDomArraySymEntry(ag.getA_START_IDX_R()).domary,
                           toDomArraySymEntry(ag.getA_SRC_R()).domary,
                           toDomArraySymEntry(ag.getA_DST_R()).domary);
                       timer.stop();
                       outMsg = "Time elapsed for aligned0 fs cc: " + timer.elapsed():string;
                       smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                       timer.clear();
                       timer.start();
                       f6=cc_fs_aligned1(
                           toSymEntry(ag.getNEIGHBOR(), int).a,
                           toSymEntry(ag.getSTART_IDX(), int).a,
                           toSymEntry(ag.getSRC(), int).a,
                           toSymEntry(ag.getDST(), int).a,
                           toSymEntry(ag.getNEIGHBOR_R(), int).a,
                           toSymEntry(ag.getSTART_IDX_R(), int).a,
                           toSymEntry(ag.getSRC_R(), int).a,
                           toSymEntry(ag.getDST_R(), int).a,
                           toDomArraySymEntry(ag.getA_NEIGHBOR()).domary,
                           toDomArraySymEntry(ag.getA_START_IDX()).domary,
                           toDomArraySymEntry(ag.getA_NEIGHBOR_R()).domary,
                           toDomArraySymEntry(ag.getA_START_IDX_R()).domary,
                           toDomArraySymEntry(ag.getA_SRC_R()).domary,
                           toDomArraySymEntry(ag.getA_DST_R()).domary);
                       timer.stop();
                       outMsg = "Time elapsed for aligned1 fs cc: " + timer.elapsed():string;
                       smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        }
        */


/*


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
        var SetCurF = new distBag(int, Locales);
        var SetNextF = new distBag(int, Locales); 

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
                      
              //  TOP DOWN 
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
              //  BOTTOM UP 
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





    // BFS method
    proc cc_bfs(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws { 

      var f = makeDistArray(Nv, int); 
      var depth = makeDistArray(Nv, int); 
      // Change the visited array to all -1. 
      coforall loc in Locales {
        on loc {
          forall i in depth.localSubdomain() {
            depth[i] = -1; 
            f[i]=i;
          }
        }
      }



        // Current level starts at 0.
      var cur_level = 0; 
      var (unvisited,nextVertex) = depth.find(-1); 
      var component:int = 0; 

        var SetCurF = new distBag(int, Locales);
        var SetNextF = new distBag(int, Locales); 


        // Size of the current frontier. 
        var numCurF:int = 1; 

        // Top-down and bottom-up counters. 
        var topdown:int = 0; 
        var bottomup:int = 0; 

        // Make the depth array. 


        // The BFS loop for while the number of vertices in the current 
        // frontier is greater than 0. 
      while(unvisited) {
        cur_level = 0; 
        SetCurF.add(nextVertex); 
        depth[nextVertex]=cur_level;
        numCurF=1;
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

              var vertexBegin=src[edgeBegin];
              var vertexEnd=src[edgeEnd];
              var vertexBeginR=srcR[edgeBegin];
              var vertexEndR=srcR[edgeEnd];

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
              var LF = 1; 
                      
              {
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
                        visited[j] = component; 
                        SetNextF.add(j);
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
                        visited[j] = component; 
                        SetNextF.add(j);
                      }
                    }
                  }
                }//end forall
              } 
            }//end on loc
          }//end coforall loc
          cur_level+=1;
          numCurF=SetNextF.getSize();
          SetCurF<=>SetNextF;
          SetNextF.clear();
        }//end while  
        (unvisited,nextVertex)  = depth.find(-1);
        if (cur_level!=0) {
              writeln("Component=",component, " diameter=",cur_level, " unvisited=",unvisited," nextVertex=",nextVertex);
        }
        // Increase the component number to find the next component, if it exists.
        component += 1; 
      } // end outermost while


      writeln("Total Number of Component=",component);
      writeln("Number of iterations = 1");

      return f;
    }//end of  cc-bfs


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




    proc cc_fs_atomic_bidirection(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_low = makeDistArray(Nv, atomic int); 
      var f_up = makeDistArray(Nv, atomic int); 

      // Initialize f and f_low in distributed memory.
      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f_up[i].write(i);
            f_low[i].write(i);
            if (nei[i] >0) {
                var tmpv=dst[start_i[i]];
                if ( tmpv <i ) {
                     f_low[i].write(tmpv);
                }
                tmpv=dst[start_i[i]+nei[i]-1];
                if ( tmpv >i ) {
                     f_up[i].write(tmpv);
                }
            }
            if (neiR[i] >0) {
                var tmpv=dstR[start_iR[i]];
                if ( tmpv <f[i] ) {
                     f[i]=tmpv;
                     f_low[i].write(tmpv);
                }
                tmpv=dstR[start_iR[i]+neiR[i]-1];
                if ( tmpv >f_up[i].read() ) {
                     f_up[i].write(tmpv);
                }
            }
          }//forall
        }
      }

      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f[i] = f_low[i].read();
          }
        }
      }
      //writeln("After initial step.  f=",f);

      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f[i] = f_up[i].read();
          }
        }
      }
      //writeln("After initial step.  f_up=",f);

      var converged:bool = false;
      var itera = 1;
      while(!converged) {
        var count:int=0;
        var count1:int=0;
        coforall loc in Locales with ( + reduce count, + reduce count1) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with ( + reduce count,+ reduce count1)  {
              var u = src[x];
              var v = dst[x];


              if ((u!=0) || (v!=0)) {
              var TmpMin,TmpMax,upval1,lowval1,upval:int;
              TmpMin=min(f_low[u].read(),f_low[v].read());
              TmpMax=max(f_up[u].read(),f_up[v].read(),u,v);
              
              if ((itera % (JumpSteps*5) ==0) ) {
                     TmpMin=min(f_low[f_low[f_low[u].read()].read()].read(),f_low[f_low[f_low[v].read()].read()].read());
                     TmpMax=max(f_up[f_up[f_up[u].read()].read()].read(),f_up[f_up[f_up[v].read()].read()].read());
              } else {
                  if ((numLocales==1)|| (itera % JumpSteps ==0)) {
                     TmpMin=min(f_low[f_low[u].read()].read(),f_low[f_low[v].read()].read());
                     TmpMax=max(f_up[f_up[u].read()].read(),f_up[f_up[v].read()].read());
                  } 
              }
              if(TmpMin < f_low[u].read()) {
                f_low[u].write(TmpMin);
                count+=1;
                upval=f_up[u].read();
                if (upval>u) {
                    if TmpMin<f_low[upval].read(){
                        f_low[upval].write(TmpMin);
                        f_up[u].write(TmpMin);
                        count+=1;
                    } else {
                        if (TmpMax > upval) {
                            f_up[u].write(TmpMax);
                        }
                    }
                }

              }
              if(TmpMin < f_low[v].read()) {
                f_low[v].write(TmpMin);
                count+=1;
                upval=f_up[v].read();
                if (upval>v) {
                    if TmpMin<f_low[upval].read(){
                        f_low[upval].write(TmpMin);
                        f_up[u].write(TmpMin);
                        count+=1;
                    } else { 
                        if(TmpMax > upval) {
                            f_up[v].write(TmpMax);
                        }
                    }
                }
              }
              if ( (numLocales==1) || (itera % JumpSteps ==0)  || (itera < JumpSteps) ) {
                   if(TmpMin < f_low[f_low[u].read()].read()) {
                     f_low[f_low[u].read()].write(TmpMin);
                     count+=1;
                     upval=f_up[f_up[u].read()].read();
                     if upval>u {
                         if TmpMin<f_low[upval].read(){
                             f_low[upval].write(TmpMin);
                             f_up[upval].write(TmpMin);
                             count+=1;
                         } else {
                             if(TmpMax > upval) {
                                 f_up[f_up[u].read()].write(TmpMax);
                             }
                         }
                     }
                   }

                   if(TmpMin < f_low[f_low[v].read()].read()) {
                     f_low[f_low[v].read()].write(TmpMin);
                     count+=1;
                     upval=f_up[f_up[v].read()].read();
                     if upval>v {
                         if TmpMin<f_low[upval].read(){
                             f_low[upval].write(TmpMin);
                             f_up[upval].write(TmpMin);
                             count+=1;
                         } else {
                             if(TmpMax > upval) {
                                 f_up[f_up[v].read()].write(TmpMax);
                             }
                         }
                     }
                   }
              }
              if (  (itera % (5*JumpSteps) == 0) ) {
                   lowval1=f_low[f_low[u].read()].read();
                   if(TmpMin < f_low[lowval1].read() ) {
                     f_low[upval1].write(TmpMin);
                     count+=1;
                     upval1=f_up[f_up[u].read()].read();
                     upval=f_up[upval1].read();
                     if upval>u {
                         if TmpMin<f_low[upval].read(){
                             f_low[upval].write(TmpMin);
                             f_up[upval].write(TmpMin);
                             count+=1;
                         } else {
                             if(TmpMax > upval ) {
                                 f_up[upval1].write(TmpMax);
                             } 
                         }
                     }
                   }
                   lowval1=f_low[f_low[v].read()].read();
                   if(TmpMin < f_low[lowval1].read() ) {
                     f_low[lowval1].write(TmpMin);
                     count+=1;
                     upval1=f_up[f_up[v].read()].read();
                     upval=f_up[upval1].read();
                     if TmpMin<f_low[upval].read(){
                         f_low[upval].write(TmpMin);
                         f_up[upval].write(TmpMin);
                         count+=1;
                     } else {
                         if(TmpMax > upval) {
                             f_up[upval1].write(TmpMax);
                         }
                     }
                   }
              }
              }//end if 
            }//end of forall

          }
        }
        coforall loc in Locales  {
          on loc {
            var vertexBegin = f.localSubdomain().lowBound;
            var vertexEnd = f.localSubdomain().highBound;
               forall i in vertexBegin..vertexEnd {
                  f[i] = f_low[i].read();
               }
          }
        }
        //writeln("After iteration ", itera, " f=",f);

        coforall loc in Locales  {
          on loc {
              var vertexBegin = f.localSubdomain().lowBound;
              var vertexEnd = f.localSubdomain().highBound;
              forall i in vertexBegin..vertexEnd {
                f[i] = f_up[i].read();
              }
          }
        }
        //writeln("After iteration ", itera, " f_up=",f);


        //if( ((count1 == 0) && (numLocales==1)) || (count==0) ) {
        if( (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
        }
        itera += 1;
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);

      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f[i] = f_low[i].read();
          }
        }
      }
      return f;
    }





    // the atomic method is slower than the non atomic method. However, for large graphs, it seems the atomic method is good.
    proc cc_fs_atomic(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_low = makeDistArray(Nv, atomic int); 

      // Initialize f and f_low in distributed memory.
      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f_low[i].write(i);
            if (nei[i] >0) {
                var tmpv=dst[start_i[i]];
                if ( tmpv <i ) {
                     f_low[i].write(tmpv);
                }
            }
            if (neiR[i] >0) {
                var tmpv=dstR[start_iR[i]];
                if ( tmpv <f[i] ) {
                     f_low[i].write(tmpv);
                }
            }
          }
        }
      }


      var converged:bool = false;
      var itera = 1;



      while(!converged) {
        var count:int=0;
        var count1:int=0;
        coforall loc in Locales with ( + reduce count, + reduce count1) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with ( + reduce count,+ reduce count1)  {
              var u = src[x];
              var v = dst[x];


              var TmpMin:int;
              var oldval:int;

                  if (itera==1){
                     TmpMin=min(u,v);
                  } else {
                     TmpMin=find_atomic_split_h(u,f_low,ORDERH);
                     TmpMin=min(TmpMin,find_atomic_split_h(v,f_low,ORDERH));
                  }
                  if ( (f_low[u].read()!=TmpMin) || (f_low[v].read()!=TmpMin)) {
                      var myx=u;
                      while (f_low[myx].read() >TmpMin ) {
                          var lastx=f_low[myx].read();
                          f_low[myx].write(TmpMin);
                          myx=lastx;
                      }
                      myx=v;
                      while (f_low[myx].read() >TmpMin ) {
                          var lastx=f_low[myx].read();
                          f_low[myx].write(TmpMin);
                          myx=lastx;
                      }
                  }

            }//end of forall
            forall x in edgeBegin..edgeEnd  with ( + reduce count,+ reduce count1)  {
              var u = src[x];
              var v = dst[x];
              if (count==0) {
                    if (f_low[u].read()!=f_low[f_low[u].read()].read()  || 
                        f_low[v].read()!=f_low[f_low[v].read()].read()  || 
                        f_low[f_low[u].read()].read() !=f_low[f_low[v].read()].read()) {
                        count=1;
                    } 
              }
            }
          }
        }

        //writeln("After iteration ", itera," f=",f);
        
        if(  (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
        }
        itera += 1;
      }


      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);
      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f[i] = f_low[i].read();
          }
        }
      }

      return f;
    }





    // the atomic method is slower than the non atomic method. However, for large graphs, it seems the atomic method is good.
    proc cc_fs_cas(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_low = makeDistArray(Nv, atomic int); 

      // Initialize f and f_low in distributed memory.
      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f_low[i].write(i);
            if (nei[i] >0) {
                var tmpv=dst[start_i[i]];
                if ( tmpv <i ) {
                     f_low[i].write(tmpv);
                }
            }
            if (neiR[i] >0) {
                var tmpv=dstR[start_iR[i]];
                if ( tmpv <f[i] ) {
                     f_low[i].write(tmpv);
                }
            }
          }
        }
      }

      var converged:bool = false;
      var itera = 1;

      while(!converged) {
        var count:int=0;
        var count1:int=0;
        coforall loc in Locales with ( + reduce count, + reduce count1) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with ( + reduce count,+ reduce count1)  {
              var u = src[x];
              var v = dst[x];


              var TmpMin:int;
              var oldval:int;

                  if (itera==1){
                     TmpMin=min(u,v);
                  } else {
                     TmpMin=find_split_atomic_h(u,f_low,ORDERH);
                     TmpMin=min(TmpMin,find_split_atomic_h(v,f_low,ORDERH));
                  }
                  if ( (f_low[u].read()!=TmpMin) || (f_low[v].read()!=TmpMin)) {
                      var myx=u;
                      while (f_low[myx].read() >TmpMin ) {
                          var lastx=f_low[myx].read();
                          f_low[myx].compareAndSwap(lastx,TmpMin);
                          myx=lastx;
                          //if (count==0) {
                          //   count = 1;
                          //}
                      }
                      myx=v;
                      while (f_low[myx].read() >TmpMin ) {
                          var lastx=f_low[myx].read();
                          f_low[myx].compareAndSwap(lastx,TmpMin);
                          myx=lastx;
                          //if (count==0) {
                          //   count = 1;
                          //}
                      }
                  }

            }//end of forall
            forall x in edgeBegin..edgeEnd  with ( + reduce count,+ reduce count1)  {
              var u = src[x];
              var v = dst[x];
              if (count==0) {
                    if (f_low[u].read()!=f_low[f_low[u].read()].read()  || 
                        f_low[v].read()!=f_low[f_low[v].read()].read()  || 
                        f_low[f_low[u].read()].read() !=f_low[f_low[v].read()].read()) {
                        count=1;
                    } 
              }
            }
          }
        }

        //writeln("After iteration ", itera," f=",f);
        
        if(  (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
        }
        itera += 1;
      }

      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);
      coforall loc in Locales {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd {
            f[i] = f_low[i].read();
          }
        }
      }

      return f;
    }


    // FastSpread: a  propogation based connected components algorithm
    proc cc_fs_aligned0(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, 
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        a_nei:[?D21] DomArray, a_start_i:[?D22] DomArray,
                        a_neiR:[?D31] DomArray, a_start_iR:[?D32] DomArray,
                        a_srcR:[?D41] DomArray, a_dstR:[?D42] DomArray
                     ) throws {


      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_low = makeDistArray(Nv, int); 
      var f1=makeDistArray(numLocales,DomArray);
      var f1_next=makeDistArray(numLocales,DomArray);

      var gf = makeDistArray(Nv, int);
      var gf_low = makeDistArray(Nv, int);
      var dup = makeDistArray(Nv, int);
      var diff = makeDistArray(Nv, int);

      //writeln("D21=",D21," D41=",D41);
      coforall loc in Locales {
        on loc {
            f1[here.id].new_dom(a_nei[here.id].DO);
            f1_next[here.id].new_dom(a_nei[here.id].DO);
            //initialize the array

            forall i in a_nei[here.id].DO {
                 f1[here.id].A[i]=i;
                 f1_next[here.id].A[i]=i;
            }

            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;
            var vertexBegin = src[edgeBegin];
            var vertexEnd = src[edgeEnd];
            //writeln("ID=",here.id, " domain=",a_nei[here.id].DO);
            //writeln("ID=",here.id, " vertexBegin=",vertexBegin," vertexEnd=",vertexEnd);
            forall i in vertexBegin..vertexEnd {
                //writeln("ID=",here.id, " before check value f1[",here.id,"].A[",i,"]=",f1[here.id].A[i], " and f1_next[",here.id,"].A[",i,"]=",f1_next[here.id].A[i]);
                if (a_nei[here.id].A[i] >0) {
                    var tmpv=dst[a_start_i[here.id].A[i]];
                    if ( tmpv <i ) {
                         f1[here.id].A[i]=tmpv;
                         f1_next[here.id].A[i]=tmpv;
                    }
                }
                if (a_neiR[here.id].A[i] >0) {
                    var tmpv=dstR[a_start_iR[here.id].A[i]];
                    if ( tmpv <f1[here.id].A[i] ) {
                         f1[here.id].A[i]=tmpv;
                         f1_next[here.id].A[i]=tmpv;
                    }
                }
                //writeln("ID=",here.id, " after check value f1[",here.id,"].A[",i,"]=",f1[here.id].A[i], " and f1_next[",here.id,"].A[",i,"]=",f1_next[here.id].A[i]);
                //writeln("ID=",here.id, " after update");
            }

            // here we update the neighbor area with the same vertex ID
            if (here.id>0) {
                 if ( (a_nei[here.id-1].DO.highBound >=vertexBegin) && (a_nei[here.id-1].DO.lowBound <=vertexBegin)) {
                      if (f1[here.id-1].A[vertexBegin]>f1[here.id].A[vertexBegin]) {
                            f1[here.id-1].A[vertexBegin]=f1[here.id].A[vertexBegin];
                            f1_next[here.id-1].A[vertexBegin]=f1_next[here.id].A[vertexBegin];
                      }
                 }
            }
            if (here.id<numLocales-1) {
                 if ( (a_nei[here.id+1].DO.lowBound <=vertexEnd) && (a_nei[here.id+1].DO.highBound >=vertexEnd) ) {
                      if (f1[here.id+1].A[vertexEnd]>f1[here.id].A[vertexEnd]) {
                            f1[here.id+1].A[vertexEnd]=f1[here.id].A[vertexEnd];
                            f1_next[here.id+1].A[vertexEnd]=f1_next[here.id].A[vertexEnd];
                      }
                 }
            }
        }
      }



      var converged:bool = false;
      var itera = 1;
      while(!converged) {
        var count:int=0;
        var count1:int=0;
        coforall loc in Locales with ( + reduce count, + reduce count1) {
          on loc {
              var edgeBegin = src.localSubdomain().lowBound;
              var edgeEnd = src.localSubdomain().highBound;

              //writeln("ID=",here.id, " edgeBegin=",edgeBegin," edgeEnd=",edgeEnd);
              forall x in edgeBegin..edgeEnd  with ( + reduce count,+ reduce count1)  {
                  var u = src[x];
                  var v = dst[x];
                  var fu,fv,ffu,ffv,fffu,fffv:int;
                  var locu1,locv1,locu2,locv2,vid:int;

                  proc VertexToLocale(low:int,high:int,v:int):int {
                          if high<low {
                               return -1;
                          }
                          var mid=(low+high)/2;
                          if ( (a_nei[mid].DO.lowBound <=v ) && (a_nei[mid].DO.highBound >=v) ) {
                                return mid;
                          } else {
                               if (a_nei[mid].DO.lowBound > v) {
                                   return VertexToLocale(low,mid-1,v);
                               } else {
                                   return VertexToLocale(mid+1,high,v);
                               }
                          }
                  }
                  proc SearchVertexValue(v:int) :int {
                           if v<0 {
                                 return -1;
                           }
                           var curval:int;
                           var id=VertexToLocale(0,numLocales-1,v);
                           if (id!=-1) {
                                  curval=f1[id].A[v];
                           }
                           if (id>0) {
                                id=VertexToLocale(id-1,id-1,v);
                                if (id!=-1) {
                                    if (curval>f1[id].A[v] ) {
                                         curval=f1[id].A[v];
                                    }        
                                }
                           } else {
                               if (id <numLocales-1) {
                                    id=VertexToLocale(id+1,id+1,v);
                                    if (id!=-1) {
                                          if (curval>f1[id].A[v]) {
                                              curval=f1[id].A[v];
                                          }
                                    }

                               }
                           }
                           return curval;
 
                  }
                  proc UpdateValue(minval:int,v:int):bool {
                           var UpdateFlag:bool=false;
                           if v<0 {
                                 return UpdateFlag;
                           }
                           var curval:int;
                           var id=VertexToLocale(0,numLocales-1,v);
                           if (id!=-1) {
                               if (minval<f1_next[id].A[v] ) {
                                  f1_next[id].A[v]=minval;
                                  UpdateFlag=true;
                               }
                           }

                           if (id>0) {
                                while (id>0) {
                                    id=VertexToLocale(id-1,id-1,v);
                                    if (id!=-1) {
                                        if (minval<f1_next[id].A[v] ) {
                                             f1_next[id].A[v]=minval;
                                             UpdateFlag=true;
                                        }
                                    }
                                }
                           } else {
                               while ( (id <numLocales-1) && (id!=-1))  {
                                    id=VertexToLocale(id+1,id+1,v);
                                    if (id!=-1) {
                                          if (minval<f1_next[id].A[v]) {
                                              f1_next[id].A[v]=minval;
                                              UpdateFlag=true;
                                          }
                                    }

                               }
                           }

                           return UpdateFlag;
                  }

                  //var TmpMin=min(f[u],f[v],f[f[u]],f[f[v]],f[f[f[u]]],f[f[f[v]]]);
                  var TmpMin:int;
                  fu=f1[here.id].A[u];
                  fv=SearchVertexValue(v);
                  if ((numLocales ==1) || (itera % JumpSteps==0) ) {
                       //TmpMin=min(f[u],f[v],gf[u],gf[v]);
                       //TmpMin=min(f[u],f[v],gf[u],gf[v],gf[gf[u]],gf[gf[v]]);

                       ffu=SearchVertexValue(fu);
                       ffv=SearchVertexValue(fv);

                       fffu=SearchVertexValue(ffu);
                       fffv=SearchVertexValue(ffv);

                       TmpMin=min(fu,fv,ffu,ffv,fffu,fffv);
                  } else {
                         TmpMin=min(fu,fv);
                  }

                  //writeln("ID=",here.id, "fu,fv,ffu,ffv,fffu,fffv=",fu,fv,ffu,ffv,fffu,fffv);
                  //writeln("ID=",here.id, "flocu1,locv1,locu2,locv2=",locu1,locv1,locu2,locv2);
                  if(TmpMin < f1_next[here.id].A[u]) {
                      f1_next[here.id].A[u] = TmpMin;
                      count+=1;
                  }
                  if(UpdateValue(TmpMin,v) ) {
                      count+=1;
                  }
                  if ( (numLocales==1) || (itera % JumpSteps == 0) ) {
                   
                       if(UpdateValue(TmpMin,fu) ) {
                           count+=1;
                           count1+=1;
                       }
                       if(UpdateValue(TmpMin,fv)) {
                           count+=1;
                           count1+=1;
                       }
                       if( UpdateValue(TmpMin,ffu) ){
                           count+=1;
                       }
                       if( UpdateValue(TmpMin,ffv) ){
                           count+=1;
                       }
                  }
              }// end forall     
              var vertexBegin = a_nei[here.id].DO.lowBound;
              var vertexEnd = a_nei[here.id].DO.highBound;

              //writeln("ID=",here.id, " vertexBegin=",vertexBegin," vertexEnd=",vertexEnd);
              forall i in vertexBegin..vertexEnd {
                   f1[here.id].A[i]=f1_next[here.id].A[i];
              }

            }//end of loc
          }//end of coforall


          //if( ((count1 == 0) && (numLocales==1)) || (count==0) ) {
          if( (count==0) ) {
              converged = true;
          }
          else {
              converged = false;
          }
          itera += 1;
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);


      coforall loc in Locales {
        on loc {
          var vertexBegin = a_nei[here.id].DO.lowBound;
          var vertexEnd = a_nei[here.id].DO.highBound;
          forall i in vertexBegin..vertexEnd {
               f[i]=f1[here.id].A[i];
          }
       }
     }


      return f;
    }


    // there are unknow bugs in this version
    proc cc_fs_aligned1(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, 
                    start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        a_nei:[?D21] DomArray, a_start_i:[?D22] DomArray,
                        a_neiR:[?D31] DomArray, a_start_iR:[?D32] DomArray,
                        a_srcR:[?D41] DomArray, a_dstR:[?D42] DomArray 
                     ) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var f_low = makeDistArray(Nv, int); 
      var f1=makeDistArray(numLocales,DomArray);
      var f1_next=makeDistArray(numLocales,DomArray);
      var gf = makeDistArray(Nv, int);
      var gf_low = makeDistArray(Nv, int);
      var dup = makeDistArray(Nv, int);
      var diff = makeDistArray(Nv, int);

      //writeln("D21=",D21," D41=",D41);
      // Initialize f and f_low in distributed memory.

      proc VertexToLocale(low:int,high:int,v:int):int {
                          if high<low {
                               return -1;
                          }
                          var mid=(low+high)/2;
                          if ( (a_nei[mid].DO.lowBound <=v ) && (a_nei[mid].DO.highBound >=v) ) {
                                return mid;
                          } else {
                               if (a_nei[mid].DO.lowBound > v) {
                                   return VertexToLocale(low,mid-1,v);
                               } else {
                                   return VertexToLocale(mid+1,high,v);
                               }
                          }
      }


      proc SearchVertexValue(v:int) :int {
                           if v<0 {
                                 return -1;
                           }
                           var curval:int;
                           var id=VertexToLocale(0,numLocales-1,v);
                           if (id!=-1) {
                                  curval=f1[id].A[v];
                           }
                           if (id>0) {
                                id=VertexToLocale(id-1,id-1,v);
                                if (id!=-1) {
                                    if (curval>f1[id].A[v] ) {
                                         curval=f1[id].A[v];
                                    }        
                                }
                           } else {
                               if (id <numLocales-1) {
                                    id=VertexToLocale(id+1,id+1,v);
                                    if (id!=-1) {
                                          if (curval>f1[id].A[v]) {
                                              curval=f1[id].A[v];
                                          }
                                    }

                               }
                           }
                           return curval;
 
      }





      proc UpdateValue(minval:int,v:int):bool {
                           var UpdateFlag:bool=false;
                           if v<0 {
                                 return UpdateFlag;
                           }
                           var curval:int;
                           var id=VertexToLocale(0,numLocales-1,v);
                           if (id!=-1) {
                               if (minval<f1_next[id].A[v] ) {
                                  f1_next[id].A[v]=minval;
                                  UpdateFlag=true;
                               }
                           }

                           if (id>0) {
                                while (id>0) {
                                     id=VertexToLocale(id-1,id-1,v);
                                     if (id!=-1) {
                                         if (minval<f1_next[id].A[v] ) {
                                              f1_next[id].A[v]=minval;
                                              UpdateFlag=true;
                                         }
                                     }
                                }
                           } else {
                               while ((id <numLocales-1) && (id!=-1)) {
                                    id=VertexToLocale(id+1,id+1,v);
                                    if (id!=-1) {
                                          if (minval<f1_next[id].A[v]) {
                                              f1_next[id].A[v]=minval;
                                              UpdateFlag=true;
                                          }
                                    }

                               }
                           }

                           return UpdateFlag;
      }

      coforall loc in Locales {
        on loc {
            f1[here.id].new_dom(a_nei[here.id].DO);
            f1_next[here.id].new_dom(a_nei[here.id].DO);
            //initialize the array

            forall i in a_nei[here.id].DO {
                 f1[here.id].A[i]=i;
                 f1_next[here.id].A[i]=i;
            }

            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;
            var vertexBegin = src[edgeBegin];
            var vertexEnd = src[edgeEnd];
            //writeln("ID=",here.id, " domain=",a_nei[here.id].DO);
            //writeln("ID=",here.id, " vertexBegin=",vertexBegin," vertexEnd=",vertexEnd);
            forall i in vertexBegin..vertexEnd {
                //writeln("ID=",here.id, " before check value f1[",here.id,"].A[",i,"]=",f1[here.id].A[i], " and f1_next[",here.id,"].A[",i,"]=",f1_next[here.id].A[i]);
                if (a_nei[here.id].A[i] >0) {
                    var tmpv=dst[a_start_i[here.id].A[i]];
                    if ( tmpv <i ) {
                         f1[here.id].A[i]=tmpv;
                         f1_next[here.id].A[i]=tmpv;
                    }
                }
                if (a_neiR[here.id].A[i] >0) {
                    var tmpv=dstR[a_start_iR[here.id].A[i]];
                    if ( tmpv <f1[here.id].A[i] ) {
                         f1[here.id].A[i]=tmpv;
                         f1_next[here.id].A[i]=tmpv;
                    }
                }
                //writeln("ID=",here.id, " after check value f1[",here.id,"].A[",i,"]=",f1[here.id].A[i], " and f1_next[",here.id,"].A[",i,"]=",f1_next[here.id].A[i]);
                //writeln("ID=",here.id, " after update");
            }

            // here we update the neighbor area with the same vertex ID
            if (here.id>0) {
                 if ( (a_nei[here.id-1].DO.highBound >=vertexBegin) && (a_nei[here.id-1].DO.lowBound <=vertexBegin)) {
                      if (f1[here.id-1].A[vertexBegin]>f1[here.id].A[vertexBegin]) {
                            f1[here.id-1].A[vertexBegin]=f1[here.id].A[vertexBegin];
                            f1_next[here.id-1].A[vertexBegin]=f1_next[here.id].A[vertexBegin];
                      }
                 }
            }
            if (here.id<numLocales-1) {
                 if ( (a_nei[here.id+1].DO.lowBound <=vertexEnd) && (a_nei[here.id+1].DO.highBound >=vertexEnd) ) {
                      if (f1[here.id+1].A[vertexEnd]>f1[here.id].A[vertexEnd]) {
                            f1[here.id+1].A[vertexEnd]=f1[here.id].A[vertexEnd];
                            f1_next[here.id+1].A[vertexEnd]=f1_next[here.id].A[vertexEnd];
                      }
                 }
            }
        }
      }




      var converged:bool = false;
      var itera = 1;
      while(!converged) {
        var count:int=0;
        var count1:int=0;
        coforall loc in Locales with ( + reduce count, + reduce count1) {
          on loc {

                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;
                var vertexBegin = src[edgeBegin];
                var vertexEnd = src[edgeEnd];

                forall x in vertexBegin..vertexEnd  with ( + reduce count,+ reduce count1)  {
                  var minval:int;
                  if (a_nei[here.id].A[x] >0) { 
                      var edgeBegin = a_start_i[here.id].A[x];
                      var edgeEnd = edgeBegin+a_nei[here.id].A[x]-1;
                      minval=f1_next[here.id].A[x] ;
                      for i in edgeBegin..edgeEnd  {
                            var tmp2=SearchVertexValue(dst[i]);
                            if ((minval>tmp2)&&(tmp2!=-1)) {
                                 minval=tmp2;  
                            }
                      }
                      if ( UpdateValue(minval,x)) {
                               count+=1;
                      }
                  }
                  if (a_neiR[here.id].A[x] >0) { 
                      var edgeBegin = a_start_iR[here.id].A[x];
                      var edgeEnd = edgeBegin+a_neiR[here.id].A[x]-1;
                      minval=f1_next[here.id].A[x] ;
                      for i in edgeBegin..edgeEnd   {
                            var tmp2=SearchVertexValue(a_dstR[here.id].A[i]);
                            if minval>tmp2 {
                                 minval=tmp2;  
                            }
                      }
                      if ( UpdateValue(minval,x)) {
                               count+=1;
                      }
                  }
                }//end of forall






                vertexBegin = a_nei[here.id].DO.lowBound;
                vertexEnd = a_nei[here.id].DO.highBound;
                forall i in vertexBegin..vertexEnd {
                   f1[here.id].A[i]=f1_next[here.id].A[i];
                }

         }//end of loc
        }//end of coforall



        //if( ((count1 == 0) && (numLocales==1)) || (count==0) ) {
        if( (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
        }
        itera += 1;
      }
      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera-1);

      coforall loc in Locales {
        on loc {
          var vertexBegin = a_nei[here.id].DO.lowBound;
          var vertexEnd = a_nei[here.id].DO.highBound;
          forall i in vertexBegin..vertexEnd {
               f[i]=f1[here.id].A[i];
          }
       }
     }
      return f;
    }






















*/
