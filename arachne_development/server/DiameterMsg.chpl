module DiameterMsg {
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
  use LinearAlgebra;

  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use ArgSortMsg;
  use Time;
  use CommAggregation;
  use Sort;
  use Map;
  use DistributedDeque;

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
  const MultiLocale=1;

  private proc xlocal(x :int, low:int, high:int):bool {
    return low<=x && x<=high;
  }

  private proc xremote(x :int, low:int, high:int):bool {
    return !xlocal(x, low, high);
  }

  proc segDiameterMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
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
                    var edgeBegin = src.localSubdomain().lowBound;
                    var edgeEnd = src.localSubdomain().highBound;

                    forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
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


      var CompSet=new set(int,parSafe = true);
      for i in f  {
         CompSet.add(i);
      }
      writeln("Size of the Components=",CompSet.size);
      writeln("The components are as follows");
      writeln(CompSet);
      // handle all components
      var largestD=0:int;
      for i in CompSet  {
          writeln("Handle component ",i);
          var numV=f.count(i);
          if numV<=2 {
              writeln("Only two vertices, contiune");
              continue;
          }
          writeln("Allocate ",numV,"X",numV," matrix);
          var AdjMatrix=Matrix(numV,numV,eltType=int);
          AdjMatrix=0;
          var diameter=0:int ;
          writeln("Assign diagnal");
          forall j in 0..numV-1 with (ref AdjMatrix) {
               AdjMatrix[j,j]=1;
          }
          var mapary=f;
          var tmpmap=0:int;
          writeln("mapping vertices to matrix");
          for k in 0..f.size-1 {
              if f[k]==i {
                  mapary[k]=tmpmap;
                  tmpmap+=1;
                  
              }
          }
          writeln("assign edge to matrix");
          forall j in 0..f.size-1 with (ref AdjMatrix, ref diameter) {
             if f[j]==i  && nei[j] >=1 {
                 for k in start_i[j]..start_i[j]+nei[j]-1 {
                     if f[src[k]]!=i || f[dst[k]]!=i {
                         writeln("src[",k,"]=",src[k]," component=",i," dst[",k,"]=",dst[k]," f[src[",k,"]]=",f[src[k]]," f[dst[",k,"]]=",f[dst[k]]);
                         writeln("There is something wrong in the component ",i, " because they mapped to different vertices");
                         exit(0);
                     }
                     AdjMatrix[mapary[j],mapary[dst[k]]]=1;
                     AdjMatrix[mapary[dst[k]],mapary[j]]=1;
                     if j!=dst[k]  {
                        diameter=1;
                     }
 
                 }      
             }

          }
          if (numV<20) {
              writeln("The adjacency matrix ",numV,"X",numV," is as follows");
              writeln(AdjMatrix);
          } else {

              writeln("It is a ",numV,"X",numV," AdjMatrix");
          }
          // Here, we have built the adjacencent matrix based on component i
          var Mk=AdjMatrix;
          var k=0:int;
          var x,y:int;
          var havezero=false:bool;
      
          forall x in Mk with (ref havezero) {
               if x==0 {
                   havezero=true;
               }
          }
          writeln("size of the matrix=",Mk.size);
          writeln("calculate matrix power");
          while havezero && Mk.size>1 {
              var MM= matPow(Mk, 2);
              k=k+1;
              Mk=MM;
              havezero=false;
              forall x in Mk with (ref havezero) {
                   if x==0 {
                       havezero=true;
                   }
              }
              writeln("k=",k);
          }
          if k<=1 {
               writeln("The diameter of component ",i,"=1");
               continue;
          }
          diameter=max(2**(k-1),diameter):int ;
          var left=matPow(AdjMatrix, 2**(k-1));
          var B=left;
          for l in 0..k-2 {
              var Ml = matPow(AdjMatrix,2**(k-2-l));

              var Bnew = dot(B, Ml);

              havezero=false;
              forall x in Bnew with (ref havezero) {
                   if x==0 {
                       havezero=true;
                   }
              }
              if havezero {
                  B = Bnew;
                  //dot(left, Ml);
                  diameter  += 2**(k-2-l);
                  writeln("Increase diameter to ", diameter);
              } else {
                  
                  writeln("2^",k-2-l," do not have zero entry");
              }
          }
          largestD=max(largestD,diameter);
          writeln("The diameter of component ",i,"=",diameter );
      }
      writeln("The largest diameter =",largestD);

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



    var timer:stopwatch;
    // We only care for undirected graphs, they can be weighted or unweighted. 
    var f1 = makeDistArray(Nv, int);
    /*
    var f2 = makeDistArray(Nv, int);
    var f3 = makeDistArray(Nv, int);
    var f4 = makeDistArray(Nv, int);
    var f5 = makeDistArray(Nv, int);
    var f6 = makeDistArray(Nv, int);
    var f7 = makeDistArray(Nv, int);
    var f8 = makeDistArray(Nv, int);
    var f9 = makeDistArray(Nv, int);
    */
    if (Directed == 0) {

        /*
        timer.clear();
        timer.start(); 
        f1 = cc_fast_sv_dist( toSymEntry(ag.getNEIGHBOR(), int).a, 
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
        f2 = cc_connectit(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for Connectit cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        timer.clear();
        timer.start();
        f3 = cc_1m1m(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for 1m1m cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);




        timer.clear();
        timer.start();
        f4 = cc_1(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for fs c1  cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

        */
        timer.clear();
        timer.start();
        f1 = cc_2(  toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for fs c2 cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);




        timer.clear();
        timer.start();
        f1 = cc_mm( toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for fs mm cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);


    }
   

    // The message that is sent back to the Python front-end. 
    var comps = new set(int);
    for x in f1 {
      comps.add(x);
    }
    var num_comps = makeDistArray(numLocales, int); 
    num_comps[0] = comps.size;
    proc return_CC(ary:[?d] int): string throws {
      CCName = st.nextName();
      var CCEntry = new shared SymEntry(ary);
      st.addEntry(CCName, CCEntry);

      var CCMsg =  'created ' + st.attrib(CCName);
      return CCMsg;
    }

    var repMsg = return_CC(num_comps);
    return new MsgTuple(repMsg, MsgType.NORMAL);
  }

  use CommandMap;
  registerFunction("segmentedGraphDiameter", segDiameterMsg,getModuleName());
}








