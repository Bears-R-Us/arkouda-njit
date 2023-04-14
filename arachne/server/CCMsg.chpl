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

  //use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;
  use Utils;

  use Set;

  // private config const logLevel = ServerConfig.logLevel;
  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  
  config const start_min_degree = 1000000;
  var tmpmindegree=start_min_degree;

  var JumpSteps:int=6;

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

    // FastSpread: a  propogation based connected components algorithm
    proc cc_fs_dist(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 

      // Initialize f and f_low in distributed memory.

      coforall loc in Locales {
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



      var converged:bool = false;
      var itera = 1;
      /*
      //while( (!converged) && (itera<JumpSteps) ) {
      while( (!converged) ) {
      //for t in 0..JumpSteps {
        var count:int=0;
        var count1:int=0;
        coforall loc in Locales with ( + reduce count) {
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
                             count+=1;
                         }
                         if(TmpMin < f[f[v]]) {
                             f[f[v]] = TmpMin;
                             count+=1;
                         }
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count+=1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count+=1;
                         }
                  
            }//end of forall
          }
        }


        if( (count==0) ) {
          converged = true;
          //break;
        }
        else {
          converged = false;
        }
        itera += 1;
      }
      */
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
                  if ((numLocales ==1) || (itera % JumpSteps ==0)  ) {
                         TmpMin=min(f[f[u]],f[f[v]]);
                         if(TmpMin < f[f[u]]) {
                             f[f[u]] = TmpMin;
                             count+=1;
                         }
                         if(TmpMin < f[f[v]]) {
                             f[f[v]] = TmpMin;
                             count+=1;
                         }
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count+=1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count+=1;
                         }
                  } else {
                    if ((itera % (JumpSteps*3) !=0) ) {
                         TmpMin=min(f[u],f[v]);
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count+=1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count+=1;
                         }
                    } else { 
                       //if ((itera % (JumpSteps*3) ==0) ) {
                       TmpMin=min(f[f[f[u]]],f[f[f[v]]]);
                       if(TmpMin < f[f[f[u]]]) {
                           f[f[f[u]]] = TmpMin;
                           count+=1;
                       }
                       if(TmpMin < f[f[f[v]]]) {
                           f[f[f[v]]] = TmpMin;
                           count+=1;
                       }
                       if(TmpMin < f[f[u]]) {
                             f[f[u]] = TmpMin;
                             count+=1;
                       }
                       if(TmpMin < f[f[v]]) {
                             f[f[v]] = TmpMin;
                             count+=1;
                       }
                       if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count+=1;
                       }
                       if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count+=1;
                       }
                    } 
                  }
                  
            }//end of forall
          }
        }


        if( (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
        }
        itera += 1;
      }



      //writeln("Fast sv dist visited = ", f, " Number of iterations = ", itera);
      writeln("Number of iterations = ", itera);

      return f;
    } // end of cc_fs_dist

    var timer:stopwatch;
    // We only care for undirected graphs, they can be weighted or unweighted. 
    var f3 = makeDistArray(Nv, int);
    if (Directed == 0) {
        timer.start();
        f3 = cc_fs_dist( toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a
            );
        timer.stop(); 
        outMsg = "Time elapsed for fs dist cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
    }
    
    // The message that is sent back to the Python front-end. 
    var comps = new set(int);

    for x in f3 {
      comps.add(x);
    }
    var num_comps = comps.size;

    proc return_CC(): string throws {
      CCName = st.nextName();
      var CCEntry = new shared SymEntry(f3);
      st.addEntry(CCName, CCEntry);

      var CCMsg =  'created ' + st.attrib(CCName);
      return CCMsg;
    }

    var repMsg = return_CC();
    return new MsgTuple(repMsg, MsgType.NORMAL);
  }

  use CommandMap;
  registerFunction("segmentedGraphCC", segCCMsg,getModuleName());
}
