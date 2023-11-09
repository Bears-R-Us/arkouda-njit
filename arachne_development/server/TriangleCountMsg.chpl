module RTriCntMsg {
    // Chapel modules.
    use Reflection;
    use Time;
    
    // Arachne modules.
    use GraphArray;
    use Utils;
    use Aggregators;
    use RTriangleCount;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use AryUtil;
    use Logging;
    use Message;

    // Server message logger. 
    private config const logLevel = ServerConfig.logLevel;
    private config const logChannel = ServerConfig.logChannel;
    const tricntLogger = new Logger(logLevel, logChannel);
  
    /**
    * Run triangle counting on an undirected and (un)weighted graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc segTriCntMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        var repMsg: string;
        var n_verticesN=msgArgs.getValueOf("NumOfVertices");
        var n_edgesN=msgArgs.getValueOf("NumOfEdges");
        var directedN=msgArgs.getValueOf("Directed");
        var weightedN=msgArgs.getValueOf("Weighted");
        var graphEntryName=msgArgs.getValueOf("GraphName");

        var vertexArrayName=msgArgs.getValueOf("VertexArray");
        var gEnt: borrowed GenSymEntry = getGenericTypedArrayEntry(vertexArrayName, st);
        var e = toSymEntry(gEnt, int);
        var vertexArray = e.a;
        var returnary=vertexArray;

        var Nv=n_verticesN:int;
        var Ne=n_edgesN:int;
        var Directed=false:bool;
        var Weighted=false:bool;
        if (directedN:int) == 1 {
            Directed=true;
        }
        if (weightedN:int) == 1 {
            Weighted=true;
        }
        var countName:string;
        var timer:stopwatch;
        timer.start();

        var TotalCnt:[0..0] int;
        var subTriSum: [0..numLocales-1] int;
        var StartVerAry: [0..numLocales-1] int;
        var EndVerAry: [0..numLocales-1] int;
        var RemoteAccessTimes: [0..numLocales-1] int;
        var LocalAccessTimes: [0..numLocales-1] int;

        TotalCnt=0;
        subTriSum=0;
        StartVerAry=-1;
        EndVerAry=-1;
        RemoteAccessTimes=0;
        LocalAccessTimes=0;

        var srcN, dstN, startN, neighbourN,vweightN,eweightN, rootN :string;
        var srcRN, dstRN, startRN, neighbourRN:string;

        var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
        var ag = gEntry.graph;

        proc triCtr_kernelMST(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                              neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) {
	        var timer:stopwatch;
            TotalCnt=0;
            subTriSum=0;	  
	        timer.start();
            proc binSearchE(ary:[?D] int,l:int,h:int,key:int):int {
 
                       if ( (l>h) || ((l==h) && ( ary[l]!=key)))  {
                            return -1;
                       }
                       if (ary[l]==key){
                            return l;
                       }
                       if (ary[h]==key){
                            return h;
                       }
                       var m= (l+h)/2:int;
                       if ((m==l) ) {
                            return -1;
                       }
                       if (ary[m]==key ){
                            return m;
                       } else {
                            if (ary[m]<key) {
                              return binSearchE(ary,m+1,h,key);
                            }
                            else {
                                    return binSearchE(ary,l,m-1,key);
                            }
                       }
          }// end of proc
          // given vertces u and v, return the edge ID e=<u,v> or e=<v,u>
          proc findEdge(u:int,v:int):int {
              //given the destinontion arry ary, the edge range [l,h], return the edge ID e where ary[e]=key
 
              var beginE=start_i[u];
              var eid=-1:int;
              if (nei[u]>0) {
                  if ( (beginE>=0) && (v>=dst[beginE]) && (v<=dst[beginE+nei[u]-1]) )  {
                       eid=binSearchE(dst,beginE,beginE+nei[u]-1,v);
                       // search <u,v> in undirect edges
                  }
              }
              if (eid==-1) {// if b
                 beginE=start_i[v];
                 if (nei[v]>0) {
                    if ( (beginE>=0) && (u>=dst[beginE]) && (u<=dst[beginE+nei[v]-1]) )  {
                          eid=binSearchE(dst,beginE,beginE+nei[v]-1,u);
                          // search <v,u> in undirect edges
                    }
                 }
              }// end of if b
              return eid;
          }// end of  proc findEdge(u:int,v:int)



          // given vertces u and v, return the edge ID e=<u,v>
          proc exactEdge(u:int,v:int):int {
              //given the destinontion arry ary, the edge range [l,h], return the edge ID e where ary[e]=key
 
              var beginE=start_i[u];
              var eid=-1:int;
              if (nei[u]>0) {
                  if ( (beginE>=0) && (v>=dst[beginE]) && (v<=dst[beginE+nei[u]-1]) )  {
                       eid=binSearchE(dst,beginE,beginE+nei[u]-1,v);
                       // search <u,v> in undirect edges
                  }
              }
              return eid;
          }// end of  proc exatEdge(u:int,v:int)

              var tmptimer:stopwatch;
              tmptimer.start();
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.lowBound;
                     var endEdge = ld.highBound;
                     var triCount=0:int;
                     forall i in startEdge..endEdge with(+ reduce triCount){ 
                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1]+neiR[v1];
                                  var    dv2=nei[v2]+neiR[v2];
                                  var    sv1:int;
                                  var    lv2:int;
                                  var    sdv1:int;
                                  var    ldv2:int;
                                  if (dv1<=dv2) {
                                        sv1=v1;
                                        lv2=v2;
                                        sdv1=dv1;
                                        ldv2=dv2;
                                  } else {
                                        sv1=v2;
                                        lv2=v1;
                                        sdv1=dv2;
                                        ldv2=dv1;
                                  }
                                  {
                                      var nextStart=start_i[sv1];
                                      var nextEnd=start_i[sv1]+nei[sv1]-1;
                                      if (nei[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce triCount){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                           triCount +=1;                                                                                                                   
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    
                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce triCount ){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                           triCount +=1;
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting
                     }// end of forall. We get the number of triangles for each edge
                     subTriSum[here.id]=triCount;
                  }// end of  on loc 
              } // end of coforall loc in Locales  


          tmptimer.stop();
          writeln("Elapsed time for triangle Counting minimum search ="+(tmptimer.elapsed()):string);
    } // end MST kernel 

    proc triCtr_vertex(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, vertex:int) {
            proc binSearchE(ary:[?D] int,l:int,h:int,key:int):int {
                if ( (l>h) || ((l==h) && ( ary[l]!=key)))  {
                    return -1;
                }
                if (ary[l]==key){
                    return l;
                }
                if (ary[h]==key){
                    return h;
                }
                var m = (l + h) / 2:int;
                if ((m==l) ) {
                    return -1;
                }
                if (ary[m]==key ){
                    return m;
                } else {
                    if (ary[m]<key) {
                        return binSearchE(ary,m+1,h,key);
                    }
                    else {
                        return binSearchE(ary,l,m-1,key);
                    }
                 }
            }// end of binSearch
            // given vertces u and v, return the edge ID e=<u,v> or e=<v,u>
            proc findEdge(u:int,v:int):int {
                //given the destination arry ary, the edge range [l,h], return the edge ID e where ary[e]=key
                if ((u==v)  ) {
                    return -1;
                    // we do not accept self-loop
                }
                var beginE=start_i[u];
                var eid=-1:int;
                if (nei[u]>0) {
                    if ( (beginE>=0) && (v>=dst[beginE]) && (v<=dst[beginE+nei[u]-1]) )  {
                        eid=binSearchE(dst,beginE,beginE+nei[u]-1,v);
                        // search <u,v> in undirect edges
                    }
                }
                if (eid==-1) {// if b
                    beginE=start_i[v];
                    if (nei[v]>0) {
                        if ( (beginE>=0) && (u>=dst[beginE]) && (u<=dst[beginE+nei[v]-1]) )  {
                            eid=binSearchE(dst,beginE,beginE+nei[v]-1,u);
                            // search <v,u> in undirect edges
                        }
                    }
                }// end of if b
                return eid;
            }// end of  proc findEdge


            // given vertces u and v, return the edge ID e=<u,v>
            proc exactEdge(u:int,v:int):int {
                //given the destination arry ary, the edge range [l,h], return the edge ID e where ary[e]=key
                if ((u==v) || (u<D1.lowBound) || (v<D1.lowBound) || (u>D1.highBound) || (v>D1.highBound) ) {
                    return -1;
                    // we do not accept self-loop
                }
                var beginE=start_i[u];
                var eid=-1:int;
                if (nei[u]>0) {
                    if ( (beginE>=0) && (v>=dst[beginE]) && (v<=dst[beginE+nei[u]-1]) )  {
                        eid=binSearchE(dst,beginE,beginE+nei[u]-1,v);
                    }
                }
                return eid;
            }// end of  proc exatEdge(u:int,v:int)


            TotalCnt=0;
            subTriSum=0;	
                            

            var timer:stopwatch;
            timer.start();
            var tmptimer:stopwatch;
            tmptimer.start();



            coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.lowBound;
                     var endEdge = ld.highBound;
                     startEdge=max(startEdge,start_i[vertex]);
                     endEdge=min(endEdge,start_i[vertex]+nei[vertex]-1);

                     var triCount=0:int;
                     forall i in startEdge..endEdge with(+ reduce triCount){
                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1]+neiR[v1];
                                  var    dv2=nei[v2]+neiR[v2];
                                  var    sv1:int;
                                  var    lv2:int;
                                  var    sdv1:int;
                                  var    ldv2:int;
                                  if (dv1<=dv2) {
                                        sv1=v1;
                                        lv2=v2;
                                        sdv1=dv1;
                                        ldv2=dv2;
                                  } else {
                                        sv1=v2;
                                        lv2=v1;
                                        sdv1=dv2;
                                        ldv2=dv1;
                                  }
                                  {
                                      var nextStart=start_i[sv1];
                                      var nextEnd=start_i[sv1]+nei[sv1]-1;
                                      if (nei[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce triCount){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                           triCount +=1;
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    
                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce triCount ){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var tmpe:int;
                                             if ( ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                           triCount +=1;
                                                       }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting
                     }// end of forall. We get the number of triangles for each edge
                     //subTriSum[here.id]=triCount;



                     ld = srcR.localSubdomain();
                     startEdge = ld.lowBound;
                     endEdge = ld.highBound;
                     startEdge=max(startEdge,start_iR[vertex]);
                     endEdge=min(endEdge,start_iR[vertex]+neiR[vertex]-1);
                     forall i in startEdge..endEdge with(+ reduce triCount){
                                  var    v1=srcR[i];
                                  var    v2=dstR[i];
                                  var    dv1=nei[v1]+neiR[v1];
                                  var    dv2=nei[v2]+neiR[v2];
                                  var    sv1:int;
                                  var    lv2:int;
                                  var    sdv1:int;
                                  var    ldv2:int;
                                  if (dv1<=dv2) {
                                        sv1=v1;
                                        lv2=v2;
                                        sdv1=dv1;
                                        ldv2=dv2;
                                  } else {
                                        sv1=v2;
                                        lv2=v1;
                                        sdv1=dv2;
                                        ldv2=dv1;
                                  }
                                  {
                                      var nextStart=start_i[sv1];
                                      var nextEnd=start_i[sv1]+nei[sv1]-1;
                                      if (nei[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce triCount){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                           triCount +=1;
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    
                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce triCount ){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var tmpe:int;
                                             if ( ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                           triCount +=1;
                                                       }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting
                     }// end of forall. We get the number of triangles for each edge
                     subTriSum[here.id]=triCount;

                }// end of  on loc 
            } // end of coforall loc in Locales 
        }//END tr_ctr_vertex



      proc return_tri_count(): int{
          for i in subTriSum {
             TotalCnt[0]+=i;
          }
          var totalRemote=0:int;
          var totalLocal=0:int;
          for i in RemoteAccessTimes {
              totalRemote+=i;
          }
          for i in LocalAccessTimes {
              totalLocal+=i;
          }
          TotalCnt[0]/=3;
          return TotalCnt[0];

      }

      proc return_tri_count_array(): string throws{
          var countName = st.nextName();
          var countEntry = new shared SymEntry(returnary);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }


      proc return_count(): int {
          for i in subTriSum {
             TotalCnt[0]+=i;
          }
          var totalRemote=0:int;
          var totalLocal=0:int;
          for i in RemoteAccessTimes {
              totalRemote+=i;
          }
          for i in LocalAccessTimes {
              totalLocal+=i;
          }
          TotalCnt[0]/=2;
          return TotalCnt[0];

      }

    proc return_all_count(): int {
          for i in subTriSum {
             TotalCnt[0]+=i;
          }
          TotalCnt[0]/=3;
          return TotalCnt[0];

      }
      proc return_vertex_count(): int {
          for i in subTriSum {
             TotalCnt[0]+=i;
          }
          TotalCnt[0]/=2;
          return TotalCnt[0];

      }


      if (!Directed) {
        if (vertexArray[0]==-1) { 
              triCtr_kernelMST(
                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a
                );
              returnary[0]=return_all_count();
               } else {
                  for i in 0..returnary.size-1 {
                       triCtr_vertex(
                        toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                        toSymEntry(ag.getComp("START_IDX"), int).a,
                        toSymEntry(ag.getComp("SRC"), int).a,
                        toSymEntry(ag.getComp("DST"), int).a,
                        toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                        toSymEntry(ag.getComp("START_IDX_R"), int).a,
                        toSymEntry(ag.getComp("SRC_R"), int).a,
                        toSymEntry(ag.getComp("DST_R"), int).a,
                      vertexArray[i]);
                       returnary[i]=return_vertex_count();

                  }
               }
      } else {
        tricntLogger.error(getModuleName(),getRoutineName(),getLineNumber(), "Triangle count not implemented for directed graphs.");
      }
      //repMsg = return_tri_count();
      repMsg = return_tri_count_array();
      timer.stop();
      tricntLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }// end of segTriMsg

   use CommandMap;
   registerFunction("RsegmentedGraphTri", segTriCntMsg,getModuleName());
}
