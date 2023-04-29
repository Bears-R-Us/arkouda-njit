module TriCtrMsg {
    use Reflection;
    use ServerErrors;
    use Logging;
    use Message;
    use SegmentedString;
    use ServerErrorStrings;
    use ServerConfig;
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use RandArray;
    use IO;

    use SymArrayDmap;
    use Random;
    use RadixSortLSD;
    use Set;
    use DistributedBag;
    use ArgSortMsg;
    use Time;
    use CommAggregation;
    use Sort;
    use Map;
    use DistributedDeque;
    use Utils;

    use List; 
    use Atomics;
    use IO.FormattedIO; 
    use GraphArray;

    private config const logLevel = ServerConfig.logLevel;
    const smLogger = new Logger(logLevel);
  

  //Given a graph, calculate its number of triangles
  proc segTriCtrMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
      var repMsg: string;
      var n_verticesN=msgArgs.getValueOf("NumOfVertices");
      var n_edgesN=msgArgs.getValueOf("NumOfEdges");
      var directedN=msgArgs.getValueOf("Directed");
      var weightedN=msgArgs.getValueOf("Weighted");
      var graphEntryName=msgArgs.getValueOf("GraphName");

      var Nv=n_verticesN:int;
      var Ne=n_edgesN:int;
      var Directed=false:bool;
      var Weighted=false:bool;
      if (directedN:int)==1 {
          Directed=true;
      }
      if (weightedN:int)==1 {
          Weighted=true;
      }
      var countName:string;
      var timer:stopwatch;

      var TotalCnt:[0..0] int;
      var subTriSum: [0..numLocales-1] int;
      var NeiNonTriNum=makeDistArray(Nv,atomic int);
      var TriCtr:[0..Nv-1] real;
      var TriNum=makeDistArray(Nv,atomic int);
      var NeiTriNum=makeDistArray(Nv,atomic int);
      var NeiAry=makeDistArray(Ne,bool);
      NeiAry=false;
      TriCtr=0.0;
      forall i in TriNum {
          i.write(0);
      }
      forall i in NeiTriNum {
          i.write(0);
      }
      forall i in NeiNonTriNum {
          i.write(0);
      }


      TotalCnt=0;
      subTriSum=0;


      var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
      var ag = gEntry.graph;
      

      proc triCtr_kernelMST(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{
	  var timer:stopwatch;
          TriCtr=0.0;
          forall i in TriNum {
              i.write(0);
          }
          forall i in NeiTriNum {
              i.write(0);
          }
      	  forall i in NeiNonTriNum {
              i.write(0);
          }          


          TotalCnt=0;
          subTriSum=0;	  
	      timer.start();
          proc binSearchE(ary:[?D] int,l:int,h:int,key:int):int {
                       if ( (l<D.lowBound) || (h>D.highBound) || (l<0)) {
                           return -1;
                       }
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
              if ((u==v) || (u<D1.lowBound) || (v<D1.lowBound) || (u>D1.highBound) || (v>D1.highBound) ) {
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
          }// end of  proc findEdge(u:int,v:int)



          // given vertces u and v, return the edge ID e=<u,v>
          proc exactEdge(u:int,v:int):int {
              //given the destinontion arry ary, the edge range [l,h], return the edge ID e where ary[e]=key
              if ((u==v) || (u<D1.lowBound) || (v<D1.lowBound) || (u>D1.highBound) || (v>D1.highBound) ) {
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
                           var Count:int;
                           Count=0;
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
                                                           TriNum[sv1].add(1);
                                                           TriNum[lv2].add(1);
                                                           TriNum[v4].add(1);
                                                           NeiAry[i]=true;
                                                           NeiAry[j]=true;
                                                           NeiAry[tmpe]=true;                                                                                                                         
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
                                                           TriNum[sv1].add(1);
                                                           TriNum[lv2].add(1);
                                                           TriNum[v4].add(1);
                                                           NeiAry[i]=true;
                                                           NeiAry[j]=true;
                                                           NeiAry[tmpe]=true;
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



          for i in subTriSum {
             TotalCnt[0]+=i;
          }
          tmptimer.stop();
          writeln("Elapsed time for triangle Counting minimum search ="+(tmptimer.elapsed()):string);


          coforall loc in Locales {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.lowBound;
                     var endEdge = ld.highBound;

                     forall i in startEdge..endEdge {
                         var u = src[i];
                         var v = dst[i];
                         if NeiAry[i] {
                              NeiTriNum[u].add(TriNum[v].read());                   
                              NeiTriNum[v].add(TriNum[u].read());                   
                         }
                         else {
                              NeiNonTriNum[u].add(TriNum[v].read());                   
                              NeiNonTriNum[v].add(TriNum[u].read()); 
                         }                         
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 

          coforall loc in Locales {
                on loc {

                     var ld = nei.localSubdomain();
                     var startVer = ld.lowBound;
                     var endVer = ld.highBound;
                     forall i in startVer..endVer{
                             var curnum=0:int;
                             var beginTmp=start_i[i];
                             var endTmp=beginTmp+nei[i]-1;
                             forall j in beginTmp..endTmp with (+ reduce curnum) {
                                   curnum+=TriNum[dst[j]].read();
                             }
                             beginTmp=start_iR[i];
                             endTmp=beginTmp+neiR[i]-1;
                             forall j in beginTmp..endTmp with (+ reduce curnum) {
                                   curnum+=TriNum[dstR[j]].read();
                             }
                             //TriCtr[i]=(NeiNonTriNum[i].read()+((NeiTriNum[i].read()+TriNum[i].read()):real)*1/3):real/TotalCnt[0]:real;
                             TriCtr[i]=(curnum-(NeiTriNum[i].read()+TriNum[i].read())*2.0/3.0+TriNum[i].read()):real/TotalCnt[0]:real;
                             //writeln("MST Number of Triangles for vertex ", i," =",TriNum[i].read());
                             //writeln("MST Sum of number of Triangles for vertex ", i,"'s neighbour =",NeiTriNum[i].read());
                             //writeln("MST Triangle Centrality of  vertex ", i," =",TriCtr[i]);
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TriCtr);
          st.addEntry(countName, countEntry);
          var cntMsg =  'created ' + st.attrib(countName);
          timer.stop();
          writeln("After Triangle Centrality Minimum search method, time= ", (timer.elapsed()):string);
          return cntMsg;
      } //END MST KERNEL

      if (!Directed) {
              repMsg=triCtr_kernelMST(
                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a
            );                                                                            
      } else {
            smLogger.error(getModuleName(), getRoutineName(), getLineNumber(), 
                           "Triangle centrality is only specified for undirected graphs currently.");
        }
      
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }// end of seg

   use CommandMap;
   registerFunction("segmentedGraphTriCtr", segTriCtrMsg,getModuleName());


}

