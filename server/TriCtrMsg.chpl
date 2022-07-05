module TriCtrMsg {


  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  use SegmentedArray;
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


  use List; 
  use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;


  private config const logLevel = ServerConfig.logLevel;
  const smLogger = new Logger(logLevel);
  

  //Given a graph, calculate its number of triangles
  proc segTriCtrMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var repMsg: string;
      var (n_verticesN,n_edgesN,directedN,weightedN,graphEntryName,restpart )
          = payload.splitMsgToTuple(6);
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
      var timer:Timer;
      timer.start();

      var TotalCnt:[0..0] int;
      var subTriSum: [0..numLocales-1] int;

      var TriCtr:[0..Nv-1] real;
      var TriNum=makeDistArray(Nv,atomic int);
      var NeiTriNum=makeDistArray(Nv,atomic int);
      var NeiNonTriNum=makeDistArray(Nv,atomic int);
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

      // triangle counting as a direct graph
      proc triCtr_kernel(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{


          proc binSearchE(ary:[?D] int,l:int,h:int,key:int):int {
                       if ( (l<D.low) || (h>D.high) || (l<0)) {
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
              if ((u==v) || (u<D1.low) || (v<D1.low) || (u>D1.high) || (v>D1.high) ) {
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
              if ((u==v) || (u<D1.low) || (v<D1.low) || (u>D1.high) || (v>D1.high) ) {
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





          coforall loc in Locales {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     var triCount=0:int;


                     forall i in startEdge..endEdge with (+ reduce triCount) {
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u];
                         var dv=nei[v];
                         {
                             var beginTmp=start_i[u];
                             var endTmp=beginTmp+nei[u]-1;
                             if ( (u!=v) ){
                                if ( (nei[u]>1)  ){
                                   forall x in dst[beginTmp..endTmp] with (+ reduce triCount)  {
                                       var  e=exactEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ((x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 // wedge case i<e, u->v, u->x
                                                 if (e3!=-1) {
                                                         triCount+=1;
                                                         TriNum[u].add(1);
                                                         TriNum[v].add(1);
                                                         TriNum[x].add(1);
                                                         NeiAry[i]=true;
                                                         NeiAry[e]=true;
                                                         NeiAry[e3]=true;
                                                 }
                                          }
                                       }
                                   }
                                }
                             }
                            
                             beginTmp=start_i[v];
                             endTmp=beginTmp+nei[v]-1;
                             if ( (u!=v) ){
                                if ( (nei[v]>0)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                   forall x in dst[beginTmp..endTmp] with (+ reduce triCount) {
                                       var  e=exactEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ( (x !=u) && (i<e)) {
                                                 var e3=exactEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ( (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
                                                         // cycle case i<e,i<e3, u->v->x->u
                                                         triCount+=1;
                                                         TriNum[u].add(1);
                                                         TriNum[v].add(1);
                                                         TriNum[x].add(1);
                                                         NeiAry[i]=true;
                                                         NeiAry[e]=true;
                                                         NeiAry[e3]=true;
                                                     }
                                                 }
                                          }
                                       }
                                   }
                                }
                             }

                        }// end of if du<=dv
                  }// end of forall. We get the number of triangles for each edge
                  subTriSum[here.id]=triCount;


                }// end of  on loc 
          } // end of coforall loc in Locales 



          for i in subTriSum {
             TotalCnt[0]+=i;
          }


          coforall loc in Locales {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;

                     forall i in startEdge..endEdge {
                         var u = src[i];
                         var v = dst[i];
                         if NeiAry[i] {
                              NeiTriNum[u].add(TriNum[v].read());                   
                              NeiTriNum[v].add(TriNum[u].read());                   
                         }else{
                              NeiNonTriNum[u].add(TriNum[v].read());                   
                              NeiNonTriNum[v].add(TriNum[u].read()); 
                         }
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 

          coforall loc in Locales {
                on loc {

                     var ld = nei.localSubdomain();
                     var startVer = ld.low;
                     var endVer = ld.high;
                     forall i in startVer..endVer {
                             TriCtr[i]=(NeiNonTriNum[i].read()+((NeiTriNum[i].read()+TriNum[i].read()):real)*1/3):real/TotalCnt[0]:real;
                             writeln("Number of Triangles for vertex ", i," =",TriNum[i].read());
                             writeln("Sum of number of Triangles for vertex ", i,"'s neighbour =",NeiTriNum[i].read());
                             writeln("Sum of number of Non Triangles for vertex ", i,"'s neighbour =",NeiNonTriNum[i].read());
                             writeln("Triangle Centrality of  vertex ", i," =",TriCtr[i]);
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TriCtr);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }





      if (!Directed) {
              repMsg=triCtr_kernel(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a);
      }
      timer.stop();
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }// end of seg







    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedGraphTriCtr", segTriCtrMsg);
    }


}

