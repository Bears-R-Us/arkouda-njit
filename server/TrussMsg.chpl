
module TrussMsg {


  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  use SegmentedArray;
  use ServerErrorStrings;
  use ServerConfig;
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use IO;


  use SymArrayDmap;
  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use Time;
  use CommAggregation;
  use Sort;
  use Map;
  use DistributedDeque;


  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;


  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  var outMsg:string;
  



 proc segTrussMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
  //In this procedure, we implement different Truss analysis methods, including k-truss, max truss and truss decomposition
  
      var repMsg: string;
      var (kTrussN,n_verticesN, n_edgesN, directedN, weightedN, graphEntryName, restpart )
          = payload.splitMsgToTuple(7);
      var kValue=kTrussN:int;
      var Nv=n_verticesN:int;
      var Ne=n_edgesN:int;
      var Directed=false:bool;
      var Weighted=false:bool;
      if ((directedN:int)==1){
          Directed=true;
      }
      if ((weightedN:int)==1) {
          Weighted=true;
      }
      var countName:string;


      
      var StartEdgeAry: [0..numLocales-1] int;
      var EndEdgeAry: [0..numLocales-1] int;
      var RemoteAccessTimes: [0..numLocales-1] int;
      var LocalAccessTimes: [0..numLocales-1] int;
      var EdgeCnt: [0..Ne] int;
      var EdgeFlags:[0..Ne] int;
      var EdgeCount:[0..Ne] int;
      StartEdgeAry=-1;
      EndEdgeAry=-1;
      RemoteAccessTimes=0;
      LocalAccessTimes=0;
      EdgeCnt=0;
      EdgeFlags = 0;
      EdgeCount = 0;

      var srcN, dstN, startN, neighbourN,vweightN,eweightN, rootN :string;
      var srcRN, dstRN, startRN, neighbourRN:string;
      var repCount=0:int;

      
      var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
      var ag = gEntry.graph;

      var gEdgeDeleted=makeDistArray(Ne,int); //we need a global instead of local array
      var lEdgeDeleted=makeDistArray(Ne,int); //we need a global instead of local array
      var AllRemoved:bool;
      gEdgeDeleted=-1;
      lEdgeDeleted=-1;
      var kLow=3:int;
      var kUp:int;
      var kMid:int;
      var maxtimer:Timer;


      // this can be a general procedure to check if x is in given range so we put it outside
      proc xlocal(x :int, low:int, high:int):bool{
                if (low<=x && x<=high) {
                      return true;
                } else {
                      return false;
                }
      }

      // binary search if key is in ary from index l to h
      proc binSearchE(ary:[?D] int,l:int,h:int,key:int):int {
                       //if ( (l<D.low) || (h>D.high) || (l<0)) {
                       //    return -1;
                       //}
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

      //estimate the max k for given graph
      proc getupK(nei:[?D1] int, neiR:[?D11] int):int {
          var dNumber: [0..Nv-1] int;
          dNumber=0;
          var maxk=0:int;
          for  i in 0..Nv-1 {
               if nei[i]+neiR[i]>=Nv-1 {
                  dNumber[Nv-1]+=1;
               } else {
                  dNumber[nei[i]+neiR[i]]+=1;
               }
          }
          var tmpi=Nv-1:int;
          while tmpi>0 {
               dNumber[tmpi-1]+=dNumber[tmpi];
               if dNumber[tmpi-1]>=tmpi {
                   maxk=tmpi;
                   break;
               }
               tmpi=tmpi-1;
          }
          
          return maxk;
      }






//@@@@@@@@@@@@@@@@@@@@@@@@@@@@
//Begin of K-Truss Functions
      proc kTrussNaiveListIntersection(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i]=0;
                         var uadj = new set(int, parSafe = true);
                         var vadj = new set(int, parSafe = true);
                         var u = src[i];
                         var v = dst[i];
                         var beginTmp=start_i[u];
                         var endTmp=beginTmp+nei[u]-1;
                         if ((EdgeDeleted[i]==-1) && (u!=v) ){
                            if ( (nei[u]>0)  ){
                               forall x in dst[beginTmp..endTmp] with (ref uadj) {
                                   var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                   if (e!=-1){
                                      if ((EdgeDeleted[e] ==-1) && (x !=v)) {
                                             uadj.add(x);
                                      }
                                   }
                               }
                            }
                            beginTmp=start_iR[u];
                            endTmp=beginTmp+neiR[u]-1;
                            if ((neiR[u]>0) ){
                               forall x in dstR[beginTmp..endTmp] with (ref uadj) {
                                   var e=findEdge(x,u);
                                   if (e!=-1){
                                      if ((EdgeDeleted[e] ==-1) && (x !=v)) {
                                             uadj.add(x);
                                      }
                                   }
                               }
                            }
                            



                            beginTmp=start_i[v];
                            endTmp=beginTmp+nei[v]-1;
                            if ( (nei[v]>0)  ){
                               forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                   var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                   if (e!=-1){
                                      if ((EdgeDeleted[e] ==-1) && (x !=u)) {
                                             vadj.add(x);
                                      }
                                   }
                               }
                            }
                            beginTmp=start_iR[v];
                            endTmp=beginTmp+neiR[v]-1;
                            if ((neiR[v]>0) ){
                               forall x in dstR[beginTmp..endTmp] with (ref vadj) {
                                   var e=findEdge(x,v);
                                   if (e!=-1){
                                      if ((EdgeDeleted[e] ==-1) && (x !=u)) {
                                             vadj.add(x);
                                      }
                                   }
                               }
                            }

                            if  (! uadj.isEmpty() ){
                               var Count=0:int;
                               forall s in uadj with ( + reduce Count) {
                                   //var e=findEdge(s,v);
                                   if ( vadj.contains(s) ) {
                                      Count +=1;
                                   }
                               }
                               TriCount[i]=Count;


                               // here we get the number of triangles of edge ID i
                            }// end of if 
                        }//end of if
                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussNaiveListIntersection, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveListIntersection, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveListIntersection, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveListIntersection, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussNaiveListIntersection



      proc kTrussNaiveSetSearchSmall(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;

                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i]=0;
                         var sVadj = new set(int, parSafe = true);
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u]+neiR[u];
                         var dv=nei[v]+neiR[v];
                         var sV:int;
                         var lV:int;
                         var ldV:int;

                         if ( du<=dv ) {
                             sV=u;   //sV is the small degree vertex
                             lV=v;   //lV is the large degree vertex
                             ldV=dv; //ldV is the degree number 
                         } else {
                             sV=v;
                             lV=u;
                             ldV=du;
                         }
                         // here we search from the vertex who has small degree
                         {
                             var beginTmp=start_i[sV];
                             var endTmp=beginTmp+nei[sV]-1;
                             if ((EdgeDeleted[i]==-1) && (sV!=lV) ){
                                if ( (nei[sV]>0)  ){
                                   forall x in dst[beginTmp..endTmp] with (ref sVadj) {
                                       var  e=exactEdge(sV,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }
                                   }
                                }
                                beginTmp=start_iR[sV];
                                endTmp=beginTmp+neiR[sV]-1;
                                if ((neiR[sV]>0) ){
                                   forall x in dstR[beginTmp..endTmp] with (ref sVadj) {
                                       var e=exactEdge(x,sV);
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }  
                                   }
                                }
                                if  (! sVadj.isEmpty() ){
                                   var Count=0:int;
                                   forall s in sVadj with ( + reduce Count) {
                                       var ds1=nei[s]+neiR[s];
                                       var e:int;
                                       if (ds1<ldV) {
                                          e=findEdge(s,lV);
                                       } else {
                                          e=findEdge(lV,s);
                                       }
                                       if ( (e!=-1)  && (e!=i) ) {
                                           if ( EdgeDeleted[e]==-1) {
                                              Count +=1;
                                           }
                                       }
                                   }
                               TriCount[i]=Count;


                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussNaiveSetSearchSmall, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveSetSearchSmall, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveSetSearchSmall, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveSetSearchSmall, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussNaiveSetSearchSmall



      proc kTrussNaiveSetSearchSmallSeq(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;

                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i]=0;
                         var sVadj = new set(int, parSafe = true);
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u]+neiR[u];
                         var dv=nei[v]+neiR[v];
                         var sV:int;
                         var lV:int;
                         var ldV:int;

                         if ( du<=dv ) {
                             sV=u;   //sV is the small degree vertex
                             lV=v;   //lV is the large degree vertex
                             ldV=dv; //ldV is the degree number 
                         } else {
                             sV=v;
                             lV=u;
                             ldV=du;
                         }
                         // here we search from the vertex who has small degree
                         {
                             var beginTmp=start_i[sV];
                             var endTmp=beginTmp+nei[sV]-1;
                             if ((EdgeDeleted[i]==-1) && (sV!=lV) ){
                                if ( (nei[sV]>0)  ){
                                   for x in dst[beginTmp..endTmp]  {
                                       var  e=exactEdge(sV,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }
                                   }
                                }
                                beginTmp=start_iR[sV];
                                endTmp=beginTmp+neiR[sV]-1;
                                if ((neiR[sV]>0) ){
                                   for x in dstR[beginTmp..endTmp]  {
                                       var e=exactEdge(x,sV);
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }  
                                   }
                                }
                                if  (! sVadj.isEmpty() ){
                                   var Count=0:int;
                                   for s in sVadj  {
                                       var ds1=nei[s]+neiR[s];
                                       var e:int;
                                       if (ds1<ldV) {
                                          e=findEdge(s,lV);
                                       } else {
                                          e=findEdge(lV,s);
                                       }
                                       if ( (e!=-1)  && (e!=i) ) {
                                           if ( EdgeDeleted[e]==-1) {
                                              Count +=1;
                                           }
                                       }
                                   }
                               TriCount[i]=Count;



                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 





                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussNaiveSetSearchSmallSeq, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveSetSearchSmallSeq, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveSetSearchSmallSeq, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveSetSearchSmallSeq, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussNaiveSetSearchSmallSeq



      proc kTrussNaivePathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge {
                         TriCount[i]=0;
                         var Count=0:int;
                         var u = src[i];
                         var v = dst[i];
                         var beginUf=start_i[u];
                         var endUf=beginUf+nei[u]-1;

                         var beginUb=start_iR[u];
                         var endUb=beginUb+neiR[u]-1;

                         var beginVf=start_i[v];
                         var endVf=beginVf+nei[v]-1;

                         var beginVb=start_iR[v];
                         var endVb=beginVb+neiR[v]-1;

                         var iu:int;
                         var jv:int;
                         var eu:int;
                         var ev:int;
                         if ((EdgeDeleted[i]==-1) && (u!=v) ){
                           iu=beginUf;
                           jv=beginVf;
                           while ( (iu <=endUf) &&   (jv<=endVf) && (nei[u]>0) && (nei[v]>0))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }  

                           iu=beginUf;
                           jv=beginVb;
                           while ( (iu <=endUf) &&   (jv<=endVb) && (nei[u]>0) && (neiR[v]>0) )  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             ev=findEdge(dstR[jv],v);
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }



                           iu=beginUb;
                           jv=beginVf;
                           while ( (iu <=endUb) &&   (jv<=endVf) && (neiR[u]>0) && (nei[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }


                           iu=beginUb;
                           jv=beginVb;
                           while ( (iu <=endUb) &&   (jv<=endVb) && (neiR[u]>0) && (neiR[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             ev=findEdge(dstR[jv],v);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }
                        }//end of if
                               TriCount[i]=Count;


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussNaivePathMerge, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaivePathMerge, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaivePathMerge, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaivePathMerge, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussNaivePathMerge



      proc kTrussNaiveMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles using mininum search  method.
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i]=0;
                           var Count:int;
                           Count=0;
                           if (EdgeDeleted[i]==-1) {
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
                                         forall j in nextStart..nextEnd with (+ reduce Count){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //for j in nextStart..nextEnd {
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]==-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce Count ){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //forall j in nextStart..nextEnd {
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      //TriCount[i]+=1;
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting

                           }// i is an undeleted edge
                               TriCount[i]=Count;


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussNaiveMinSearch, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveMinSearch, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveMinSearch, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNaiveMinSearch, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussNaiveMinSearch



      proc kTrussPathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          //while (ConFlag) {
          {

              // first we calculate the number of triangles
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge {
                         TriCount[i].write(0);
                         var Count=0:int;
                         var u = src[i];
                         var v = dst[i];
                         var beginUf=start_i[u];
                         var endUf=beginUf+nei[u]-1;

                         var beginUb=start_iR[u];
                         var endUb=beginUb+neiR[u]-1;

                         var beginVf=start_i[v];
                         var endVf=beginVf+nei[v]-1;

                         var beginVb=start_iR[v];
                         var endVb=beginVb+neiR[v]-1;

                         var iu:int;
                         var jv:int;
                         var eu:int;
                         var ev:int;
                         if ((EdgeDeleted[i]==-1) && (u!=v) ){
                           iu=beginUf;
                           jv=beginVf;
                           while ( (iu <=endUf) &&   (jv<=endVf) && (nei[u]>0) && (nei[v]>0))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }  

                           iu=beginUf;
                           jv=beginVb;
                           while ( (iu <=endUf) &&   (jv<=endVb) && (nei[u]>0) && (neiR[v]>0) )  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             ev=findEdge(dstR[jv],v);
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }



                           iu=beginUb;
                           jv=beginVf;
                           while ( (iu <=endUb) &&   (jv<=endVf) && (neiR[u]>0) && (nei[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }


                           iu=beginUb;
                           jv=beginVb;
                           while ( (iu <=endUb) &&   (jv<=endVb) && (neiR[u]>0) && (neiR[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             ev=findEdge(dstR[jv],v);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }
                        }//end of if
                               TriCount[i].write(Count);


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 

          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){

                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i].read() <MinNumTri[here.id]) {
                                            MinNumTri[here.id]=TriCount[i].read();
                                       }
                                  }
                               }

                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF

                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF  {


                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges


                                  var u = src[i];
                                  var v = dst[i];
                                  var beginUf=start_i[u];
                                  var endUf=beginUf+nei[u]-1;
 
                                  var beginUb=start_iR[u];
                                  var endUb=beginUb+neiR[u]-1;

                                  var beginVf=start_i[v];
                                  var endVf=beginVf+nei[v]-1;

                                  var beginVb=start_iR[v];
                                  var endVb=beginVb+neiR[v]-1;

                                  var iu:int;
                                  var jv:int;
                                  var eu:int;
                                  var ev:int;
                                  if ( (u!=v) ){// edge <u,v> is not a self-loop
                                    iu=beginUf;
                                    jv=beginVf;
                                    if  ((nei[u]<2) || (nei[v]==0)) {
                                        iu=endUf+1;
                                    }
                                    while ( (iu <=endUf) &&   (jv<=endVf)  )  {
                                      if  ( (EdgeDeleted[iu] >0 ) || (dst[iu]==v) || (dst[iu]==u)) {
                                            iu+=1;
                                            continue;
                                      }
                                      if ( (EdgeDeleted[jv] >0 ) || (dst[jv]==u)|| (dst[jv]==v) ) {
                                           jv+=1;
                                           continue;
                                      }
                                      {
                                          if dst[iu]==dst[jv] {
                                              if (EdgeDeleted[iu]==-1) && (EdgeDeleted[jv]==-1) {
                                                  TriCount[iu].sub(1);
                                                  TriCount[jv].sub(1);
                                              } else {
                                                  if (EdgeDeleted[jv]==-1) && (i<iu) {
                                                      TriCount[jv].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[iu]==-1) && (i<jv) {
                                                          TriCount[iu].sub(1);
                                                      }
                                                  }

                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                              if dst[iu]<dst[jv] {
                                                 iu+=1;
                                              } else {
                                                 jv+=1;
                                             }
                                          }
                                      } 
                                    }  

                                    iu=beginUf;
                                    jv=beginVb;
                                    if  ((nei[u]<2) || (neiR[v]==0)) {
                                        iu=endUf+1;
                                    }
                                    while ( (iu <=endUf) &&   (jv<=endVb) )  {
                                      if  ( (EdgeDeleted[iu] >0) || (dst[iu]==v)|| (dst[iu]==u) ) {
                                           iu+=1;
                                           continue;
                                      }
                                      ev=exactEdge(dstR[jv],v);
                                      if (ev!=-1) {
                                          if ( (EdgeDeleted[ev]>0) || (dstR[jv]==u)|| (dstR[jv]==v)) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dst[iu]==dstR[jv] {
                                              if (EdgeDeleted[iu]==-1) && (EdgeDeleted[ev]==-1) {
                                                  TriCount[iu].sub(1);
                                                  TriCount[ev].sub(1);
                                              } else {
                                                  if (EdgeDeleted[ev]==-1) && (i<iu) {
                                                      TriCount[ev].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[iu]==-1) && (i<ev) {
                                                          TriCount[iu].sub(1);
                                                      }
                                                  }

                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                              if dst[iu]<dstR[jv] {
                                                 iu+=1;
                                              } else {
                                                 jv+=1;
                                              }
                                          }
                                      } 
                                    }



                                    iu=beginUb;
                                    jv=beginVf;
                                    if  ((neiR[u]<1) || (nei[v]<1)) {
                                        iu=endUb+1;
                                    }
                                    while ( (iu <=endUb) &&   (jv<=endVf) )  {
                                      eu=exactEdge(dstR[iu],u);
                                      if (eu!=-1){
                                          if  ( (EdgeDeleted[eu] >0) || (dstR[iu]==v)|| (dstR[iu]==u) ) {
                                               iu+=1;
                                               continue;
                                          }
                                          if ( (EdgeDeleted[jv] >0) || (dst[jv]==u) || (dst[jv]==v)) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dstR[iu]==dst[jv] {
                                              if (EdgeDeleted[eu]==-1) && (EdgeDeleted[jv]==-1) {
                                                  TriCount[eu].sub(1);
                                                  TriCount[jv].sub(1);
                                              } else {
                                                  if (EdgeDeleted[jv]==-1) && (i<eu) {
                                                      TriCount[jv].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[eu]==-1) && (i<jv) {
                                                          TriCount[eu].sub(1);
                                                      }
                                                  }
                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                             if dstR[iu]<dst[jv] {
                                                iu+=1;
                                             } else {
                                                jv+=1;
                                             }
                                          }
                                      } 
                                    }


                                    iu=beginUb;
                                    jv=beginVb;
                                    if  ((neiR[u]<1) || (neiR[v]<2)) {
                                        iu=endUb+1;
                                    }
                                    while ( (iu <=endUb) &&   (jv<=endVb) )  {
                                      eu=exactEdge(dstR[iu],u);
                                      ev=exactEdge(dstR[jv],v);
                                      if ((eu!=-1)&&(ev!=-1)){

                                          if  ( (EdgeDeleted[eu] >0) || (dstR[iu]==v) || (dstR[iu]==u) ) {
                                               iu+=1;
                                               continue;
                                          }
                                          if ( (EdgeDeleted[ev] >0)  || (dstR[jv]==u) || (dstR[jv]==v)  ) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else
                                      {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dstR[iu]==dstR[jv] {
                                              if (EdgeDeleted[eu]==-1) && (EdgeDeleted[ev]==-1) {
                                                  TriCount[eu].sub(1);
                                                  TriCount[ev].sub(1);
                                              } else {
                                                  if (EdgeDeleted[ev]==-1) && (i<eu) {
                                                      TriCount[ev].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[eu]==-1) && (i<ev) {
                                                          TriCount[eu].sub(1);
                                                      }
                                                  }
                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                             if dstR[iu]<dstR[jv] {
                                                iu+=1;
                                             } else {
                                                jv+=1;
                                             }
                                          }
                                      } 
                                    }

                                  }// end of if ( (u!=v) )

                              }// end of if (xlocal(i,startEdge,endEdge)) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 

                  //outMsg="After forall ";
                  //smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                  coforall loc in Locales  {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussPathMerge, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussPathMerge, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussPathMerge, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussPathMerge, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussPathMerge



      proc kTrussNonMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          //while (ConFlag) {
          {

              // first we calculate the number of triangles using mininum search  method.
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i].write(0);
                           var Count:int;
                           Count=0;
                           if (EdgeDeleted[i]==-1) {
                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1]+neiR[v1];
                                  var    dv2=nei[v2]+neiR[v2];
                                  var    sv1:int;
                                  var    lv2:int;
                                  var    sdv1:int;
                                  var    ldv2:int;





                                  {
                                        sv1=v1;
                                        lv2=v2;
                                        sdv1=dv1;
                                        ldv2=dv2;
                                  } 
                                  {
                                      var nextStart=start_i[sv1];
                                      var nextEnd=start_i[sv1]+nei[sv1]-1;
                                      if (nei[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce Count){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //for j in nextStart..nextEnd {
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                            tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]==-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce Count ){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //forall j in nextStart..nextEnd {
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                          tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      //TriCount[i]+=1;
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting

                           }// i is an undeleted edge
                               TriCount[i].write(Count);


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){

                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i].read() <MinNumTri[here.id]) {
                                            MinNumTri[here.id]=TriCount[i].read();
                                       }
                                  }
                               }

                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1]+neiR[v1];
                                  var    dv2=nei[v2]+neiR[v2];
                                  var    sv1:int;
                                  var    lv2:int;
                                  var    sdv1:int;
                                  var    ldv2:int;





                                  {
                                        sv1=v1;
                                        lv2=v2;
                                        sdv1=dv1;
                                        ldv2=dv2;
                                  } 
                                  {
                                      var nextStart=start_i[sv1];
                                      var nextEnd=start_i[sv1]+nei[sv1]-1;
                                      if (nei[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                            tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {


                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {

                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=findEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                          tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e1].sub(1);

                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       } 
                                                                   } 
                                                               }
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of affected edge search 



                              } // end if (xlocal(i,startEdge,endEdge) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 


                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussNonMinSearch, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNonMinSearch, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNonMinSearch, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussNonMinSearch, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussNonMinSearch



      proc kTrussMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          //while (ConFlag) {
          {

              // first we calculate the number of triangles using mininum search  method.
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i].write(0);
                           var Count:int;
                           Count=0;
                           if (EdgeDeleted[i]==-1) {
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
                                         forall j in nextStart..nextEnd with (+ reduce Count){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //for j in nextStart..nextEnd {
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]==-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce Count ){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //forall j in nextStart..nextEnd {
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      //TriCount[i]+=1;
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting

                           }// i is an undeleted edge
                               TriCount[i].write(Count);


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){

                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i].read() <MinNumTri[here.id]) {
                                            MinNumTri[here.id]=TriCount[i].read();
                                       }
                                  }
                               }

                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
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
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<=dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {


                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {

                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=findEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e1].sub(1);

                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       } 
                                                                   } 
                                                               }
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of affected edge search 



                              } // end if (xlocal(i,startEdge,endEdge) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 


                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussMinSearch, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussMinSearch, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussMinSearch, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussMinSearch, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussMinSearch



      proc kTrussMix(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          //while (ConFlag) {
          {

              // first we calculate the number of triangles
              coforall loc in Locales with ( ref SetNextF) {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;


                     forall i in startEdge..endEdge {
                         TriCount[i].write(0);
                     }
                     //forall i in startEdge..endEdge with(ref SetCurF){
                     forall i in startEdge..endEdge {
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u];
                         var dv=nei[v];
                         {
                             var beginTmp=start_i[u];
                             var endTmp=beginTmp+nei[u]-1;
                             if ((EdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[u]>1)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref uadj) {
                                   forall x in dst[beginTmp..endTmp]  {
                                       var  e=exactEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 // wedge case i<e, u->v, u->x
                                                 if (e3!=-1) {
                                                     if (EdgeDeleted[e3]==-1) {
                                                         TriCount[i].add(1);
                                                         TriCount[e].add(1);
                                                         TriCount[e3].add(1);
                                                     }
                                                 }
                                          }
                                       }
                                   }
                                }
                             }
                            
                             beginTmp=start_i[v];
                             endTmp=beginTmp+nei[v]-1;
                             if ((EdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[v]>0)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                   forall j in beginTmp..endTmp {
                                       var  x=dst[j];
                                       if ((EdgeDeleted[j] ==-1) && (x !=u) && (i<j)) {
                                                 var e3=exactEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1)  && (i<e3)) {
                                                         // cycle case i<j,i<e3, u->v->x->u
                                                         TriCount[i].add(1);
                                                         TriCount[j].add(1);
                                                         TriCount[e3].add(1);
                                                     }
                                                 }
                                       }
                                   }
                                }
                             }

                        }// end of if du<=dv
                  }// end of forall. We get the number of triangles for each edge


                }// end of  on loc 
              } // end of coforall loc in Locales 



          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){

                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i].read() <MinNumTri[here.id]) {
                                            MinNumTri[here.id]=TriCount[i].read();
                                       }
                                  }
                               }

                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;


              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges

                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1];
                                  var    dv2=nei[v2];

                                  {
                                      var nextStart=start_i[v1];
                                      var nextEnd=start_i[v1]+nei[v1]-1;
                                      if (nei[v1]>1) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==v1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( v2!=v4 ) ) {
                                                       //v1->v2, v1->v4
                                                       tmpe=findEdge(v2,v4);
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   //if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                   if ((EdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                      if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                      }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_i[v2];
                                      nextEnd=start_i[v2]+nei[v2]-1;
                                      if (nei[v2]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==v2
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( v1!=v4 )  ) {
                                                       tmpe=exactEdge(v4,v1);
                                                       // cycle case v1->v2->v4->v1
                                                       if (tmpe!=-1)  {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if


                                      //check the case of x->v1 and x->v2
                                      nextStart=start_iR[v1];
                                      nextEnd=start_iR[v1]+neiR[v1]-1;
                                      var dv1=neiR[v1];
                                      var dv2=neiR[v2];
                                      if ((dv1<=dv2) && (dv1>0)) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//v3==v1
                                             var v4=dstR[j];
                                             var e2=exactEdge(v4,v3);
                                             if (EdgeDeleted[e2]<=-1) {
                                                var tmpe=exactEdge(v4,v2);
                                                if (tmpe!=-1) {
                                                               if ((EdgeDeleted[e2]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e2].sub(1);
                                                               } 
                                                }
                                             }
                                          }
                                      } else {
                                         nextStart=start_iR[v2];
                                         nextEnd=start_iR[v2]+neiR[v2]-1;
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//v3==v2
                                             var v4=dstR[j];
                                             var e2=exactEdge(v4,v3);
                                             if (EdgeDeleted[e2]<=-1) {
                                                var tmpe=exactEdge(v4,v1);
                                                if (tmpe!=-1) {
                                                               if ((EdgeDeleted[e2]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e2].sub(1);
                                                               } 
                                                }
                                             }
                                          }
                                      } 

                                  }


                              } // end if (xlocal(i,startEdge,endEdge) 
                           } // end forall i in SetCurF with (ref SetNextF) 
                      } //end on loc 
                  } //end coforall loc in Locales 

                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge) ) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc 
                  } // end of coforall loc in Locales 

                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
              
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          if (RemovedEdge.read()<Ne) {
                  AllRemoved=false;
          }



          outMsg="After kTrussMix, Given K ="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussMix, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussMix, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After kTrussMix, The k truss has edges ="+(Ne-RemovedEdge.read()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc kTrussMix



//End of K-Truss Functions
//@@@@@@@@@@@@@@@@@@@@@@@@@@@@


//@@@@@@@@@@@@@@@@@@@@@@@@@@@@
//Begin of Max K-Truss Functions
      proc OnceMaxTrussNaivePathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):bool{ 


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge {
                         TriCount[i]=0;
                         var Count=0:int;
                         var u = src[i];
                         var v = dst[i];
                         var beginUf=start_i[u];
                         var endUf=beginUf+nei[u]-1;

                         var beginUb=start_iR[u];
                         var endUb=beginUb+neiR[u]-1;

                         var beginVf=start_i[v];
                         var endVf=beginVf+nei[v]-1;

                         var beginVb=start_iR[v];
                         var endVb=beginVb+neiR[v]-1;

                         var iu:int;
                         var jv:int;
                         var eu:int;
                         var ev:int;
                         if ((EdgeDeleted[i]==-1) && (u!=v) ){
                           iu=beginUf;
                           jv=beginVf;
                           while ( (iu <=endUf) &&   (jv<=endVf) && (nei[u]>0) && (nei[v]>0))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }  

                           iu=beginUf;
                           jv=beginVb;
                           while ( (iu <=endUf) &&   (jv<=endVb) && (nei[u]>0) && (neiR[v]>0) )  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             ev=findEdge(dstR[jv],v);
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }



                           iu=beginUb;
                           jv=beginVf;
                           while ( (iu <=endUb) &&   (jv<=endVf) && (neiR[u]>0) && (nei[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }


                           iu=beginUb;
                           jv=beginVb;
                           while ( (iu <=endUb) &&   (jv<=endVb) && (neiR[u]>0) && (neiR[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             ev=findEdge(dstR[jv],v);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }
                        }//end of if
                               TriCount[i]=Count;


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());



              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();




              
              N2+=1;
          }// end while 
          AllRemoved=true;
          var cnt:[0..numLocales-1] int=0;
          coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         var tmpcnt:int=0;
                         forall i in startEdge..endEdge with (+reduce tmpcnt)  {
                               if ((EdgeDeleted[i]==-1) ) {
                                   tmpcnt+=1;
                               }
                         }
                         cnt[here.id]=tmpcnt;
                      }// end of  on loc
          } // end of coforall loc in Locales


          for i in 0..numLocales-1  {
               if cnt[i]>0 {
                     AllRemoved=false;
                     break;
               }
          }





          return AllRemoved;

      }// end of proc OnceMaxTrussNaivePathMerge



      proc MaxTrussNaivePathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{

                var PlTriCount =makeDistArray(Ne,int);
                ref gEdgeDeleted=EdgeDeleted;
                ref PTriCount=TriCount;
                var lEdgeDeleted =makeDistArray(Ne,int);


                PTriCount=0;
                PlTriCount=0;
                gEdgeDeleted=-1;
                lEdgeDeleted=-1;//for local use
                maxtimer.clear();
                maxtimer.start();
                kLow=3;
                // we first check  kLow=3

                repMsg=kTrussNaivePathMerge(kLow,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, PlTriCount,lEdgeDeleted);


                gEdgeDeleted=lEdgeDeleted;
                PTriCount=PlTriCount;



                kUp=getupK(toSymEntry(ag.getNEIGHBOR(), int).a, toSymEntry(ag.getNEIGHBOR_R(), int).a);
                outMsg="Estimated kUp="+kUp:string;
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                if ((!AllRemoved) && (kUp>3)) {// we need to check if max k  >3
                    var ConLoop=true:bool;
                    while ( (ConLoop) && (kLow<kUp)) {
                         // we will continuely check if the up value can remove all edges
                         lEdgeDeleted=gEdgeDeleted;
                         PlTriCount=PTriCount;
                             //restore the value for kUp check
                         // we check the larget k vaule kUp which is the upper bound of max k
                         // we will use kMid to reduce kUp

                         AllRemoved=OnceMaxTrussNaivePathMerge(kUp,

                              toSymEntry(ag.getNEIGHBOR(), int).a,
                              toSymEntry(ag.getSTART_IDX(), int).a,
                              toSymEntry(ag.getSRC(), int).a,
                              toSymEntry(ag.getDST(), int).a,
                              toSymEntry(ag.getNEIGHBOR_R(), int).a,
                              toSymEntry(ag.getSTART_IDX_R(), int).a,
                              toSymEntry(ag.getSRC_R(), int).a,
                              toSymEntry(ag.getDST_R(), int).a, PlTriCount,lEdgeDeleted);
                         if (!AllRemoved) { //the up value is the max k
                                ConLoop=false;
                         } else {// we will check the mid value to reduce kUp

                            kUp= kUp-1;
                            kMid= (kLow+kUp)/2;
                            while ((AllRemoved) && (kMid<kUp-1)) {

                                lEdgeDeleted=gEdgeDeleted;
                                PlTriCount=PTriCount;
                                //restore the value for kMid check
                                //"Try mid=",kMid;

                                AllRemoved=OnceMaxTrussNaivePathMerge(kMid,

                                     toSymEntry(ag.getNEIGHBOR(), int).a,
                                     toSymEntry(ag.getSTART_IDX(), int).a,
                                     toSymEntry(ag.getSRC(), int).a,
                                     toSymEntry(ag.getDST(), int).a,
                                     toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                     toSymEntry(ag.getSTART_IDX_R(), int).a,
                                     toSymEntry(ag.getSRC_R(), int).a,
                                     toSymEntry(ag.getDST_R(), int).a, PlTriCount,lEdgeDeleted);
                                if (AllRemoved) {
                                    kUp=kMid-1;
                                    kMid= (kLow+kUp)/2;
                                }
                            }


                            if (!AllRemoved) { // if mid value can remove all edges, we will reduce the up value for checking
                                if kMid>=kUp-1 {
                                    ConLoop=false;
                                    kUp=kMid;
                                } else {// we will update the low value and then check the mid value
                                        // until all edges are removed

                                     while ((!AllRemoved) && (kMid<kUp-1)) {
                                        kLow=kMid;
                                        kMid= (kLow+kUp)/2;
                                        gEdgeDeleted=lEdgeDeleted;
                                        PTriCount=PlTriCount;
                                        //store the latest no empty subgraph setup 
                                        //("Try mid again=",kMid);

                                        AllRemoved=OnceMaxTrussNaivePathMerge(kMid,

                                             toSymEntry(ag.getNEIGHBOR(), int).a,
                                             toSymEntry(ag.getSTART_IDX(), int).a,
                                             toSymEntry(ag.getSRC(), int).a,
                                             toSymEntry(ag.getDST(), int).a,
                                             toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                             toSymEntry(ag.getSTART_IDX_R(), int).a,
                                             toSymEntry(ag.getSRC_R(), int).a,
                                             toSymEntry(ag.getDST_R(), int).a, PlTriCount,lEdgeDeleted);
                                     }
                                     if (AllRemoved) {
                                         kUp=kMid-1;
                                     }
                                  }
                            }
                         }
                    }// end of while
                    var countName = st.nextName();
                    var countEntry = new shared SymEntry(lEdgeDeleted);
                    st.addEntry(countName, countEntry);
                    repMsg =  'created ' + st.attrib(countName);
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussNaivePathMerge, Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    outMsg="After OnceMaxTrussNaivePathMerge, Max K="+kUp:string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussNaivePathMerge,Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {

                        outMsg="After OnceMaxTrussNaivePathMerge, Max K=3";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {

                        outMsg="After OnceMaxTrussNaivePathMerge,Max K=2";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }


          return repMsg;

      }// end of proc MaxTrussNaivePathMerge



      proc OnceMaxTrussPathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):bool{ 


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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


          timer.start();

          ConFlag=true;
          //while (ConFlag) {
          {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if ((EdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF

                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF  {


                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges


                                  var u = src[i];
                                  var v = dst[i];
                                  var beginUf=start_i[u];
                                  var endUf=beginUf+nei[u]-1;
 
                                  var beginUb=start_iR[u];
                                  var endUb=beginUb+neiR[u]-1;

                                  var beginVf=start_i[v];
                                  var endVf=beginVf+nei[v]-1;

                                  var beginVb=start_iR[v];
                                  var endVb=beginVb+neiR[v]-1;

                                  var iu:int;
                                  var jv:int;
                                  var eu:int;
                                  var ev:int;
                                  if ( (u!=v) ){// edge <u,v> is not a self-loop
                                    iu=beginUf;
                                    jv=beginVf;
                                    if  ((nei[u]<2) || (nei[v]==0)) {
                                        iu=endUf+1;
                                    }
                                    while ( (iu <=endUf) &&   (jv<=endVf)  )  {
                                      if  ( (EdgeDeleted[iu] >0 ) || (dst[iu]==v) || (dst[iu]==u)) {
                                            iu+=1;
                                            continue;
                                      }
                                      if ( (EdgeDeleted[jv] >0 ) || (dst[jv]==u)|| (dst[jv]==v) ) {
                                           jv+=1;
                                           continue;
                                      }
                                      {
                                          if dst[iu]==dst[jv] {
                                              if (EdgeDeleted[iu]==-1) && (EdgeDeleted[jv]==-1) {
                                                  TriCount[iu].sub(1);
                                                  TriCount[jv].sub(1);
                                              } else {
                                                  if (EdgeDeleted[jv]==-1) && (i<iu) {
                                                      TriCount[jv].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[iu]==-1) && (i<jv) {
                                                          TriCount[iu].sub(1);
                                                      }
                                                  }

                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                              if dst[iu]<dst[jv] {
                                                 iu+=1;
                                              } else {
                                                 jv+=1;
                                             }
                                          }
                                      } 
                                    }  

                                    iu=beginUf;
                                    jv=beginVb;
                                    if  ((nei[u]<2) || (neiR[v]==0)) {
                                        iu=endUf+1;
                                    }
                                    while ( (iu <=endUf) &&   (jv<=endVb) )  {
                                      if  ( (EdgeDeleted[iu] >0) || (dst[iu]==v)|| (dst[iu]==u) ) {
                                           iu+=1;
                                           continue;
                                      }
                                      ev=exactEdge(dstR[jv],v);
                                      if (ev!=-1) {
                                          if ( (EdgeDeleted[ev]>0) || (dstR[jv]==u)|| (dstR[jv]==v)) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dst[iu]==dstR[jv] {
                                              if (EdgeDeleted[iu]==-1) && (EdgeDeleted[ev]==-1) {
                                                  TriCount[iu].sub(1);
                                                  TriCount[ev].sub(1);
                                              } else {
                                                  if (EdgeDeleted[ev]==-1) && (i<iu) {
                                                      TriCount[ev].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[iu]==-1) && (i<ev) {
                                                          TriCount[iu].sub(1);
                                                      }
                                                  }

                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                              if dst[iu]<dstR[jv] {
                                                 iu+=1;
                                              } else {
                                                 jv+=1;
                                              }
                                          }
                                      } 
                                    }



                                    iu=beginUb;
                                    jv=beginVf;
                                    if  ((neiR[u]<1) || (nei[v]<1)) {
                                        iu=endUb+1;
                                    }
                                    while ( (iu <=endUb) &&   (jv<=endVf) )  {
                                      eu=exactEdge(dstR[iu],u);
                                      if (eu!=-1){
                                          if  ( (EdgeDeleted[eu] >0) || (dstR[iu]==v)|| (dstR[iu]==u) ) {
                                               iu+=1;
                                               continue;
                                          }
                                          if ( (EdgeDeleted[jv] >0) || (dst[jv]==u) || (dst[jv]==v)) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dstR[iu]==dst[jv] {
                                              if (EdgeDeleted[eu]==-1) && (EdgeDeleted[jv]==-1) {
                                                  TriCount[eu].sub(1);
                                                  TriCount[jv].sub(1);
                                              } else {
                                                  if (EdgeDeleted[jv]==-1) && (i<eu) {
                                                      TriCount[jv].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[eu]==-1) && (i<jv) {
                                                          TriCount[eu].sub(1);
                                                      }
                                                  }
                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                             if dstR[iu]<dst[jv] {
                                                iu+=1;
                                             } else {
                                                jv+=1;
                                             }
                                          }
                                      } 
                                    }


                                    iu=beginUb;
                                    jv=beginVb;
                                    if  ((neiR[u]<1) || (neiR[v]<2)) {
                                        iu=endUb+1;
                                    }
                                    while ( (iu <=endUb) &&   (jv<=endVb) )  {
                                      eu=exactEdge(dstR[iu],u);
                                      ev=exactEdge(dstR[jv],v);
                                      if ((eu!=-1)&&(ev!=-1)){

                                          if  ( (EdgeDeleted[eu] >0) || (dstR[iu]==v) || (dstR[iu]==u) ) {
                                               iu+=1;
                                               continue;
                                          }
                                          if ( (EdgeDeleted[ev] >0)  || (dstR[jv]==u) || (dstR[jv]==v)  ) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else
                                      {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dstR[iu]==dstR[jv] {
                                              if (EdgeDeleted[eu]==-1) && (EdgeDeleted[ev]==-1) {
                                                  TriCount[eu].sub(1);
                                                  TriCount[ev].sub(1);
                                              } else {
                                                  if (EdgeDeleted[ev]==-1) && (i<eu) {
                                                      TriCount[ev].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[eu]==-1) && (i<ev) {
                                                          TriCount[eu].sub(1);
                                                      }
                                                  }
                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                             if dstR[iu]<dstR[jv] {
                                                iu+=1;
                                             } else {
                                                jv+=1;
                                             }
                                          }
                                      } 
                                    }

                                  }// end of if ( (u!=v) )

                              }// end of if (xlocal(i,startEdge,endEdge)) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 

                  //outMsg="After forall ";
                  //smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                  coforall loc in Locales  {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              
              N2+=1;
          }// end while 
          AllRemoved=true;
          var cnt:[0..numLocales-1] int=0;
          coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         var tmpcnt:int=0;
                         forall i in startEdge..endEdge with (+reduce tmpcnt)  {
                               if ((EdgeDeleted[i]==-1) ) {
                                   tmpcnt+=1;
                               }
                         }
                         cnt[here.id]=tmpcnt;
                      }// end of  on loc
          } // end of coforall loc in Locales


          for i in 0..numLocales-1  {
               if cnt[i]>0 {
                     AllRemoved=false;
                     break;
               }
          }





          return AllRemoved;

      }// end of proc OnceMaxTrussPathMerge



      proc MaxTrussPathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{

                ref aPTriCount=TriCount;
                var aPlTriCount =makeDistArray(Ne,atomic int);
                ref gEdgeDeleted=EdgeDeleted;
                var lEdgeDeleted =makeDistArray(Ne,int);


                forall i in 0..Ne-1 {
                    aPTriCount[i].write(0);
                    aPlTriCount[i].write(0);
                }
                gEdgeDeleted=-1;
                lEdgeDeleted=-1;//for local use
                maxtimer.clear();
                maxtimer.start();
                kLow=3;
                // we first check  kLow=3

                repMsg=kTrussPathMerge(kLow,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                forall i in 0..Ne-1 {// first keep last time's results
                             gEdgeDeleted[i]=lEdgeDeleted[i];
                             aPTriCount[i].write(aPlTriCount[i].read());
                             //EdgeDeleted and aPTricount will keep the latest value with no empty subgraph
                }
                kUp=getupK(toSymEntry(ag.getNEIGHBOR(), int).a, toSymEntry(ag.getNEIGHBOR_R(), int).a);
                outMsg="Estimated kUp="+kUp:string;
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                if ((!AllRemoved) && (kUp>3)) {// we need to check if max k  >3
                    var ConLoop=true:bool;
                    while ( (ConLoop) && (kLow<kUp)) {
                         // we will continuely check if the up value can remove all edges
                         forall i in 0..Ne-1 {// first keep last time's results
                             lEdgeDeleted[i]=gEdgeDeleted[i];
                             aPlTriCount[i].write(aPTriCount[i].read());
                             //restore the value for kUp check
                         }
                         // we check the larget k vaule kUp which is the upper bound of max k
                         // we will use kMid to reduce kUp

                         AllRemoved=OnceMaxTrussPathMerge(kUp,

                              toSymEntry(ag.getNEIGHBOR(), int).a,
                              toSymEntry(ag.getSTART_IDX(), int).a,
                              toSymEntry(ag.getSRC(), int).a,
                              toSymEntry(ag.getDST(), int).a,
                              toSymEntry(ag.getNEIGHBOR_R(), int).a,
                              toSymEntry(ag.getSTART_IDX_R(), int).a,
                              toSymEntry(ag.getSRC_R(), int).a,
                              toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                         if (!AllRemoved) { //the up value is the max k
                                ConLoop=false;
                         } else {// we will check the mid value to reduce kUp


                            kUp= kUp-1;
                            kMid= (kLow+kUp)/2;
                            while ((AllRemoved) && (kMid<kUp-1)) {

                                forall i in 0..Ne-1 {
                                    lEdgeDeleted[i]=gEdgeDeleted[i];
                                    aPlTriCount[i].write(aPTriCount[i].read());
                                //restore the value for kMid check
                                }
                                //"Try mid=",kMid;

                                AllRemoved=OnceMaxTrussPathMerge(kMid,

                                     toSymEntry(ag.getNEIGHBOR(), int).a,
                                     toSymEntry(ag.getSTART_IDX(), int).a,
                                     toSymEntry(ag.getSRC(), int).a,
                                     toSymEntry(ag.getDST(), int).a,
                                     toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                     toSymEntry(ag.getSTART_IDX_R(), int).a,
                                     toSymEntry(ag.getSRC_R(), int).a,
                                     toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                                if (AllRemoved) {
                                    kUp=kMid-1;
                                    kMid= (kLow+kUp)/2;
                                }
                            }
                            if (!AllRemoved) { // if mid value can remove all edges, we will reduce the up value for checking
                                if kMid>=kUp-1 {
                                    ConLoop=false;
                                    kUp=kMid;
                                } else {// we will update the low value and then check the mid value 
                                        // until all edges are removed
                                     while ((!AllRemoved) && (kMid<kUp-1)) {
                                        kLow=kMid;
                                        kMid= (kLow+kUp)/2;
                                        forall i in 0..Ne-1 { 
                                            gEdgeDeleted[i]=lEdgeDeleted[i];
                                            aPTriCount[i].write(aPlTriCount[i].read());
                                            //store the latest no empty subgraph setup 
                                        }

                                        AllRemoved=OnceMaxTrussPathMerge(kMid,

                                             toSymEntry(ag.getNEIGHBOR(), int).a,
                                             toSymEntry(ag.getSTART_IDX(), int).a,
                                             toSymEntry(ag.getSRC(), int).a,
                                             toSymEntry(ag.getDST(), int).a,
                                             toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                             toSymEntry(ag.getSTART_IDX_R(), int).a,
                                             toSymEntry(ag.getSRC_R(), int).a,
                                             toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                                     }
                                     if (AllRemoved) {
                                         kUp=kMid-1;
                                     } 
                                  }
                            }
                         }
                    }// end of while
                    var countName = st.nextName();
                    var maxKAry:[0..1] int;
                    maxKAry[0]=kUp;
                    var countEntry = new shared SymEntry(maxKAry);
                    st.addEntry(countName, countEntry);
                    repMsg =  'created ' + st.attrib(countName);
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussPathMerge, Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    outMsg="After OnceMaxTrussPathMerge, Max K="+kUp:string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussPathMerge,Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {

                        outMsg="After OnceMaxTrussPathMerge, Max K=3";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {

                        outMsg="After OnceMaxTrussPathMerge,Max K=2";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }


          return repMsg;

      }// end of proc MaxTrussPathMerge



      proc OnceMaxTrussNonMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):bool{ 


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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


          timer.start();

          ConFlag=true;
          //while (ConFlag) {
          {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if ((EdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1]+neiR[v1];
                                  var    dv2=nei[v2]+neiR[v2];
                                  var    sv1:int;
                                  var    lv2:int;
                                  var    sdv1:int;
                                  var    ldv2:int;





                                  {
                                        sv1=v1;
                                        lv2=v2;
                                        sdv1=dv1;
                                        ldv2=dv2;
                                  } 
                                  {
                                      var nextStart=start_i[sv1];
                                      var nextEnd=start_i[sv1]+nei[sv1]-1;
                                      if (nei[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                            tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {


                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {

                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=findEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                          tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e1].sub(1);

                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       } 
                                                                   } 
                                                               }
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of affected edge search 



                              } // end if (xlocal(i,startEdge,endEdge) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 


                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              
              N2+=1;
          }// end while 
          AllRemoved=true;
          var cnt:[0..numLocales-1] int=0;
          coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         var tmpcnt:int=0;
                         forall i in startEdge..endEdge with (+reduce tmpcnt)  {
                               if ((EdgeDeleted[i]==-1) ) {
                                   tmpcnt+=1;
                               }
                         }
                         cnt[here.id]=tmpcnt;
                      }// end of  on loc
          } // end of coforall loc in Locales


          for i in 0..numLocales-1  {
               if cnt[i]>0 {
                     AllRemoved=false;
                     break;
               }
          }





          return AllRemoved;

      }// end of proc OnceMaxTrussNonMinSearch



      proc MaxTrussNonMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{

                ref aPTriCount=TriCount;
                var aPlTriCount =makeDistArray(Ne,atomic int);
                ref gEdgeDeleted=EdgeDeleted;
                var lEdgeDeleted =makeDistArray(Ne,int);


                forall i in 0..Ne-1 {
                    aPTriCount[i].write(0);
                    aPlTriCount[i].write(0);
                }
                gEdgeDeleted=-1;
                lEdgeDeleted=-1;//for local use
                maxtimer.clear();
                maxtimer.start();
                kLow=3;
                // we first check  kLow=3

                repMsg=kTrussNonMinSearch(kLow,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                forall i in 0..Ne-1 {// first keep last time's results
                             gEdgeDeleted[i]=lEdgeDeleted[i];
                             aPTriCount[i].write(aPlTriCount[i].read());
                             //EdgeDeleted and aPTricount will keep the latest value with no empty subgraph
                }
                kUp=getupK(toSymEntry(ag.getNEIGHBOR(), int).a, toSymEntry(ag.getNEIGHBOR_R(), int).a);
                outMsg="Estimated kUp="+kUp:string;
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                if ((!AllRemoved) && (kUp>3)) {// we need to check if max k  >3
                    var ConLoop=true:bool;
                    while ( (ConLoop) && (kLow<kUp)) {
                         // we will continuely check if the up value can remove all edges
                         forall i in 0..Ne-1 {// first keep last time's results
                             lEdgeDeleted[i]=gEdgeDeleted[i];
                             aPlTriCount[i].write(aPTriCount[i].read());
                             //restore the value for kUp check
                         }
                         // we check the larget k vaule kUp which is the upper bound of max k
                         // we will use kMid to reduce kUp

                         AllRemoved=OnceMaxTrussNonMinSearch(kUp,

                              toSymEntry(ag.getNEIGHBOR(), int).a,
                              toSymEntry(ag.getSTART_IDX(), int).a,
                              toSymEntry(ag.getSRC(), int).a,
                              toSymEntry(ag.getDST(), int).a,
                              toSymEntry(ag.getNEIGHBOR_R(), int).a,
                              toSymEntry(ag.getSTART_IDX_R(), int).a,
                              toSymEntry(ag.getSRC_R(), int).a,
                              toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                         if (!AllRemoved) { //the up value is the max k
                                ConLoop=false;
                         } else {// we will check the mid value to reduce kUp


                            kUp= kUp-1;
                            kMid= (kLow+kUp)/2;
                            while ((AllRemoved) && (kMid<kUp-1)) {

                                forall i in 0..Ne-1 {
                                    lEdgeDeleted[i]=gEdgeDeleted[i];
                                    aPlTriCount[i].write(aPTriCount[i].read());
                                //restore the value for kMid check
                                }
                                //"Try mid=",kMid;

                                AllRemoved=OnceMaxTrussNonMinSearch(kMid,

                                     toSymEntry(ag.getNEIGHBOR(), int).a,
                                     toSymEntry(ag.getSTART_IDX(), int).a,
                                     toSymEntry(ag.getSRC(), int).a,
                                     toSymEntry(ag.getDST(), int).a,
                                     toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                     toSymEntry(ag.getSTART_IDX_R(), int).a,
                                     toSymEntry(ag.getSRC_R(), int).a,
                                     toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                                if (AllRemoved) {
                                    kUp=kMid-1;
                                    kMid= (kLow+kUp)/2;
                                }
                            }
                            if (!AllRemoved) { // if mid value can remove all edges, we will reduce the up value for checking
                                if kMid>=kUp-1 {
                                    ConLoop=false;
                                    kUp=kMid;
                                } else {// we will update the low value and then check the mid value 
                                        // until all edges are removed
                                     while ((!AllRemoved) && (kMid<kUp-1)) {
                                        kLow=kMid;
                                        kMid= (kLow+kUp)/2;
                                        forall i in 0..Ne-1 { 
                                            gEdgeDeleted[i]=lEdgeDeleted[i];
                                            aPTriCount[i].write(aPlTriCount[i].read());
                                            //store the latest no empty subgraph setup 
                                        }

                                        AllRemoved=OnceMaxTrussNonMinSearch(kMid,

                                             toSymEntry(ag.getNEIGHBOR(), int).a,
                                             toSymEntry(ag.getSTART_IDX(), int).a,
                                             toSymEntry(ag.getSRC(), int).a,
                                             toSymEntry(ag.getDST(), int).a,
                                             toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                             toSymEntry(ag.getSTART_IDX_R(), int).a,
                                             toSymEntry(ag.getSRC_R(), int).a,
                                             toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                                     }
                                     if (AllRemoved) {
                                         kUp=kMid-1;
                                     } 
                                  }
                            }
                         }
                    }// end of while
                    var countName = st.nextName();
                    var maxKAry:[0..1] int;
                    maxKAry[0]=kUp;
                    var countEntry = new shared SymEntry(maxKAry);
                    st.addEntry(countName, countEntry);
                    repMsg =  'created ' + st.attrib(countName);
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussNonMinSearch, Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    outMsg="After OnceMaxTrussNonMinSearch, Max K="+kUp:string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussNonMinSearch,Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {

                        outMsg="After OnceMaxTrussNonMinSearch, Max K=3";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {

                        outMsg="After OnceMaxTrussNonMinSearch,Max K=2";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }


          return repMsg;

      }// end of proc MaxTrussNonMinSearch



      proc OnceMaxTrussMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):bool{ 


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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


          timer.start();

          ConFlag=true;
          //while (ConFlag) {
          {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if ((EdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
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
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<=dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {


                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {

                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=findEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e1].sub(1);

                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       } 
                                                                   } 
                                                               }
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of affected edge search 



                              } // end if (xlocal(i,startEdge,endEdge) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 


                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              
              N2+=1;
          }// end while 
          AllRemoved=true;
          var cnt:[0..numLocales-1] int=0;
          coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         var tmpcnt:int=0;
                         forall i in startEdge..endEdge with (+reduce tmpcnt)  {
                               if ((EdgeDeleted[i]==-1) ) {
                                   tmpcnt+=1;
                               }
                         }
                         cnt[here.id]=tmpcnt;
                      }// end of  on loc
          } // end of coforall loc in Locales


          for i in 0..numLocales-1  {
               if cnt[i]>0 {
                     AllRemoved=false;
                     break;
               }
          }





          return AllRemoved;

      }// end of proc OnceMaxTrussMinSearch



      proc MaxTrussMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{

                ref aPTriCount=TriCount;
                var aPlTriCount =makeDistArray(Ne,atomic int);
                ref gEdgeDeleted=EdgeDeleted;
                var lEdgeDeleted =makeDistArray(Ne,int);


                forall i in 0..Ne-1 {
                    aPTriCount[i].write(0);
                    aPlTriCount[i].write(0);
                }
                gEdgeDeleted=-1;
                lEdgeDeleted=-1;//for local use
                maxtimer.clear();
                maxtimer.start();
                kLow=3;
                // we first check  kLow=3

                repMsg=kTrussMinSearch(kLow,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                forall i in 0..Ne-1 {// first keep last time's results
                             gEdgeDeleted[i]=lEdgeDeleted[i];
                             aPTriCount[i].write(aPlTriCount[i].read());
                             //EdgeDeleted and aPTricount will keep the latest value with no empty subgraph
                }
                kUp=getupK(toSymEntry(ag.getNEIGHBOR(), int).a, toSymEntry(ag.getNEIGHBOR_R(), int).a);
                outMsg="Estimated kUp="+kUp:string;
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                if ((!AllRemoved) && (kUp>3)) {// we need to check if max k  >3
                    var ConLoop=true:bool;
                    while ( (ConLoop) && (kLow<kUp)) {
                         // we will continuely check if the up value can remove all edges
                         forall i in 0..Ne-1 {// first keep last time's results
                             lEdgeDeleted[i]=gEdgeDeleted[i];
                             aPlTriCount[i].write(aPTriCount[i].read());
                             //restore the value for kUp check
                         }
                         // we check the larget k vaule kUp which is the upper bound of max k
                         // we will use kMid to reduce kUp

                         AllRemoved=OnceMaxTrussMinSearch(kUp,

                              toSymEntry(ag.getNEIGHBOR(), int).a,
                              toSymEntry(ag.getSTART_IDX(), int).a,
                              toSymEntry(ag.getSRC(), int).a,
                              toSymEntry(ag.getDST(), int).a,
                              toSymEntry(ag.getNEIGHBOR_R(), int).a,
                              toSymEntry(ag.getSTART_IDX_R(), int).a,
                              toSymEntry(ag.getSRC_R(), int).a,
                              toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                         if (!AllRemoved) { //the up value is the max k
                                ConLoop=false;
                         } else {// we will check the mid value to reduce kUp


                            kUp= kUp-1;
                            kMid= (kLow+kUp)/2;
                            while ((AllRemoved) && (kMid<kUp-1)) {

                                forall i in 0..Ne-1 {
                                    lEdgeDeleted[i]=gEdgeDeleted[i];
                                    aPlTriCount[i].write(aPTriCount[i].read());
                                //restore the value for kMid check
                                }
                                //"Try mid=",kMid;

                                AllRemoved=OnceMaxTrussMinSearch(kMid,

                                     toSymEntry(ag.getNEIGHBOR(), int).a,
                                     toSymEntry(ag.getSTART_IDX(), int).a,
                                     toSymEntry(ag.getSRC(), int).a,
                                     toSymEntry(ag.getDST(), int).a,
                                     toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                     toSymEntry(ag.getSTART_IDX_R(), int).a,
                                     toSymEntry(ag.getSRC_R(), int).a,
                                     toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                                if (AllRemoved) {
                                    kUp=kMid-1;
                                    kMid= (kLow+kUp)/2;
                                }
                            }
                            if (!AllRemoved) { // if mid value can remove all edges, we will reduce the up value for checking
                                if kMid>=kUp-1 {
                                    ConLoop=false;
                                    kUp=kMid;
                                } else {// we will update the low value and then check the mid value 
                                        // until all edges are removed
                                     while ((!AllRemoved) && (kMid<kUp-1)) {
                                        kLow=kMid;
                                        kMid= (kLow+kUp)/2;
                                        forall i in 0..Ne-1 { 
                                            gEdgeDeleted[i]=lEdgeDeleted[i];
                                            aPTriCount[i].write(aPlTriCount[i].read());
                                            //store the latest no empty subgraph setup 
                                        }

                                        AllRemoved=OnceMaxTrussMinSearch(kMid,

                                             toSymEntry(ag.getNEIGHBOR(), int).a,
                                             toSymEntry(ag.getSTART_IDX(), int).a,
                                             toSymEntry(ag.getSRC(), int).a,
                                             toSymEntry(ag.getDST(), int).a,
                                             toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                             toSymEntry(ag.getSTART_IDX_R(), int).a,
                                             toSymEntry(ag.getSRC_R(), int).a,
                                             toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                                     }
                                     if (AllRemoved) {
                                         kUp=kMid-1;
                                     } 
                                  }
                            }
                         }
                    }// end of while
                    var countName = st.nextName();
                    var maxKAry:[0..1] int;
                    maxKAry[0]=kUp;
                    var countEntry = new shared SymEntry(maxKAry);
                    st.addEntry(countName, countEntry);
                    repMsg =  'created ' + st.attrib(countName);
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussMinSearch, Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    outMsg="After OnceMaxTrussMinSearch, Max K="+kUp:string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussMinSearch,Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {

                        outMsg="After OnceMaxTrussMinSearch, Max K=3";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {

                        outMsg="After OnceMaxTrussMinSearch,Max K=2";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }


          return repMsg;

      }// end of proc MaxTrussMinSearch



      proc OnceMaxTrussMix(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):bool{ 


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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


          timer.start();

          ConFlag=true;
          //while (ConFlag) {
          {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if ((EdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;


              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges

                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1];
                                  var    dv2=nei[v2];

                                  {
                                      var nextStart=start_i[v1];
                                      var nextEnd=start_i[v1]+nei[v1]-1;
                                      if (nei[v1]>1) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==v1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( v2!=v4 ) ) {
                                                       //v1->v2, v1->v4
                                                       tmpe=findEdge(v2,v4);
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   //if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                   if ((EdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                      if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                      }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_i[v2];
                                      nextEnd=start_i[v2]+nei[v2]-1;
                                      if (nei[v2]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==v2
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( v1!=v4 )  ) {
                                                       tmpe=exactEdge(v4,v1);
                                                       // cycle case v1->v2->v4->v1
                                                       if (tmpe!=-1)  {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if


                                      //check the case of x->v1 and x->v2
                                      nextStart=start_iR[v1];
                                      nextEnd=start_iR[v1]+neiR[v1]-1;
                                      var dv1=neiR[v1];
                                      var dv2=neiR[v2];
                                      if ((dv1<=dv2) && (dv1>0)) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//v3==v1
                                             var v4=dstR[j];
                                             var e2=exactEdge(v4,v3);
                                             if (EdgeDeleted[e2]<=-1) {
                                                var tmpe=exactEdge(v4,v2);
                                                if (tmpe!=-1) {
                                                               if ((EdgeDeleted[e2]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e2].sub(1);
                                                               } 
                                                }
                                             }
                                          }
                                      } else {
                                         nextStart=start_iR[v2];
                                         nextEnd=start_iR[v2]+neiR[v2]-1;
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//v3==v2
                                             var v4=dstR[j];
                                             var e2=exactEdge(v4,v3);
                                             if (EdgeDeleted[e2]<=-1) {
                                                var tmpe=exactEdge(v4,v1);
                                                if (tmpe!=-1) {
                                                               if ((EdgeDeleted[e2]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e2].sub(1);
                                                               } 
                                                }
                                             }
                                          }
                                      } 

                                  }


                              } // end if (xlocal(i,startEdge,endEdge) 
                           } // end forall i in SetCurF with (ref SetNextF) 
                      } //end on loc 
                  } //end coforall loc in Locales 

                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge) ) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc 
                  } // end of coforall loc in Locales 

                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 





              
              N2+=1;
          }// end while 
          AllRemoved=true;
          var cnt:[0..numLocales-1] int=0;
          coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         var tmpcnt:int=0;
                         forall i in startEdge..endEdge with (+reduce tmpcnt)  {
                               if ((EdgeDeleted[i]==-1) ) {
                                   tmpcnt+=1;
                               }
                         }
                         cnt[here.id]=tmpcnt;
                      }// end of  on loc
          } // end of coforall loc in Locales


          for i in 0..numLocales-1  {
               if cnt[i]>0 {
                     AllRemoved=false;
                     break;
               }
          }





          return AllRemoved;

      }// end of proc OnceMaxTrussMix



      proc MaxTrussMix(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{

                ref aPTriCount=TriCount;
                var aPlTriCount =makeDistArray(Ne,atomic int);
                ref gEdgeDeleted=EdgeDeleted;
                var lEdgeDeleted =makeDistArray(Ne,int);


                forall i in 0..Ne-1 {
                    aPTriCount[i].write(0);
                    aPlTriCount[i].write(0);
                }
                gEdgeDeleted=-1;
                lEdgeDeleted=-1;//for local use
                maxtimer.clear();
                maxtimer.start();
                kLow=3;
                // we first check  kLow=3

                repMsg=kTrussMix(kLow,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                forall i in 0..Ne-1 {// first keep last time's results
                             gEdgeDeleted[i]=lEdgeDeleted[i];
                             aPTriCount[i].write(aPlTriCount[i].read());
                             //EdgeDeleted and aPTricount will keep the latest value with no empty subgraph
                }
                kUp=getupK(toSymEntry(ag.getNEIGHBOR(), int).a, toSymEntry(ag.getNEIGHBOR_R(), int).a);
                outMsg="Estimated kUp="+kUp:string;
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                if ((!AllRemoved) && (kUp>3)) {// we need to check if max k  >3
                    var ConLoop=true:bool;
                    while ( (ConLoop) && (kLow<kUp)) {
                         // we will continuely check if the up value can remove all edges
                         forall i in 0..Ne-1 {// first keep last time's results
                             lEdgeDeleted[i]=gEdgeDeleted[i];
                             aPlTriCount[i].write(aPTriCount[i].read());
                             //restore the value for kUp check
                         }
                         // we check the larget k vaule kUp which is the upper bound of max k
                         // we will use kMid to reduce kUp

                         AllRemoved=OnceMaxTrussMix(kUp,

                              toSymEntry(ag.getNEIGHBOR(), int).a,
                              toSymEntry(ag.getSTART_IDX(), int).a,
                              toSymEntry(ag.getSRC(), int).a,
                              toSymEntry(ag.getDST(), int).a,
                              toSymEntry(ag.getNEIGHBOR_R(), int).a,
                              toSymEntry(ag.getSTART_IDX_R(), int).a,
                              toSymEntry(ag.getSRC_R(), int).a,
                              toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                         if (!AllRemoved) { //the up value is the max k
                                ConLoop=false;
                         } else {// we will check the mid value to reduce kUp


                            kUp= kUp-1;
                            kMid= (kLow+kUp)/2;
                            while ((AllRemoved) && (kMid<kUp-1)) {

                                forall i in 0..Ne-1 {
                                    lEdgeDeleted[i]=gEdgeDeleted[i];
                                    aPlTriCount[i].write(aPTriCount[i].read());
                                //restore the value for kMid check
                                }
                                //"Try mid=",kMid;

                                AllRemoved=OnceMaxTrussMix(kMid,

                                     toSymEntry(ag.getNEIGHBOR(), int).a,
                                     toSymEntry(ag.getSTART_IDX(), int).a,
                                     toSymEntry(ag.getSRC(), int).a,
                                     toSymEntry(ag.getDST(), int).a,
                                     toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                     toSymEntry(ag.getSTART_IDX_R(), int).a,
                                     toSymEntry(ag.getSRC_R(), int).a,
                                     toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                                if (AllRemoved) {
                                    kUp=kMid-1;
                                    kMid= (kLow+kUp)/2;
                                }
                            }
                            if (!AllRemoved) { // if mid value can remove all edges, we will reduce the up value for checking
                                if kMid>=kUp-1 {
                                    ConLoop=false;
                                    kUp=kMid;
                                } else {// we will update the low value and then check the mid value 
                                        // until all edges are removed
                                     while ((!AllRemoved) && (kMid<kUp-1)) {
                                        kLow=kMid;
                                        kMid= (kLow+kUp)/2;
                                        forall i in 0..Ne-1 { 
                                            gEdgeDeleted[i]=lEdgeDeleted[i];
                                            aPTriCount[i].write(aPlTriCount[i].read());
                                            //store the latest no empty subgraph setup 
                                        }

                                        AllRemoved=OnceMaxTrussMix(kMid,

                                             toSymEntry(ag.getNEIGHBOR(), int).a,
                                             toSymEntry(ag.getSTART_IDX(), int).a,
                                             toSymEntry(ag.getSRC(), int).a,
                                             toSymEntry(ag.getDST(), int).a,
                                             toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                             toSymEntry(ag.getSTART_IDX_R(), int).a,
                                             toSymEntry(ag.getSRC_R(), int).a,
                                             toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                                     }
                                     if (AllRemoved) {
                                         kUp=kMid-1;
                                     } 
                                  }
                            }
                         }
                    }// end of while
                    var countName = st.nextName();
                    var maxKAry:[0..1] int;
                    maxKAry[0]=kUp;
                    var countEntry = new shared SymEntry(maxKAry);
                    st.addEntry(countName, countEntry);
                    repMsg =  'created ' + st.attrib(countName);
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussMix, Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    outMsg="After OnceMaxTrussMix, Max K="+kUp:string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();

                    outMsg="After OnceMaxTrussMix,Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {

                        outMsg="After OnceMaxTrussMix, Max K=3";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {

                        outMsg="After OnceMaxTrussMix,Max K=2";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }


          return repMsg;

      }// end of proc MaxTrussMix



//End of Max K-Truss Functions
//@@@@@@@@@@@@@@@@@@@@@@@@@@@@


//@@@@@@@@@@@@@@@@@@@@@@@@@@@@
//Begin of Truss Decomposition Functions
      proc TrussDecoNaiveListIntersection(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i]=0;
                         var uadj = new set(int, parSafe = true);
                         var vadj = new set(int, parSafe = true);
                         var u = src[i];
                         var v = dst[i];
                         var beginTmp=start_i[u];
                         var endTmp=beginTmp+nei[u]-1;
                         if ((EdgeDeleted[i]==-1) && (u!=v) ){
                            if ( (nei[u]>0)  ){
                               forall x in dst[beginTmp..endTmp] with (ref uadj) {
                                   var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                   if (e!=-1){
                                      if ((EdgeDeleted[e] ==-1) && (x !=v)) {
                                             uadj.add(x);
                                      }
                                   }
                               }
                            }
                            beginTmp=start_iR[u];
                            endTmp=beginTmp+neiR[u]-1;
                            if ((neiR[u]>0) ){
                               forall x in dstR[beginTmp..endTmp] with (ref uadj) {
                                   var e=findEdge(x,u);
                                   if (e!=-1){
                                      if ((EdgeDeleted[e] ==-1) && (x !=v)) {
                                             uadj.add(x);
                                      }
                                   }
                               }
                            }
                            



                            beginTmp=start_i[v];
                            endTmp=beginTmp+nei[v]-1;
                            if ( (nei[v]>0)  ){
                               forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                   var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                   if (e!=-1){
                                      if ((EdgeDeleted[e] ==-1) && (x !=u)) {
                                             vadj.add(x);
                                      }
                                   }
                               }
                            }
                            beginTmp=start_iR[v];
                            endTmp=beginTmp+neiR[v]-1;
                            if ((neiR[v]>0) ){
                               forall x in dstR[beginTmp..endTmp] with (ref vadj) {
                                   var e=findEdge(x,v);
                                   if (e!=-1){
                                      if ((EdgeDeleted[e] ==-1) && (x !=u)) {
                                             vadj.add(x);
                                      }
                                   }
                               }
                            }

                            if  (! uadj.isEmpty() ){
                               var Count=0:int;
                               forall s in uadj with ( + reduce Count) {
                                   //var e=findEdge(s,v);
                                   if ( vadj.contains(s) ) {
                                      Count +=1;
                                   }
                               }
                               TriCount[i]=Count;


                               // here we get the number of triangles of edge ID i
                            }// end of if 
                        }//end of if
                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoNaiveListIntersection, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveListIntersection, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveListIntersection, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveListIntersection, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoNaiveListIntersection



      proc TrussDecoNaiveSetSearchSmall(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;

                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i]=0;
                         var sVadj = new set(int, parSafe = true);
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u]+neiR[u];
                         var dv=nei[v]+neiR[v];
                         var sV:int;
                         var lV:int;
                         var ldV:int;

                         if ( du<=dv ) {
                             sV=u;   //sV is the small degree vertex
                             lV=v;   //lV is the large degree vertex
                             ldV=dv; //ldV is the degree number 
                         } else {
                             sV=v;
                             lV=u;
                             ldV=du;
                         }
                         // here we search from the vertex who has small degree
                         {
                             var beginTmp=start_i[sV];
                             var endTmp=beginTmp+nei[sV]-1;
                             if ((EdgeDeleted[i]==-1) && (sV!=lV) ){
                                if ( (nei[sV]>0)  ){
                                   forall x in dst[beginTmp..endTmp] with (ref sVadj) {
                                       var  e=exactEdge(sV,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }
                                   }
                                }
                                beginTmp=start_iR[sV];
                                endTmp=beginTmp+neiR[sV]-1;
                                if ((neiR[sV]>0) ){
                                   forall x in dstR[beginTmp..endTmp] with (ref sVadj) {
                                       var e=exactEdge(x,sV);
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }  
                                   }
                                }
                                if  (! sVadj.isEmpty() ){
                                   var Count=0:int;
                                   forall s in sVadj with ( + reduce Count) {
                                       var ds1=nei[s]+neiR[s];
                                       var e:int;
                                       if (ds1<ldV) {
                                          e=findEdge(s,lV);
                                       } else {
                                          e=findEdge(lV,s);
                                       }
                                       if ( (e!=-1)  && (e!=i) ) {
                                           if ( EdgeDeleted[e]==-1) {
                                              Count +=1;
                                           }
                                       }
                                   }
                               TriCount[i]=Count;


                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoNaiveSetSearchSmall, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveSetSearchSmall, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveSetSearchSmall, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveSetSearchSmall, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoNaiveSetSearchSmall



      proc TrussDecoNaiveSetSearchSmallSeq(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;

                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i]=0;
                         var sVadj = new set(int, parSafe = true);
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u]+neiR[u];
                         var dv=nei[v]+neiR[v];
                         var sV:int;
                         var lV:int;
                         var ldV:int;

                         if ( du<=dv ) {
                             sV=u;   //sV is the small degree vertex
                             lV=v;   //lV is the large degree vertex
                             ldV=dv; //ldV is the degree number 
                         } else {
                             sV=v;
                             lV=u;
                             ldV=du;
                         }
                         // here we search from the vertex who has small degree
                         {
                             var beginTmp=start_i[sV];
                             var endTmp=beginTmp+nei[sV]-1;
                             if ((EdgeDeleted[i]==-1) && (sV!=lV) ){
                                if ( (nei[sV]>0)  ){
                                   for x in dst[beginTmp..endTmp]  {
                                       var  e=exactEdge(sV,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }
                                   }
                                }
                                beginTmp=start_iR[sV];
                                endTmp=beginTmp+neiR[sV]-1;
                                if ((neiR[sV]>0) ){
                                   for x in dstR[beginTmp..endTmp]  {
                                       var e=exactEdge(x,sV);
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }  
                                   }
                                }
                                if  (! sVadj.isEmpty() ){
                                   var Count=0:int;
                                   for s in sVadj  {
                                       var ds1=nei[s]+neiR[s];
                                       var e:int;
                                       if (ds1<ldV) {
                                          e=findEdge(s,lV);
                                       } else {
                                          e=findEdge(lV,s);
                                       }
                                       if ( (e!=-1)  && (e!=i) ) {
                                           if ( EdgeDeleted[e]==-1) {
                                              Count +=1;
                                           }
                                       }
                                   }
                               TriCount[i]=Count;



                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 





                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoNaiveSetSearchSmallSeq, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveSetSearchSmallSeq, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveSetSearchSmallSeq, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveSetSearchSmallSeq, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoNaiveSetSearchSmallSeq



      proc TrussDecoNaivePathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge {
                         TriCount[i]=0;
                         var Count=0:int;
                         var u = src[i];
                         var v = dst[i];
                         var beginUf=start_i[u];
                         var endUf=beginUf+nei[u]-1;

                         var beginUb=start_iR[u];
                         var endUb=beginUb+neiR[u]-1;

                         var beginVf=start_i[v];
                         var endVf=beginVf+nei[v]-1;

                         var beginVb=start_iR[v];
                         var endVb=beginVb+neiR[v]-1;

                         var iu:int;
                         var jv:int;
                         var eu:int;
                         var ev:int;
                         if ((EdgeDeleted[i]==-1) && (u!=v) ){
                           iu=beginUf;
                           jv=beginVf;
                           while ( (iu <=endUf) &&   (jv<=endVf) && (nei[u]>0) && (nei[v]>0))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }  

                           iu=beginUf;
                           jv=beginVb;
                           while ( (iu <=endUf) &&   (jv<=endVb) && (nei[u]>0) && (neiR[v]>0) )  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             ev=findEdge(dstR[jv],v);
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }



                           iu=beginUb;
                           jv=beginVf;
                           while ( (iu <=endUb) &&   (jv<=endVf) && (neiR[u]>0) && (nei[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }


                           iu=beginUb;
                           jv=beginVb;
                           while ( (iu <=endUb) &&   (jv<=endVb) && (neiR[u]>0) && (neiR[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             ev=findEdge(dstR[jv],v);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }
                        }//end of if
                               TriCount[i]=Count;


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoNaivePathMerge, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaivePathMerge, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaivePathMerge, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaivePathMerge, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoNaivePathMerge



      proc TrussDecoNaiveMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          ConFlag=true;
          while (ConFlag) {

              // first we calculate the number of triangles using mininum search  method.
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i]=0;
                           var Count:int;
                           Count=0;
                           if (EdgeDeleted[i]==-1) {
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
                                         forall j in nextStart..nextEnd with (+ reduce Count){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //for j in nextStart..nextEnd {
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]==-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce Count ){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //forall j in nextStart..nextEnd {
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      //TriCount[i]+=1;
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting

                           }// i is an undeleted edge
                               TriCount[i]=Count;


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                                   } else {
                                       if TriCount[i]<MinNumTri[here.id] {
                                           MinNumTri[here.id]=TriCount[i];
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoNaiveMinSearch, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveMinSearch, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveMinSearch, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNaiveMinSearch, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoNaiveMinSearch



      proc TrussDecoPathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          //while (ConFlag) {
          {

              // first we calculate the number of triangles
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge {
                         TriCount[i].write(0);
                         var Count=0:int;
                         var u = src[i];
                         var v = dst[i];
                         var beginUf=start_i[u];
                         var endUf=beginUf+nei[u]-1;

                         var beginUb=start_iR[u];
                         var endUb=beginUb+neiR[u]-1;

                         var beginVf=start_i[v];
                         var endVf=beginVf+nei[v]-1;

                         var beginVb=start_iR[v];
                         var endVb=beginVb+neiR[v]-1;

                         var iu:int;
                         var jv:int;
                         var eu:int;
                         var ev:int;
                         if ((EdgeDeleted[i]==-1) && (u!=v) ){
                           iu=beginUf;
                           jv=beginVf;
                           while ( (iu <=endUf) &&   (jv<=endVf) && (nei[u]>0) && (nei[v]>0))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }  

                           iu=beginUf;
                           jv=beginVb;
                           while ( (iu <=endUf) &&   (jv<=endVb) && (nei[u]>0) && (neiR[v]>0) )  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             ev=findEdge(dstR[jv],v);
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dst[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dst[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }



                           iu=beginUb;
                           jv=beginVf;
                           while ( (iu <=endUb) &&   (jv<=endVf) && (neiR[u]>0) && (nei[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dst[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }


                           iu=beginUb;
                           jv=beginVb;
                           while ( (iu <=endUb) &&   (jv<=endVb) && (neiR[u]>0) && (neiR[v]>0))  {
                             eu=findEdge(dstR[iu],u);
                             ev=findEdge(dstR[jv],v);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             {
                                 if dstR[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     Count+=1;
                                     iu+=1;
                                     jv+=1;
                                 } else {
                                    if dstR[iu]<dstR[jv] {
                                       iu+=1;
                                    } else {
                                       jv+=1;
                                    }
                                 }
                             } 
                           }
                        }//end of if
                               TriCount[i].write(Count);


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 

          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){

                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i].read() <MinNumTri[here.id]) {
                                            MinNumTri[here.id]=TriCount[i].read();
                                       }
                                  }
                               }

                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF

                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF  {


                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges


                                  var u = src[i];
                                  var v = dst[i];
                                  var beginUf=start_i[u];
                                  var endUf=beginUf+nei[u]-1;
 
                                  var beginUb=start_iR[u];
                                  var endUb=beginUb+neiR[u]-1;

                                  var beginVf=start_i[v];
                                  var endVf=beginVf+nei[v]-1;

                                  var beginVb=start_iR[v];
                                  var endVb=beginVb+neiR[v]-1;

                                  var iu:int;
                                  var jv:int;
                                  var eu:int;
                                  var ev:int;
                                  if ( (u!=v) ){// edge <u,v> is not a self-loop
                                    iu=beginUf;
                                    jv=beginVf;
                                    if  ((nei[u]<2) || (nei[v]==0)) {
                                        iu=endUf+1;
                                    }
                                    while ( (iu <=endUf) &&   (jv<=endVf)  )  {
                                      if  ( (EdgeDeleted[iu] >0 ) || (dst[iu]==v) || (dst[iu]==u)) {
                                            iu+=1;
                                            continue;
                                      }
                                      if ( (EdgeDeleted[jv] >0 ) || (dst[jv]==u)|| (dst[jv]==v) ) {
                                           jv+=1;
                                           continue;
                                      }
                                      {
                                          if dst[iu]==dst[jv] {
                                              if (EdgeDeleted[iu]==-1) && (EdgeDeleted[jv]==-1) {
                                                  TriCount[iu].sub(1);
                                                  TriCount[jv].sub(1);
                                              } else {
                                                  if (EdgeDeleted[jv]==-1) && (i<iu) {
                                                      TriCount[jv].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[iu]==-1) && (i<jv) {
                                                          TriCount[iu].sub(1);
                                                      }
                                                  }

                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                              if dst[iu]<dst[jv] {
                                                 iu+=1;
                                              } else {
                                                 jv+=1;
                                             }
                                          }
                                      } 
                                    }  

                                    iu=beginUf;
                                    jv=beginVb;
                                    if  ((nei[u]<2) || (neiR[v]==0)) {
                                        iu=endUf+1;
                                    }
                                    while ( (iu <=endUf) &&   (jv<=endVb) )  {
                                      if  ( (EdgeDeleted[iu] >0) || (dst[iu]==v)|| (dst[iu]==u) ) {
                                           iu+=1;
                                           continue;
                                      }
                                      ev=exactEdge(dstR[jv],v);
                                      if (ev!=-1) {
                                          if ( (EdgeDeleted[ev]>0) || (dstR[jv]==u)|| (dstR[jv]==v)) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dst[iu]==dstR[jv] {
                                              if (EdgeDeleted[iu]==-1) && (EdgeDeleted[ev]==-1) {
                                                  TriCount[iu].sub(1);
                                                  TriCount[ev].sub(1);
                                              } else {
                                                  if (EdgeDeleted[ev]==-1) && (i<iu) {
                                                      TriCount[ev].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[iu]==-1) && (i<ev) {
                                                          TriCount[iu].sub(1);
                                                      }
                                                  }

                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                              if dst[iu]<dstR[jv] {
                                                 iu+=1;
                                              } else {
                                                 jv+=1;
                                              }
                                          }
                                      } 
                                    }



                                    iu=beginUb;
                                    jv=beginVf;
                                    if  ((neiR[u]<1) || (nei[v]<1)) {
                                        iu=endUb+1;
                                    }
                                    while ( (iu <=endUb) &&   (jv<=endVf) )  {
                                      eu=exactEdge(dstR[iu],u);
                                      if (eu!=-1){
                                          if  ( (EdgeDeleted[eu] >0) || (dstR[iu]==v)|| (dstR[iu]==u) ) {
                                               iu+=1;
                                               continue;
                                          }
                                          if ( (EdgeDeleted[jv] >0) || (dst[jv]==u) || (dst[jv]==v)) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dstR[iu]==dst[jv] {
                                              if (EdgeDeleted[eu]==-1) && (EdgeDeleted[jv]==-1) {
                                                  TriCount[eu].sub(1);
                                                  TriCount[jv].sub(1);
                                              } else {
                                                  if (EdgeDeleted[jv]==-1) && (i<eu) {
                                                      TriCount[jv].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[eu]==-1) && (i<jv) {
                                                          TriCount[eu].sub(1);
                                                      }
                                                  }
                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                             if dstR[iu]<dst[jv] {
                                                iu+=1;
                                             } else {
                                                jv+=1;
                                             }
                                          }
                                      } 
                                    }


                                    iu=beginUb;
                                    jv=beginVb;
                                    if  ((neiR[u]<1) || (neiR[v]<2)) {
                                        iu=endUb+1;
                                    }
                                    while ( (iu <=endUb) &&   (jv<=endVb) )  {
                                      eu=exactEdge(dstR[iu],u);
                                      ev=exactEdge(dstR[jv],v);
                                      if ((eu!=-1)&&(ev!=-1)){

                                          if  ( (EdgeDeleted[eu] >0) || (dstR[iu]==v) || (dstR[iu]==u) ) {
                                               iu+=1;
                                               continue;
                                          }
                                          if ( (EdgeDeleted[ev] >0)  || (dstR[jv]==u) || (dstR[jv]==v)  ) {
                                               jv+=1;
                                               continue;
                                          }
                                      } else
                                      {
                                          writeln("there is something wrong in the graph");
                                          break;
                                      }
                                      {
                                          if dstR[iu]==dstR[jv] {
                                              if (EdgeDeleted[eu]==-1) && (EdgeDeleted[ev]==-1) {
                                                  TriCount[eu].sub(1);
                                                  TriCount[ev].sub(1);
                                              } else {
                                                  if (EdgeDeleted[ev]==-1) && (i<eu) {
                                                      TriCount[ev].sub(1);
                                                  }else {
                                                      if (EdgeDeleted[eu]==-1) && (i<ev) {
                                                          TriCount[eu].sub(1);
                                                      }
                                                  }
                                              }
                                              iu+=1;
                                              jv+=1;
                                          } else {
                                             if dstR[iu]<dstR[jv] {
                                                iu+=1;
                                             } else {
                                                jv+=1;
                                             }
                                          }
                                      } 
                                    }

                                  }// end of if ( (u!=v) )

                              }// end of if (xlocal(i,startEdge,endEdge)) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 

                  //outMsg="After forall ";
                  //smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                  coforall loc in Locales  {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoPathMerge, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoPathMerge, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoPathMerge, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoPathMerge, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoPathMerge



      proc TrussDecoNonMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          //while (ConFlag) {
          {

              // first we calculate the number of triangles using mininum search  method.
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i].write(0);
                           var Count:int;
                           Count=0;
                           if (EdgeDeleted[i]==-1) {
                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1]+neiR[v1];
                                  var    dv2=nei[v2]+neiR[v2];
                                  var    sv1:int;
                                  var    lv2:int;
                                  var    sdv1:int;
                                  var    ldv2:int;





                                  {
                                        sv1=v1;
                                        lv2=v2;
                                        sdv1=dv1;
                                        ldv2=dv2;
                                  } 
                                  {
                                      var nextStart=start_i[sv1];
                                      var nextEnd=start_i[sv1]+nei[sv1]-1;
                                      if (nei[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce Count){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //for j in nextStart..nextEnd {
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                            tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]==-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce Count ){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //forall j in nextStart..nextEnd {
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                          tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      //TriCount[i]+=1;
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting

                           }// i is an undeleted edge
                               TriCount[i].write(Count);


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){

                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i].read() <MinNumTri[here.id]) {
                                            MinNumTri[here.id]=TriCount[i].read();
                                       }
                                  }
                               }

                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1]+neiR[v1];
                                  var    dv2=nei[v2]+neiR[v2];
                                  var    sv1:int;
                                  var    lv2:int;
                                  var    sdv1:int;
                                  var    ldv2:int;





                                  {
                                        sv1=v1;
                                        lv2=v2;
                                        sdv1=dv1;
                                        ldv2=dv2;
                                  } 
                                  {
                                      var nextStart=start_i[sv1];
                                      var nextEnd=start_i[sv1]+nei[sv1]-1;
                                      if (nei[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                            tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {


                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {

                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=findEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       {
                                                          tmpe=findEdge(lv2,v4);
                                                       } 
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e1].sub(1);

                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       } 
                                                                   } 
                                                               }
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of affected edge search 



                              } // end if (xlocal(i,startEdge,endEdge) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 


                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoNonMinSearch, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNonMinSearch, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNonMinSearch, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoNonMinSearch, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoNonMinSearch



      proc TrussDecoMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          //while (ConFlag) {
          {

              // first we calculate the number of triangles using mininum search  method.
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                         TriCount[i].write(0);
                           var Count:int;
                           Count=0;
                           if (EdgeDeleted[i]==-1) {
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
                                         forall j in nextStart..nextEnd with (+ reduce Count){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //for j in nextStart..nextEnd {
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]==-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (+ reduce Count ){
                                         //forall j in nextStart..nextEnd with (ref SetNextF){
                                         //forall j in nextStart..nextEnd {
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      //TriCount[i]+=1;
                                                                      Count+=1;
                                                               } 
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of triangle counting

                           }// i is an undeleted edge
                               TriCount[i].write(Count);


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 

          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){

                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i].read() <MinNumTri[here.id]) {
                                            MinNumTri[here.id]=TriCount[i].read();
                                       }
                                  }
                               }

                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;

              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
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
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<=dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {


                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {

                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=findEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (EdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (EdgeDeleted[e1]==-1) && (EdgeDeleted[tmpe]==-1) ) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e1].sub(1);

                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                       } 
                                                                   } 
                                                               }
                                                         }
                                                       }
                                                }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                  }// end of affected edge search 



                              } // end if (xlocal(i,startEdge,endEdge) 

                           } // end forall i in SetCurF with (ref SetNextF) 


                      } //end on loc 
                  } //end coforall loc in Locales 


                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  // then we try to remove the affected edges
                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoMinSearch, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoMinSearch, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoMinSearch, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoMinSearch, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoMinSearch



      proc TrussDecoMix(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:Timer;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,int);
          MinNumTri=1000000;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur==0) ) {
                    return -1;
               }
               var u=src[cur]:int;
               var v=dst[cur]:int;
               var lu=start_i[u]:int;
               var nu=nei[u]:int;
               var lv=start_i[v]:int;
               var nv=nei[v]:int;
               var DupE:int;
               if ((nu<=1) || (cur<=lu)) {
                   DupE=-1;
               } else {
                   
                   DupE =binSearchE(dst,lu,cur-1,v);
               }
               if (DupE!=-1) {
                    EdgeDeleted[cur]=k-1;
                    RemovedEdge.add(1);
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                           RemovedEdge.add(1);
                      }
                   }
               }
               return DupE;
          }

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
          }
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

          //coforall loc in Locales {
          //    on loc {
          {
              {
                    //var ld = src.localSubdomain();
                    //var startEdge = ld.low;
                    //var endEdge = ld.high;
                    var startEdge = 0;
                    var endEdge = Ne-1;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if (  (nei[v1]+neiR[v1])<k-1  || 
                             ((nei[v2]+neiR[v2])<k-1) || (v1==v2)) {
                              //we will delete all the edges connected with a vertex only has very small degree 
                              //(less than k-1)
                              if (EdgeDeleted[i]==-1) {
                                  EdgeDeleted[i]=k-1;
                                  RemovedEdge.add(1);
                              }
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          writeln("Preprocessing removed ",RemovedEdge.read(), " edges");

          //writeln("After Preprocessing");


          timer.start();
          //while (ConFlag) {
          {

              // first we calculate the number of triangles
              coforall loc in Locales with ( ref SetNextF) {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;


                     forall i in startEdge..endEdge {
                         TriCount[i].write(0);
                     }
                     //forall i in startEdge..endEdge with(ref SetCurF){
                     forall i in startEdge..endEdge {
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u];
                         var dv=nei[v];
                         {
                             var beginTmp=start_i[u];
                             var endTmp=beginTmp+nei[u]-1;
                             if ((EdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[u]>1)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref uadj) {
                                   forall x in dst[beginTmp..endTmp]  {
                                       var  e=exactEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 // wedge case i<e, u->v, u->x
                                                 if (e3!=-1) {
                                                     if (EdgeDeleted[e3]==-1) {
                                                         TriCount[i].add(1);
                                                         TriCount[e].add(1);
                                                         TriCount[e3].add(1);
                                                     }
                                                 }
                                          }
                                       }
                                   }
                                }
                             }
                            
                             beginTmp=start_i[v];
                             endTmp=beginTmp+nei[v]-1;
                             if ((EdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[v]>0)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                   forall j in beginTmp..endTmp {
                                       var  x=dst[j];
                                       if ((EdgeDeleted[j] ==-1) && (x !=u) && (i<j)) {
                                                 var e3=exactEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1)  && (i<e3)) {
                                                         // cycle case i<j,i<e3, u->v->x->u
                                                         TriCount[i].add(1);
                                                         TriCount[j].add(1);
                                                         TriCount[e3].add(1);
                                                     }
                                                 }
                                       }
                                   }
                                }
                             }

                        }// end of if du<=dv
                  }// end of forall. We get the number of triangles for each edge


                }// end of  on loc 
              } // end of coforall loc in Locales 



          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {


              // here we mark the edges whose number of triangles is less than k-2 as 1-k
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){

                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i].read() <MinNumTri[here.id]) {
                                            MinNumTri[here.id]=TriCount[i].read();
                                       }
                                  }
                               }

                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;


              while (SetCurF.getSize()>0) {
                  //first we build the edge set that will be affected by the removed edges in SetCurF
                  coforall loc in Locales with ( ref SetNextF) {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall i in SetCurF with (ref SetNextF) {
                              if (xlocal(i,startEdge,endEdge)) {//each local only check the owned edges

                                  var    v1=src[i];
                                  var    v2=dst[i];
                                  var    dv1=nei[v1];
                                  var    dv2=nei[v2];

                                  {
                                      var nextStart=start_i[v1];
                                      var nextEnd=start_i[v1]+nei[v1]-1;
                                      if (nei[v1]>1) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==v1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( v2!=v4 ) ) {
                                                       //v1->v2, v1->v4
                                                       tmpe=findEdge(v2,v4);
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   //if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                   if ((EdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                      if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                      }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if EdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_i[v2];
                                      nextEnd=start_i[v2]+nei[v2]-1;
                                      if (nei[v2]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==v2
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (EdgeDeleted[j]<=-1) && ( v1!=v4 )  ) {
                                                       tmpe=exactEdge(v4,v1);
                                                       // cycle case v1->v2->v4->v1
                                                       if (tmpe!=-1)  {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[j].sub(1);
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if


                                      //check the case of x->v1 and x->v2
                                      nextStart=start_iR[v1];
                                      nextEnd=start_iR[v1]+neiR[v1]-1;
                                      var dv1=neiR[v1];
                                      var dv2=neiR[v2];
                                      if ((dv1<=dv2) && (dv1>0)) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//v3==v1
                                             var v4=dstR[j];
                                             var e2=exactEdge(v4,v3);
                                             if (EdgeDeleted[e2]<=-1) {
                                                var tmpe=exactEdge(v4,v2);
                                                if (tmpe!=-1) {
                                                               if ((EdgeDeleted[e2]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e2].sub(1);
                                                               } 
                                                }
                                             }
                                          }
                                      } else {
                                         nextStart=start_iR[v2];
                                         nextEnd=start_iR[v2]+neiR[v2]-1;
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//v3==v2
                                             var v4=dstR[j];
                                             var e2=exactEdge(v4,v3);
                                             if (EdgeDeleted[e2]<=-1) {
                                                var tmpe=exactEdge(v4,v1);
                                                if (tmpe!=-1) {
                                                               if ((EdgeDeleted[e2]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      TriCount[e2].sub(1);
                                                               } 
                                                }
                                             }
                                          }
                                      } 

                                  }


                              } // end if (xlocal(i,startEdge,endEdge) 
                           } // end forall i in SetCurF with (ref SetNextF) 
                      } //end on loc 
                  } //end coforall loc in Locales 

                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         forall i in SetCurF {
                              if (xlocal(i,startEdge,endEdge) ) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  RemovedEdge.add(SetCurF.getSize());
                  SetCurF.clear();

                  coforall loc in Locales with (ref SetCurF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;
                         // each locale only handles the edges owned by itself
                         forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1)  {
                                  if  (TriCount[i].read() < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                      if (TriCount[i].read() < MinNumTri[here.id]) {
                                           MinNumTri[here.id]=TriCount[i].read();
                                      }
                                  }
                               }
                         }
                      }// end of  on loc 
                  } // end of coforall loc in Locales 

                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 





              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  if (RemovedEdge.read()<Ne) {
                          ConFlag=true;
                          var tmp=MinNumTri[0];
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i] {
                                   tmp=MinNumTri[i];
                               }
                          }
                          k=tmp+2;
                          MinNumTri=1000000;
                          largest=RemovedEdge.read();
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();


          outMsg="After TrussDecoMix, Max K="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoMix, Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoMix, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After TrussDecoMix, The largest number of k truss edges ="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }// end of proc TrussDecoMix



//End of Truss Decomposition Functions
//@@@@@@@@@@@@@@@@@@@@@@@@@@@@


//@@@@@@@@@@@@@@@@@@@@@@@@@@@@
//Begin of Undirected Graph 



      if (!Directed) {//for undirected graph



          if (kValue>0) {// k-truss analysis


                var PTriCount=makeDistArray(Ne,int);


                PTriCount=0;
                gEdgeDeleted=-1;


                PTriCount=0;
                gEdgeDeleted=-1;


                PTriCount=0;
                gEdgeDeleted=-1;


                PTriCount=0;
                gEdgeDeleted=-1;

                repMsg=kTrussNaivePathMerge(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      PTriCount,gEdgeDeleted);



                PTriCount=0;
                gEdgeDeleted=-1;

                repMsg=kTrussNaiveMinSearch(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      PTriCount,gEdgeDeleted);



                var AtoTriCount=makeDistArray(Ne,atomic int);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=kTrussPathMerge(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=kTrussNonMinSearch(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=kTrussMinSearch(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=kTrussMix(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);



          }// end of k-truss analysis


          if (kValue==-1) {// max k-truss analysis
                var PTriCount=makeDistArray(Ne,int);


                PTriCount=0;
                gEdgeDeleted=-1;

                repMsg=MaxTrussNaivePathMerge(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      PTriCount,gEdgeDeleted);



                var AtoTriCount=makeDistArray(Ne,atomic int);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=MaxTrussPathMerge(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=MaxTrussNonMinSearch(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=MaxTrussMinSearch(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=MaxTrussMix(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);



          }// end of max k-truss analysis


          if (kValue==-2) {
                var PTriCount=makeDistArray(Ne,int);


                PTriCount=0;
                gEdgeDeleted=-1;

                kValue=3;
                repMsg=TrussDecoNaivePathMerge(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      PTriCount,gEdgeDeleted);



                PTriCount=0;
                gEdgeDeleted=-1;

                kValue=3;
                repMsg=TrussDecoNaiveMinSearch(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      PTriCount,gEdgeDeleted);



                var AtoTriCount=makeDistArray(Ne,atomic int);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                kValue=3;
                repMsg=TrussDecoPathMerge(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                kValue=3;
                repMsg=TrussDecoNonMinSearch(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                kValue=3;
                repMsg=TrussDecoMinSearch(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                kValue=3;
                repMsg=TrussDecoMix(kValue,


                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,


                      AtoTriCount,gEdgeDeleted);



          }// end of truss decomposition analysis



      } //end of  undirected graph
      

//End of Undirected Graph Test
//@@@@@@@@@@@@@@@@@@@@@@@@@@@@




      return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedTruss", segTrussMsg);
    }


}


