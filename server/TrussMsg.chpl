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
  



  //In this procedure, we implement different Truss analysis methods, including k-truss, max truss and truss decomposition
  proc segTrussMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
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

      var EdgeDeleted=makeDistArray(Ne,int); //we need a global instead of local array
      var lEdgeDeleted=makeDistArray(Ne,int); //we need a global instead of local array
      var AllRemoved:bool;
      EdgeDeleted=-1;
      lEdgeDeleted=-1;

      //writeln("enter truss analysis");

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
          //writeln("Degree value=",dNumber);
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








      // Begin of KTruss analysis series

      // For undirected graph, using Naive and list intersection method. It should have worst performance.
      // This procedure is just used for worst case test
      proc kTrussNaiveListIntersection(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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
          //here we begin the first naive version
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
                              EdgeDeleted[i]=k-1;
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  EdgeDeleted[i]=k-1;
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          //After Preprocessing

          timer.start();
          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {
              //ConFlag=false;
              // first we calculate the number of triangles
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                               TriCount[i] = Count;
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
                               if ((EdgeDeleted[i]==-1) && (TriCount[i] < k-2)) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              }
              SetCurF.clear();

              N2+=1;
          }// end while 



          timer.stop();
          AllRemoved=true;
          var tmpi=0;
          for i in 0..Ne-1  {
              if (EdgeDeleted[i]==-1) {
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }

          outMsg="After KTruss Naive List Intersection,Given k="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussNaiveListIntersection



      // For undirected graph, using naive method. Its performance should be worse, but it is a simple implementation to 
      // check the correctness of the results
      proc kTrussNaive(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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


          //here we begin the first naive version
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
                              EdgeDeleted[i]=k-1;
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  EdgeDeleted[i]=k-1;
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          //After Preprocessing

          timer.start();
          //we will try to remove all the unnecessary edges in the graph
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
                                   TriCount[i] = Count;
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
                               if ((EdgeDeleted[i]==-1) && (TriCount[i] < k-2)) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              }
              SetCurF.clear();

              N2+=1;
          }// end while 



          timer.stop();
          AllRemoved=true;
          var tmpi=0;
          for i in 0..Ne-1  {
              if (EdgeDeleted[i]==-1) {
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }

          outMsg="After KTruss Naive,Given k="+k:string+" All removed="+AllRemoved:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussNaive


      //For undirected graph, we use list intersection to calculate the number of triangles. 
      //But affected edge search is normal. 
      //This procedure is used to show how list intersection can affect the performance compared with our edges search method.
      proc kTrussListIntersection(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var timer:Timer;

          //To have unique results, we remove the duplicated edges.
          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
               if (  (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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

          //here we begin the timer
          // we first removed the duplicated and cycle edges.
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
                              EdgeDeleted[i]=k-1;
                              //writeln("For k=",k," We have removed the edge ",i, "=<",v1,",",v2,">");
                              //writeln("Degree of ",v1,"=",nei[v1]+neiR[v1]," Degree of ",v2, "=",nei[v2]+neiR[v2]);
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //writeln("My locale=",here.id, " Find duplicated edges ",i,"=<",src[i],",",dst[i],"> and ", DupE,"=<", src[DupE],",",dst[DupE],">");
                                  EdgeDeleted[i]=k-1;
                             }
                        }
                    }
              }        
          }// end of coforall loc        
          //After Preprocessing


          timer.start();
          {
              // first we calculate the number of triangles using list intersection method.
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
                            if ( (nei[u]>1)  ){
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                                   // I found that the contains operation is very expensive in Chapel, we should avoid it.
                                   // This is the reason why list intersection has bad performance

                                      Count +=1;
                                   }
                               }
                               TriCount[i] = Count;
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
                               if ((EdgeDeleted[i]==-1) && (TriCount[i] < k-2)) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we remove as many edges as possible in the following code in once iteration
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
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      SetNextF.add((i,tmpe));
                                                                      SetNextF.add((i,j));
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                       SetNextF.add((i,j));
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                           SetNextF.add((i,tmpe));
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
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1==-1) {
                                                   //writeln("Error! Cannot find the edge ",j,"=(",v4,",",v3,")");
                                             } else {
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
                                                                      SetNextF.add((i,tmpe));
                                                                      SetNextF.add((i,e1));
                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                       SetNextF.add((i,e1));
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                           SetNextF.add((i,tmpe));
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
                              if (xlocal(i,startEdge,endEdge) && (EdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  SetCurF.clear();
                  // then we try to remove the affected edges
                  coforall loc in Locales  {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           var rset = new set((int,int), parSafe = true);

                           forall (i,j) in SetNextF with(ref rset)  {
                              if (xlocal(j,startEdge,endEdge)) {//each local only check the owned edges
                                             rset.add((i,j));// just want (i,j) is unique in rset
                              }
                           }// end of forall
                           for (i,j) in rset  {
                                if (EdgeDeleted[j]==-1) {
                                    TriCount[j]-=1;
                                    if (TriCount[j]<k-2) {
                                       EdgeDeleted[j]=1-k;
                                       SetCurF.add(j);
                                    }
                                }
                           }
                      } //end on loc 
                  } //end coforall loc in Locales 
                  RemovedEdge+=SetCurF.getSize();
                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          var tmpi=0;
          for i in 0..Ne-1  {
              if (EdgeDeleted[i]==-1) {
                  //writeln("remove the ",tmpi, " edge ",i);
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }


          outMsg="After KTruss List Intersection,Given K="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss List Intersection,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss List Intersection,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss List Intersection,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTruss List Intersection, (the method can be updated)


      //For undirected graph, we use triangle search method. This should be our typical method.
      //The performance should be good.
      proc kTruss(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] atomic int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
               if (  (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
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


          //First off, we remove the duplicated and cycle edges. This is common for all methods.
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
                              EdgeDeleted[i]=k-1;
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                        }
                    }
              }        
          }// end of coforall loc        
          //After Preprocessing


          timer.start();

          {
              // first we calculate the number of triangles
              coforall loc in Locales with ( ref SetNextF) {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;


                     forall i in startEdge..endEdge with(ref SetCurF){
                         var sVadj = new set(int, parSafe = true);
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u]+neiR[u];
                         var dv=nei[v]+neiR[v];
                         var sV:int;
                         var lV:int;
                         var ldV:int;

                         if ( du<=dv ) {
                             sV=u;
                             lV=v;
                             ldV=dv;
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
                                       if (ds1<=ldV) {
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
                                   TriCount[i].write(Count);
                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 


                  }// end of forall. We get the number of triangles for each edge


                }// end of  on loc 
              } // end of coforall loc in Locales 



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
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[e1].sub(1);
                                                                      if TriCount[e1].read() <k-2 {
                                                                         SetNextF.add((i,e1));
                                                                      }

                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                      if TriCount[e1].read() <k-2 {
                                                                         SetNextF.add((i,e1));
                                                                      }
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                              if (xlocal(i,startEdge,endEdge) && (EdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  SetCurF.clear();
                  // then we try to remove the affected edges
                  coforall loc in Locales  {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;

                           forall (i,j) in SetNextF  {
                             if (xlocal(j,startEdge,endEdge)) {//each locale only check its owned edges
                                if (EdgeDeleted[j]==-1) {
                                       EdgeDeleted[j]=1-k;
                                       SetCurF.add(j);
                                }
                             }
                           }
                      } //end on loc 
                  } //end coforall loc in Locales 
                  RemovedEdge+=SetCurF.getSize();
                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          var tmpi=0;
          for i in 0..Ne-1  {
              if (EdgeDeleted[i]==-1) {
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }


          outMsg="After KTruss,Given K="+k:string +" All Removed="+AllRemoved:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTruss
                    



      //For undirected graph, mix the two data structure methods to search triangles. 
      //This should be the best one.
      proc kTrussMix(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                           neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] atomic int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
               if (  (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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

          //here we first remove the duplicated and cycle edges
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
                              EdgeDeleted[i]=k-1;
                              //writeln("For k=",k," We have removed the edge ",i, "=<",v1,",",v2,">");
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                        }
                    }
              }        
          }// end of coforall loc        
          //writeln("After Preprocessing");

          timer.start();
          //we will try to remove all the unnecessary edges in the graph
          //while (ConFlag) {
          //we should not need the loop for non-naive version
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
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
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
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=exactEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 var e3=exactEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1) && (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
                                                         // cycle case i<e,i<e3, u->v->x->u
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

                        }// end of if du<=dv
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
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   //if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                   if ((EdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                      if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read()<k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                             //EdgeDeleted[tmpe]=1-k;
                                                                          }
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
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                                             if (EdgeDeleted[e2]==-1) {
                                                var tmpe=exactEdge(v4,v2);
                                                if (tmpe!=-1) {
                                                    if (EdgeDeleted[tmpe]==-1) {
                                                         TriCount[e2].sub(1);
                                                         if TriCount[e2].read() <k-2 {
                                                                 SetNextF.add((i,e2));
                                                         }
                                                         TriCount[tmpe].sub(1);
                                                         if TriCount[tmpe].read() <k-2 {
                                                                 SetNextF.add((i,tmpe));
                                                         }
                                                    }
                                                }
                                             }
                                          }
                                      } else {
                                         if (dv2>0) {

                                             nextStart=start_iR[v2];
                                             nextEnd=start_iR[v2]+neiR[v2]-1;
                                             forall j in nextStart..nextEnd with (ref SetNextF){
                                                 var v3=srcR[j];//v3==v2
                                                 var v4=dstR[j];
                                                 var e2=exactEdge(v4,v3);
                                                 if (EdgeDeleted[e2]==-1) {
                                                    var tmpe=exactEdge(v4,v1);
                                                    if (tmpe!=-1) {
                                                        if (EdgeDeleted[tmpe]==-1) {
                                                             TriCount[e2].sub(1);
                                                             if TriCount[e2].read() <k-2 {
                                                                     SetNextF.add((i,e2));
                                                             }
                                                             TriCount[tmpe].sub(1);
                                                             if TriCount[tmpe].read() <k-2 {
                                                                     SetNextF.add((i,tmpe));
                                                             } 
                                                        }
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
                              if (xlocal(i,startEdge,endEdge) && (EdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  SetCurF.clear();
                  coforall loc in Locales with (ref SetNextF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;

                         forall (i,j) in SetNextF  {
                            if (xlocal(j,startEdge,endEdge)) {//each local only check the owned edges
                                       EdgeDeleted[j]=1-k;
                                       SetCurF.add(j);
                            }
                         }// end of forall

                      }
                  }
                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 
              N2+=1;

          }// end while 


          timer.stop();
          AllRemoved=true;
          var tmpi=0;
          for i in 0..Ne-1  {
              if (EdgeDeleted[i]==-1) {
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }


          outMsg="After KTruss,Given K="+k:string +" All Removed="+AllRemoved:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTrussMix,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTrussMix,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTrussMix,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussMix






      //For directed graph, using the naive method. The performance should be bad.
      proc kTrussNaiveDirected(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var TriCount=makeDistArray(Ne,atomic int);
          var EReverse=makeDistArray(Ne,set((int,int),parSafe = true) );
          forall i in TriCount {
              i.write(0);
          }
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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


          //here we begin the first naive version
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
                        if ( v1==v2) {
                              EdgeDeleted[i]=k-1;
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          //writeln("After Preprocessing");

          timer.start();
          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {
              //ConFlag=false;
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
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if (EdgeDeleted[e3]==-1) {
                                                         TriCount[i].add(1);
                                                         TriCount[e].add(1);
                                                         TriCount[e3].add(1);
                                                         EReverse[e3].add((i,e));
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
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1) && (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
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

                        }// end of if du<=dv
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
                               if ((EdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 



       
              ConFlag=false;
              if SetCurF.getSize()>0 {
                  ConFlag=true;
              }
              SetCurF.clear();

              // we try to remove as many edges as possible in the following code
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          var tmpi=0;
          for i in 0..Ne-1  {
              if (EdgeDeleted[i]==-1) {
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }


          outMsg="After KTruss Naive Directed,Given K="+k:string+" All Removed="+AllRemoved:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Directed,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Directed,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Directed,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc NaiveKTrussDirected



      //For directed graph, the straight forward method.
      proc kTrussDirected(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var TriCount=makeDistArray(Ne,atomic int);
          var EReverse=makeDistArray(Ne,set((int,int),parSafe = true) );
          forall i in TriCount {
              i.write(0);
          }
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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


          //here we begin the first naive version
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
                        if ( v1==v2) {
                              EdgeDeleted[i]=k-1;
                              //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //writeln("My locale=",here.id, " Find duplicated edges ",i,"=<",src[i],",",dst[i],"> and ", DupE,"=<", src[DupE],",",dst[DupE],">");
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          //writeln("After Preprocessing");

          timer.start();
          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {
              //ConFlag=false;
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
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if (EdgeDeleted[e3]==-1) {
                                                         TriCount[i].add(1);
                                                         TriCount[e].add(1);
                                                         TriCount[e3].add(1);
                                                         EReverse[e3].add((i,e));
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
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 //var e3=findEdge(x,v);
                                                 var e3=findEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1) && (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
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

                        }// end of if du<=dv
                  }// end of forall. We get the number of triangles for each edge


                }// end of  on loc 
              } // end of coforall loc in Locales 


              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     forall i in startEdge..endEdge with(ref SetCurF){
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 


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
                                                       tmpe=findEdge(v2,v4);
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   //if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                   if ((EdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                      if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read()<k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                             //EdgeDeleted[tmpe]=1-k;
                                                                          }
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
                                                       if (tmpe!=-1)  {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                      if EReverse[i].size>0 {
                                          forall (e1,e2) in EReverse[i] {
                                                if ((EdgeDeleted[e1]==-1) && (EdgeDeleted[e2]==-1)) {
                                                         TriCount[e1].sub(1);
                                                         if TriCount[e1].read() <k-2 {
                                                                 SetNextF.add((i,e1));
                                                         }
                                                         TriCount[e2].sub(1);
                                                         if TriCount[e2].read() <k-2 {
                                                                 SetNextF.add((i,e2));
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
                              if (xlocal(i,startEdge,endEdge) && (EdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  SetCurF.clear();
                  coforall loc in Locales with (ref SetNextF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;

                         var rset = new set((int,int), parSafe = true);
                         forall (i,j) in SetNextF with(ref rset)  {
                            if (xlocal(j,startEdge,endEdge)) {//each local only check the owned edges
                                       EdgeDeleted[j]=1-k;
                                       SetCurF.add(j);
                            }
                         }// end of forall

                      }
                  }
                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 
              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          var tmpi=0;
          for i in 0..Ne-1  {
              if (EdgeDeleted[i]==-1) {
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }


          outMsg="After KTruss Directed,Given K="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Directed,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Directed,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Directed,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussDirected

      // end of KTruss serial 




      //Begin of Max KTruss Serial

      proc SkMaxTrussNaive(kInput:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] int):bool{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var k=kInput:int;
          var ConFlag=true:bool;
          var RemovedEdge=0: int;
          //var TriCount=makeDistArray(Ne,int);
          //TriCount=0;
          var timer:Timer;


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
          //here we begin the first naive version
          timer.start();

          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {
              // first we calculate the number of triangles
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
                         var du=nei[u]+neiR[u];
                         var dv=nei[v]+neiR[v];
                         if ( du<=dv ) {
                             var beginTmp=start_i[u];
                             var endTmp=beginTmp+nei[u]-1;
                             if ((lEdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[u]>0)  ){
                                   forall x in dst[beginTmp..endTmp] with (ref uadj) {
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((lEdgeDeleted[e] ==-1) && (x !=v)) {
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
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((lEdgeDeleted[e] ==-1) && (x !=v)) {
                                                 uadj.add(x);
                                          }
                                       }  
                                   }
                                }
                            
                                if  (! uadj.isEmpty() ){
                                   var Count=0:int;
                                   forall s in uadj with ( + reduce Count) {
                                       var e=findEdge(s,v);
                                       if ( (e!=-1)  && (e!=i) ) {
                                           if ( EdgeDeleted[e]==-1) {
                                              Count +=1;
                                           }
                                       }
                                   }
                                   TriCount[i] = Count;
                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if
                        } else {

                             var beginTmp=start_i[v];
                             var endTmp=beginTmp+nei[v]-1;
                             if ((EdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[v]>0)  ){
                                   forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((lEdgeDeleted[e] ==-1) && (x !=v)) {
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
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((lEdgeDeleted[e] ==-1) && (x !=u)) {
                                                 vadj.add(x);
                                          }
                                       }  
                                   }
                                }
                            
                                if  (! vadj.isEmpty() ){
                                   var Count=0:int;
                                   forall s in vadj with ( + reduce Count) {
                                       var e=findEdge(s,u);
                                       if ( (e!=-1) && (e!=i) ) {
                                           if ( lEdgeDeleted[e]==-1 ) {
                                              Count +=1;
                                           }
                                       }
                                   }
                                   TriCount[i] = Count;
                                   // here we get the number of triangles of edge ID i
                                }// end of if 


                            }//end of if
                        }
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
                               if ((lEdgeDeleted[i]==-1) && (TriCount[i] < k-2)) {
                                     lEdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 


              //if (!SetCurF.isEmpty()) {
              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              }
              SetCurF.clear();

              N2+=1;
          }// end while 

          coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     forall i in startEdge..endEdge {
                               if (lEdgeDeleted[i]==1-k) {
                                     lEdgeDeleted[i] = k-1;
                               }
                     }
                  }// end of  on loc 
          } // end of coforall loc in Locales 

          var tmpi=0;
          while tmpi<Ne {
                  if (lEdgeDeleted[tmpi]==-1) {
                      return false;
                  } else {
                      tmpi+=1;
                  }
          }
          return true;

      } // end of proc SKMaxTrussNaive










      //For undirected graph.
      proc SkMaxTruss(kInput:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, lEdgeDeleted:[?D6] int ):bool{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var k=kInput:int;
          var ConFlag=true:bool;
          var RemovedEdge=0: int;
          var timer:Timer;


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



          //here we begin the truss version
          timer.start();

          {


              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if ((lEdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     lEdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 


              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              }
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
                                      if (nei[sv1]>1) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==sv1
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (lEdgeDeleted[j]<=-1) && ( lv2!=v4 ) ) {
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if (ldv2<dv4) {
                                                            tmpe=findEdge(lv2,v4);
                                                       } else {
                                                            tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( lEdgeDeleted[tmpe]<=-1 ) {
                                                               if ((lEdgeDeleted[j]==-1) && (lEdgeDeleted[tmpe]==-1)) {

                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }

                                                               } else {
                                                                   if ((lEdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((lEdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if lEdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_iR[sv1];
                                      nextEnd=start_iR[sv1]+neiR[sv1]-1;
                                      if (neiR[sv1]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=srcR[j];//sv1==v3
                                             var v4=dstR[j]; 
                                             var e1=exactEdge(v4,v3);// we need the edge ID in src instead of srcR
                                             var tmpe:int;
                                             if (e1!=-1) {
                                                if ( (lEdgeDeleted[e1]<=-1) && ( lv2!=v4 ) ) {
                                                       // we first check if  the two different vertices can be the third edge
                                                       var dv4=nei[v4]+neiR[v4];
                                                       if ldv2<dv4 {
                                                          tmpe=findEdge(lv2,v4);
                                                       } else {
                                                          tmpe=findEdge(v4,lv2);
                                                       }
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( lEdgeDeleted[tmpe]<=-1 ) {
                                                               if ( (lEdgeDeleted[e1]==-1) && (lEdgeDeleted[tmpe]==-1) ) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[e1].sub(1);
                                                                      if TriCount[e1].read() <k-2 {
                                                                         SetNextF.add((i,e1));
                                                                      }
                                                               } else {
                                                                   if ((lEdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                      if TriCount[e1].read() <k-2 {
                                                                         SetNextF.add((i,e1));
                                                                      }
                                                                   } else { 
                                                                       if ((lEdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                              if (xlocal(i,startEdge,endEdge) && (lEdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  lEdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  SetCurF.clear();
                  // then we try to remove the affected edges
                  coforall loc in Locales  {
                      on loc {

                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           forall (i,j) in SetNextF   {
                              if (xlocal(j,startEdge,endEdge)) {//each local only check the owned edges
                                        if (lEdgeDeleted[j]==-1) {
                                             if (TriCount[j].read()<k-2) {
                                                 lEdgeDeleted[j]=1-k;
                                                 SetCurF.add(j);
                                             }
                                        }

                              }
                           }// end of forall
                      } //end on loc 
                  } //end coforall loc in Locales 
                  tmpN2+=1;
                  //RemovedEdge+=SetCurF.getSize();
                  //SetCurF<=>SetNextF;
                  SetNextF.clear();
              }// end of while (!SetCurF.isEmpty()) 
              N2+=1;
          }// end while 

          coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     forall i in startEdge..endEdge {
                               if (lEdgeDeleted[i]==1-k) {
                                     lEdgeDeleted[i] = k-1;
                               }
                     }
                  }// end of  on loc 
          } // end of coforall loc in Locales 

          var tmpi=0;
          while tmpi<Ne {
                  if (lEdgeDeleted[tmpi]==-1) {
                      return false;
                  } else {
                      tmpi+=1;
                  }
          }
          return true;

      } // end of proc SkMaxTruss





      //For undirected graph.
      proc SkMaxTrussMix(kInput:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int,lEdgeDeleted:[?D6] int):bool{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var k=kInput:int;
          var ConFlag=true:bool;
          var RemovedEdge=0: int;
          var timer:Timer;


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


          //here we begin the first naive version
          timer.start();

          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {



              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if ((lEdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     lEdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 


              ConFlag=false;

              // we try to remove as many edges as possible in the following code
              //while (!SetCurF.isEmpty()) {
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
                                             if ( (lEdgeDeleted[j]<=-1) && ( v2!=v4 ) ) {
                                                       //v1->v2, v1->v4
                                                       tmpe=findEdge(v2,v4);
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( lEdgeDeleted[tmpe]<=-1 ) {
                                                               if ((lEdgeDeleted[j]==-1) && (lEdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((lEdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                      if ((lEdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read()<k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
                                                                      }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }// end of if lEdgeDeleted[j]<=-1
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if nei[v1]>1
    


                                      nextStart=start_i[v2];
                                      nextEnd=start_i[v2]+nei[v2]-1;
                                      if (nei[v2]>0) {
                                         forall j in nextStart..nextEnd with (ref SetNextF){
                                             var v3=src[j];//v3==v2
                                             var v4=dst[j]; 
                                             var tmpe:int;
                                             if ( (lEdgeDeleted[j]<=-1) && ( v1!=v4 )  ) {
                                                       tmpe=exactEdge(v4,v1);
                                                       // cycle case v1->v2->v4->v1
                                                       if (tmpe!=-1)  {// there is such third edge
                                                         if ( lEdgeDeleted[tmpe]<=-1 ) {
                                                               if ((lEdgeDeleted[j]==-1) && (lEdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((lEdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((lEdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                                             if (lEdgeDeleted[e2]==-1) {
                                                var tmpe=exactEdge(v4,v2);
                                                if (tmpe!=-1) {
                                                    if (lEdgeDeleted[tmpe]==-1) {
                                                         TriCount[e2].sub(1);
                                                         if TriCount[e2].read() <k-2 {
                                                                 SetNextF.add((i,e2));
                                                         }
                                                         TriCount[tmpe].sub(1);
                                                         if TriCount[tmpe].read() <k-2 {
                                                                 SetNextF.add((i,tmpe));
                                                         }
                                                    }
                                                }
                                             }
                                          }
                                      } else {
                                         if (dv2>0) {

                                             nextStart=start_iR[v2];
                                             nextEnd=start_iR[v2]+neiR[v2]-1;
                                             forall j in nextStart..nextEnd with (ref SetNextF){
                                                 var v3=srcR[j];//v3==v2
                                                 var v4=dstR[j];
                                                 var e2=exactEdge(v4,v3);
                                                 if (lEdgeDeleted[e2]==-1) {
                                                    var tmpe=exactEdge(v4,v1);
                                                    if (tmpe!=-1) {
                                                        if (lEdgeDeleted[tmpe]==-1) {
                                                             TriCount[e2].sub(1);
                                                             if TriCount[e2].read() <k-2 {
                                                                     SetNextF.add((i,e2));
                                                             }
                                                             TriCount[tmpe].sub(1);
                                                             if TriCount[tmpe].read() <k-2 {
                                                                     SetNextF.add((i,tmpe));
                                                             } 
                                                        }
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
                              if (xlocal(i,startEdge,endEdge) && (lEdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  lEdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  SetCurF.clear();
                  // then we try to remove the affected edges
                  coforall loc in Locales  {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;
                           var rset = new set((int,int), parSafe = true);
                           forall (i,j) in SetNextF with(ref rset)  {
                              if (xlocal(j,startEdge,endEdge)) {//each local only check the owned edges
                                        if (lEdgeDeleted[j]==-1) {
                                             rset.add((i,j));
                                        }

                              }
                           }// end of forall
                           for (i,j) in rset  {
                                if (lEdgeDeleted[j]==-1) {
                                    TriCount[j].sub(1);
                                    if (TriCount[j].read()<k-2) {
                                         lEdgeDeleted[j]=1-k;
                                         SetCurF.add(j);
                                    }
                                }
                           }
                      } //end on loc 
                  } //end coforall loc in Locales 
                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while (!SetCurF.isEmpty()) 
              N2+=1;
          }// end while 

          coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     forall i in startEdge..endEdge {
                               if (lEdgeDeleted[i]==1-k) {
                                     lEdgeDeleted[i] = k-1;
                               }
                     }
                  }// end of  on loc 
          } // end of coforall loc in Locales 

          var tmpi=0;
          while tmpi<Ne {
                  if (lEdgeDeleted[tmpi]==-1) {
                      return false;
                  } else {
                      tmpi+=1;
                  }
          }
          return true;

      } // end of proc SKMaxTrussMix
                    

      //For Directed graph
      proc SkMaxTrussNaiveDirected(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int):bool throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var TriCount=makeDistArray(Ne,atomic int);
          var EReverse=makeDistArray(Ne,set((int,int),parSafe = true) );
          forall i in TriCount {
              i.write(0);
          }
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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


          //here we begin the first naive version
          timer.start();


          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {
              //ConFlag=false;
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
                             if ((lEdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[u]>1)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref uadj) {
                                   forall x in dst[beginTmp..endTmp]  {
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                       } else {
                                          if ((lEdgeDeleted[e] ==-1) && (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if (lEdgeDeleted[e3]==-1) {
                                                         TriCount[i].add(1);
                                                         TriCount[e].add(1);
                                                         TriCount[e3].add(1);
                                                         EReverse[e3].add((i,e));
                                                     }
                                                 }
                                          }
                                       }
                                   }
                                }
                             }
                            
                             beginTmp=start_i[v];
                             endTmp=beginTmp+nei[v]-1;
                             if ((lEdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[v]>0)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((lEdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if ((lEdgeDeleted[e3]==-1) && (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
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

                        }// end of if du<=dv
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
                               if ((lEdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     lEdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;
              if SetCurF.getSize()>0 {
                  ConFlag=true;
              }
              SetCurF.clear();


              N2+=1;
          }// end while 


          timer.stop();


          var tmpi=0;
          while tmpi<Ne {
                  if (lEdgeDeleted[tmpi]==-1) {
                      return false;
                  } else {
                      tmpi+=1;
                  }
          }
          return true;

      } // end of proc SkMaxTrussNaiveDirected


      //For directed graph
      proc SkMaxTrussDirected(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int):bool throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var TriCount=makeDistArray(Ne,atomic int);
          var EReverse=makeDistArray(Ne,set((int,int),parSafe = true) );
          forall i in TriCount {
              i.write(0);
          }
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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


          //here we begin the first naive version
          timer.start();


          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {
              //ConFlag=false;
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
                             if ((lEdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[u]>1)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref uadj) {
                                   forall x in dst[beginTmp..endTmp]  {
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((lEdgeDeleted[e] ==-1) && (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if (lEdgeDeleted[e3]==-1) {
                                                         TriCount[i].add(1);
                                                         TriCount[e].add(1);
                                                         TriCount[e3].add(1);
                                                         EReverse[e3].add((i,e));
                                                     }
                                                 }
                                          }
                                       }
                                   }
                                }
                             }
                            
                             beginTmp=start_i[v];
                             endTmp=beginTmp+nei[v]-1;
                             if ((lEdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[v]>0)  ){
                                   //forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((lEdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if ((lEdgeDeleted[e3]==-1) && (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
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

                        }// end of if du<=dv
                  }// end of forall. We get the number of triangles for each edge


                }// end of  on loc 
              } // end of coforall loc in Locales 


              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     forall i in startEdge..endEdge with(ref SetCurF){
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 


              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if ((lEdgeDeleted[i]==-1) && (TriCount[i].read() < k-2)) {
                                     lEdgeDeleted[i] = 1-k;
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
                                             if ( (lEdgeDeleted[j]<=-1) && ( v2!=v4 ) ) {
                                                       tmpe=findEdge(v2,v4);
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( lEdgeDeleted[tmpe]<=-1 ) {
                                                               if ((lEdgeDeleted[j]==-1) && (lEdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   //if ((lEdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                   if ((lEdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                      if ((lEdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read()<k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                                             if ( (lEdgeDeleted[j]<=-1) && ( v1!=v4 )  ) {
                                                       tmpe=exactEdge(v4,v1);
                                                       if (tmpe!=-1)  {// there is such third edge
                                                         if ( lEdgeDeleted[tmpe]<=-1 ) {
                                                               if ((lEdgeDeleted[j]==-1) && (lEdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((lEdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((lEdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                      if EReverse[i].size>0 {
                                          forall (e1,e2) in EReverse[i] {
                                                if ((lEdgeDeleted[e1]==-1) && (lEdgeDeleted[e2]==-1)) {
                                                         TriCount[e1].sub(1);
                                                         if TriCount[e1].read() <k-2 {
                                                                 SetNextF.add((i,e1));
                                                         }
                                                         TriCount[e2].sub(1);
                                                         if TriCount[e2].read() <k-2 {
                                                                 SetNextF.add((i,e2));
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
                              if (xlocal(i,startEdge,endEdge) && (lEdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  lEdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  SetCurF.clear();
                  coforall loc in Locales with (ref SetNextF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;

                         var rset = new set((int,int), parSafe = true);
                         forall (i,j) in SetNextF with(ref rset)  {
                            if (xlocal(j,startEdge,endEdge)) {//each local only check the owned edges
                                       lEdgeDeleted[j]=1-k;
                                       SetCurF.add(j);
                                       //      rset.add((i,j));// just want (i,j) is unique in rset
                            }
                         }// end of forall

                      }
                  }
                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 
              N2+=1;
          }// end while 


          timer.stop();


          var tmpi=0;
          while tmpi<Ne {
                  if (lEdgeDeleted[tmpi]==-1) {
                      return false;
                  } else {
                      tmpi+=1;
                  }
          }
          return true;

      } // end of proc SkMaxTrussDirected




     //End of Max KTruss Serial








      //Begin of Truss Decomposition serial
      //For undirected graph, using the naive method
      proc TrussDecompositionNaive(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] int):string throws {
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var k=kvalue:int;
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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
          //here we begin the first naive version
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
                              EdgeDeleted[i]=k-1;
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  if (EdgeDeleted[i]==-1) {
                                          //writeln("My locale=",here.id, " before assignment edge ",i," has not been set as true");
                                  }
                                  EdgeDeleted[i]=k-1;
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          //writeln("After Preprocessing");

          timer.start();
          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {
              //ConFlag=false;
              // first we calculate the number of triangles
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
                         var du=nei[u]+neiR[u];
                         var dv=nei[v]+neiR[v];
                         if ( du<=dv ) {
                             var beginTmp=start_i[u];
                             var endTmp=beginTmp+nei[u]-1;
                             if ((EdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[u]>1)  ){
                                   forall x in dst[beginTmp..endTmp] with (ref uadj) {
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
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
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=v)) {
                                                 uadj.add(x);
                                          }
                                       }  
                                   }
                                }
                            
                                if  (! uadj.isEmpty() ){
                                   var Count=0:int;
                                   forall s in uadj with ( + reduce Count) {
                                       var e=findEdge(s,v);
                                       if ( (e!=-1)  && (e!=i) ) {
                                           if ( EdgeDeleted[e]==-1) {
                                              Count +=1;
                                           }
                                       }
                                   }
                                   TriCount[i] = Count;
                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if
                        } else {

                             var beginTmp=start_i[v];
                             var endTmp=beginTmp+nei[v]-1;
                             if ((EdgeDeleted[i]==-1) && (u!=v) ){
                                if ( (nei[v]>0)  ){
                                   forall x in dst[beginTmp..endTmp] with (ref vadj) {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=v)) {
                                                 vadj.add(x);
                                          }
                                       }
                                   }
                                }
                                beginTmp=start_iR[v];
                                endTmp=beginTmp+neiR[v]-1;
                                if ((neiR[v]>1) ){
                                   forall x in dstR[beginTmp..endTmp] with (ref vadj) {
                                       var e=findEdge(x,v);
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=u)) {
                                                 vadj.add(x);
                                          }
                                       }  
                                   }
                                }
                            
                                if  (! vadj.isEmpty() ){
                                   var Count=0:int;
                                   forall s in vadj with ( + reduce Count) {
                                       var e=findEdge(s,u);
                                       if ( (e!=-1) && (e!=i) ) {
                                           if ( EdgeDeleted[e]==-1 ) {
                                              Count +=1;
                                           }
                                       }
                                   }
                                   TriCount[i] = Count;
                                   // here we get the number of triangles of edge ID i
                                }// end of if 


                            }//end of if
                        }
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
                               if ((EdgeDeleted[i]==-1) && (TriCount[i] < k-2)) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 



              if ( SetCurF.getSize()<=0){
                      //ConFlag=false;
                      k+=1;
              }
              SetCurF.clear();

              var tmpi=0;
              ConFlag=false;
              while tmpi<Ne {
                 if (EdgeDeleted[tmpi]==-1) {
                     ConFlag=true;
                     break;
                 } else {
                  tmpi+=1;
                 }
              }

              N2+=1;
          }// end while 



          timer.stop();
          outMsg="After Truss Naive Decomposition , Max K ="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Naive Decomposition ,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Naive Decomposition ,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          AllRemoved=true;
          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc TrussDecompositionNaive




      //For undirected graph, use list intersection  method just for the initial triangle couting.
      proc TrussDecompositionListIntersection(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, 
                        dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] int):string throws{




          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var timer:Timer;
          var k=kvalue;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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
          //here we begin the first naive version
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
                              EdgeDeleted[i]=k-1;
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  EdgeDeleted[i]=k-1;
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          //After Preprocessing

          timer.start();
          ConFlag=true; 
          while (ConFlag) {
              ConFlag=false;
              // first we calculate the number of triangles
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                                   if (e==-1){
                                      //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                   } else {
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
                               TriCount[i] = Count;
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
                               if ((EdgeDeleted[i]==-1) && (TriCount[i] < k-2)) {
                                     EdgeDeleted[i] = k-1;
                                     SetCurF.add(i);
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 

              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();

              if (ConFlag==false) {
                  var tmpi=0;
                  while tmpi<Ne  {
                      if (EdgeDeleted[tmpi]==-1) {
                          ConFlag=true;
                          k=k+1;
                          break;
                      } else {
                          tmpi+=1;
                      }
                  }
              }
              N2+=1;
          }// end while 





          timer.stop();



          outMsg="After Truss Decomposition List Intersection, Max K ="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Decomposition List Intersection,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Decomposition List Intersection, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc TrussDecompositionListIntersection


      //For undirected graph, use triangle search method.
      proc TrussDecomposition(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] atomic int):string throws{





          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var timer:Timer;
          var k=kvalue;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
               if (  (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
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


          //First off, we remove the duplicated and cycle edges. This is common for all methods.
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
                              EdgeDeleted[i]=k-1;
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                        }
                    }
              }        
          }// end of coforall loc        
          //After Preprocessing


          timer.start();

          {
              // first we calculate the number of triangles
              coforall loc in Locales with ( ref SetNextF) {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;


                     forall i in startEdge..endEdge with(ref SetCurF){
                         var sVadj = new set(int, parSafe = true);
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u]+neiR[u];
                         var dv=nei[v]+neiR[v];
                         var sV:int;
                         var lV:int;
                         var ldV:int;

                         if ( du<=dv ) {
                             sV=u;
                             lV=v;
                             ldV=dv;
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
                                       if (ds1<=ldV) {
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
                                   TriCount[i].write(Count);
                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 


                  }// end of forall. We get the number of triangles for each edge


                }// end of  on loc 
              } // end of coforall loc in Locales 

          }


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
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[e1].sub(1);
                                                                      if TriCount[e1].read() <k-2 {
                                                                         SetNextF.add((i,e1));
                                                                      }

                                                               } else {
                                                                   if ((EdgeDeleted[e1]==-1) && (i<tmpe)) {
                                                                      TriCount[e1].sub(1);
                                                                      if TriCount[e1].read() <k-2 {
                                                                         SetNextF.add((i,e1));
                                                                      }
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) &&(i<e1)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                              if (xlocal(i,startEdge,endEdge) && (EdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }

                  SetCurF.clear();
                  // then we try to remove the affected edges
                  coforall loc in Locales  {
                      on loc {
                           var ld = src.localSubdomain();
                           var startEdge = ld.low;
                           var endEdge = ld.high;

                           forall (i,j) in SetNextF  {
                             if (xlocal(j,startEdge,endEdge)) {//each locale only check its owned edges
                                if (EdgeDeleted[j]==-1) {
                                       EdgeDeleted[j]=1-k;
                                       SetCurF.add(j);
                                }
                             }
                           }
                      } //end on loc 
                  } //end coforall loc in Locales 
                  RemovedEdge+=SetCurF.getSize();
                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 





              //check if all edges have been removed
              var tmpi=0;
              while tmpi<Ne  {
                  if (EdgeDeleted[tmpi]==-1) {
                      ConFlag=true;
                      k=k+1;
                      break;
                  } else {
                      tmpi+=1;
                  }
              }
              N2+=1;
          }// end while 


          timer.stop();


          AllRemoved=true;





          outMsg="After Truss Decomposition, Max K ="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Decomposition ,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Decomposition, Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc TrussDecomposition



      //For undirected graph, using mix method.
      proc TrussDecompositionMix(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,TriCount:[?D5] atomic int):string throws{


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var timer:Timer;
          var k=kvalue;


          proc RemoveDuplicatedEdges( cur: int):int {
               //if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
               if (  (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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

          //here we first remove the duplicated and cycle edges
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
                              EdgeDeleted[i]=k-1;
                              //writeln("For k=",k," We have removed the edge ",i, "=<",v1,",",v2,">");
                              // we can safely delete the edge <u,v> if the degree of u or v is less than k-1
                              // we also remove the self-loop like <v,v>
                              if (v1==v2) {
                                   //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                              }
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                        }
                    }
              }        
          }// end of coforall loc        
          //writeln("After Preprocessing");

          timer.start();
          //we will try to remove all the unnecessary edges in the graph
          //while (ConFlag) {
          //we should not need the loop for non-naive version
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
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
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
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=exactEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 var e3=exactEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1) && (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
                                                         // cycle case i<e,i<e3, u->v->x->u
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

                        }// end of if du<=dv
                  }// end of forall. We get the number of triangles for each edge


                }// end of  on loc 
              } // end of coforall loc in Locales 


          }
          //writeln("after Triangle coutning");

          ConFlag=true;
          while (ConFlag) {

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
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   //if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                   if ((EdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                      if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read()<k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                             //EdgeDeleted[tmpe]=1-k;
                                                                          }
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
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
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
                                             if (EdgeDeleted[e2]==-1) {
                                                var tmpe=exactEdge(v4,v2);
                                                if (tmpe!=-1) {
                                                    if (EdgeDeleted[tmpe]==-1) {
                                                         TriCount[e2].sub(1);
                                                         if TriCount[e2].read() <k-2 {
                                                                 SetNextF.add((i,e2));
                                                         }
                                                         TriCount[tmpe].sub(1);
                                                         if TriCount[tmpe].read() <k-2 {
                                                                 SetNextF.add((i,tmpe));
                                                         }
                                                    }
                                                }
                                             }
                                          }
                                      } else {
                                         if (dv2>0) {

                                             nextStart=start_iR[v2];
                                             nextEnd=start_iR[v2]+neiR[v2]-1;
                                             forall j in nextStart..nextEnd with (ref SetNextF){
                                                 var v3=srcR[j];//v3==v2
                                                 var v4=dstR[j];
                                                 var e2=exactEdge(v4,v3);
                                                 if (EdgeDeleted[e2]==-1) {
                                                    var tmpe=exactEdge(v4,v1);
                                                    if (tmpe!=-1) {
                                                        if (EdgeDeleted[tmpe]==-1) {
                                                             TriCount[e2].sub(1);
                                                             if TriCount[e2].read() <k-2 {
                                                                     SetNextF.add((i,e2));
                                                             }
                                                             TriCount[tmpe].sub(1);
                                                             if TriCount[tmpe].read() <k-2 {
                                                                     SetNextF.add((i,tmpe));
                                                             } 
                                                        }
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
                              if (xlocal(i,startEdge,endEdge) && (EdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  SetCurF.clear();
                  coforall loc in Locales with (ref SetNextF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;

                         forall (i,j) in SetNextF  {
                            if (xlocal(j,startEdge,endEdge)) {//each local only check the owned edges
                                       EdgeDeleted[j]=1-k;
                                       SetCurF.add(j);
                            }
                         }// end of forall

                      }
                  }
                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 

              var tmpi=0;
              ConFlag=false;
              //writeln("k=",k);
              while tmpi<Ne {
                 if (EdgeDeleted[tmpi]==-1) {
                     ConFlag=true;
                     k+=1;
                     break;
                 }
                  tmpi+=1;
              }
              N2+=1;



          }// end while 


          timer.stop();




          outMsg="After KTruss Decomposition Mix , Max K ="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Decomposition Mix ,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Decomposition Mix ,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc TrussDecompositionMix

      proc TrussNaiveDecompositionDirected(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var TriCount=makeDistArray(Ne,atomic int);
          var EReverse=makeDistArray(Ne,set((int,int),parSafe = true) );
          var k=kvalue;
          forall i in TriCount {
              i.write(0);
          }
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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


          //here we begin the first naive version
          coforall loc in Locales {
              on loc {
                    var ld = src.localSubdomain();
                    var startEdge = ld.low;
                    var endEdge = ld.high;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if ( v1==v2) {
                              EdgeDeleted[i]=k-1;
                              //writeln("My locale=",here.id," Find self-loop ",i,"=<",src[i],",",dst[i],">");
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //writeln("My locale=",here.id, " Find duplicated edges ",i,"=<",src[i],",",dst[i],"> and ", DupE,"=<", src[DupE],",",dst[DupE],">");
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          timer.start();
          //writeln("After Preprocessing");

          //we will try to remove all the unnecessary edges in the graph
          {
              //ConFlag=false;
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
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if (EdgeDeleted[e3]==-1) {
                                                         TriCount[i].add(1);
                                                         TriCount[e].add(1);
                                                         TriCount[e3].add(1);
                                                         EReverse[e3].add((i,e));
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
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 //var e3=findEdge(x,v);
                                                 var e3=findEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1) && (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
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

                        }// end of if du<=dv
                  }// end of forall. We get the number of triangles for each edge


                }// end of  on loc 
              } // end of coforall loc in Locales 
          } // end of triangle counting


          while (ConFlag) {
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     forall i in startEdge..endEdge with(ref SetCurF){
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 


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


              if ( SetCurF.getSize()<=0){
                      //ConFlag=false;
                      k+=1;
              }
              SetCurF.clear();

              var tmpi=0;
              ConFlag=false;
              while tmpi<Ne {
                 if (EdgeDeleted[tmpi]==-1) {
                     ConFlag=true;
                     break;
                 } else {
                  tmpi+=1;
                 }
              }


              N2+=1;
          }// end while 


          timer.stop();
          AllRemoved=true;
          var tmpi=0;
          for i in 0..Ne-1  {
              if (EdgeDeleted[i]==-1) {
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }

          outMsg="After KTruss Naive Decomposition Directed , Max K ="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Decomposition Directed,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Decomposition Directed,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Decomposition Directed,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc TrussNaiveDecompositionDirected

      //For directed graph, using directed method.
      proc TrussDecompositionDirected(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int):string throws{
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF= new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N2=0:int;
          var k=kvalue;
          var ConFlag=true:bool;
          EdgeDeleted=-1;
          var RemovedEdge=0: int;
          var TriCount=makeDistArray(Ne,atomic int);
          var EReverse=makeDistArray(Ne,set((int,int),parSafe = true) );
          forall i in TriCount {
              i.write(0);
          }
          var timer:Timer;


          proc RemoveDuplicatedEdges( cur: int):int {
               if ( (cur<D3.low) || (cur >D3.high) || (cur==0) ) {
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
               } else {
                   if (u>v) {
                      if (nv<=0) {
                         DupE=-1;
                      } else {
                         DupE=binSearchE(dst,lv,lv+nv-1,u);
                      }
                      if (DupE!=-1) {
                           EdgeDeleted[cur]=k-1;
                      }
                   }
               }
               return DupE;
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


          //here we begin the first naive version
          coforall loc in Locales {
              on loc {
                    var ld = src.localSubdomain();
                    var startEdge = ld.low;
                    var endEdge = ld.high;
                    forall i in startEdge..endEdge {
                        var v1=src[i];
                        var v2=dst[i];
                        if ( v1==v2) {
                              EdgeDeleted[i]=k-1;
                        }
                        if (EdgeDeleted[i]==-1) {
                             var DupE= RemoveDuplicatedEdges(i);
                             if (DupE!=-1) {
                                  //writeln("My locale=",here.id, " Find duplicated edges ",i,"=<",src[i],",",dst[i],"> and ", DupE,"=<", src[DupE],",",dst[DupE],">");
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          //writeln("After Preprocessing");

          timer.start();
          //we will try to remove all the unnecessary edges in the graph
          while (ConFlag) {
              //ConFlag=false;
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
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",u," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if (EdgeDeleted[e3]==-1) {
                                                         TriCount[i].add(1);
                                                         TriCount[e].add(1);
                                                         TriCount[e3].add(1);
                                                         EReverse[e3].add((i,e));
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
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e==-1){
                                          //writeln("vertex ",x," and ",v," findEdge Error self-loop or no such edge");
                                       } else {
                                          if ((EdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 //var e3=findEdge(x,v);
                                                 var e3=findEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1) && (src[e3]==x) && (dst[e3]==u) && (i<e3)) {
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

                        }// end of if du<=dv
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
                                                       tmpe=findEdge(v2,v4);
                                                       if (tmpe!=-1) {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   //if ((EdgeDeleted[j]==-1) && (i<tmpe)) {
                                                                   if ((EdgeDeleted[j]==-1) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                      if ((EdgeDeleted[tmpe]==-1) &&(i<j)) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read()<k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                             //EdgeDeleted[tmpe]=1-k;
                                                                          }
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
                                                       if (tmpe!=-1)  {// there is such third edge
                                                         if ( EdgeDeleted[tmpe]<=-1 ) {
                                                               if ((EdgeDeleted[j]==-1) && (EdgeDeleted[tmpe]==-1)) {
                                                                      TriCount[tmpe].sub(1);
                                                                      if TriCount[tmpe].read() <k-2 {
                                                                         SetNextF.add((i,tmpe));
                                                                      }
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                               } else {
                                                                   if ((EdgeDeleted[j]==-1) && (i<tmpe) ) {
                                                                      TriCount[j].sub(1);
                                                                      if TriCount[j].read() <k-2 {
                                                                         SetNextF.add((i,j));
                                                                      }
                                                                   } else { 
                                                                       if ((EdgeDeleted[tmpe]==-1) && (i<j) ) {
                                                                          TriCount[tmpe].sub(1);
                                                                          if TriCount[tmpe].read() <k-2 {
                                                                             SetNextF.add((i,tmpe));
                                                                          }
                                                                       }   
                                                                   }   
                                                               }
                                                         }
                                                       }
                                             }
                                         }// end of  forall j in nextStart..nextEnd 
                                      }// end of if
                                      if EReverse[i].size>0 {
                                          forall (e1,e2) in EReverse[i] {
                                                if ((EdgeDeleted[e1]==-1) && (EdgeDeleted[e2]==-1)) {
                                                         TriCount[e1].sub(1);
                                                         if TriCount[e1].read() <k-2 {
                                                                 SetNextF.add((i,e1));
                                                         }
                                                         TriCount[e2].sub(1);
                                                         if TriCount[e2].read() <k-2 {
                                                                 SetNextF.add((i,e2));
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
                              if (xlocal(i,startEdge,endEdge) && (EdgeDeleted[i]==1-k)) {//each local only check the owned edges
                                  EdgeDeleted[i]=k-1;
                              }
                           }
                           
                      }
                  }
                  SetCurF.clear();
                  coforall loc in Locales with (ref SetNextF ) {
                      on loc {
                         var ld = src.localSubdomain();
                         var startEdge = ld.low;
                         var endEdge = ld.high;

                         var rset = new set((int,int), parSafe = true);
                         forall (i,j) in SetNextF with(ref rset)  {
                            if (xlocal(j,startEdge,endEdge)) {//each local only check the owned edges
                                       EdgeDeleted[j]=1-k;
                                       SetCurF.add(j);
                                       //      rset.add((i,j));// just want (i,j) is unique in rset
                            }
                         }// end of forall

                      }
                  }
                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 

              var tmpi=0;
              ConFlag=false;
              while tmpi<Ne {
                 if (EdgeDeleted[tmpi]==-1) {
                     ConFlag=true;
                     k+=1;
                     break;
                 }
                  tmpi+=1;
              }
              N2+=1;
          }// end while 


          timer.stop();


          outMsg="After KTruss Decomposition Directed , Max K ="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Decomposition Directed ,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Decomposition Directed ,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussDecompositionDirected







      var kLow=3:int;
      var kUp:int;
      var kMid:int;
      var maxtimer:Timer;

      if (!Directed) {//for undirected graph
      
          if (kValue>0) {// k-truss analysis
                var PTriCount=makeDistArray(Ne,int);
                PTriCount=0;
                repMsg=kTrussNaiveListIntersection(kValue,

                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,
                      PTriCount);

                PTriCount=0;
                repMsg=kTrussNaive(kValue,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, PTriCount);

                /*
                PTriCount=0;
                repMsg=kTrussListIntersection(kValue,ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                               ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,PTriCount);

                */

                var AtoTriCount=makeDistArray(Ne,atomic int);

                forall i in AtoTriCount {
                       i.write(0);
                }
                repMsg=kTruss(kValue,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, AtoTriCount);

                //var AtoTriCount=makeDistArray(Ne,atomic int);

                forall i in AtoTriCount {
                       i.write(0);
                }
                repMsg=kTrussMix(kValue,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, AtoTriCount);

                /*
                repMsg=kTrussNaiveDirected(kValue,ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a );
                repMsg=kTrussDirected(kValue,ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a );
                */

          } else if (kValue==-2) {
                //writeln("truss decomposition");
                /*
                var PTriCount=makeDistArray(Ne,int);
                PTriCount=0;
                repMsg=TrussDecompositionNaive(3,ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,PTriCount);
                PTriCount=0;
                repMsg=TrussDecompositionListIntersection(3,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, PTriCount);
                */
                var AtoTriCount=makeDistArray(Ne,atomic int);
                forall i in AtoTriCount {
                      i.write(0);
                }
                repMsg=TrussDecomposition(3,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, AtoTriCount);

                /*
                PTriCount=0;
                repMsg=TrussNaiveDecompositionDirected(3,ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a);

                */
                //var AtoTriCount=makeDistArray(Ne,atomic int);
                forall i in AtoTriCount {
                      i.write(0);
                }
                repMsg=TrussDecompositionMix(3,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, AtoTriCount);
          } else  {//k max branch

                //first the optimized method
                maxtimer.clear();
                var PTriCount=makeDistArray(Ne,atomic int);//keep the last no all removed results
                var PlTriCount=makeDistArray(Ne,atomic int);//for local use
                forall i in 0..Ne-1 {
                    PTriCount[i].write(0);
                    PlTriCount[i].write(0);
                }
                EdgeDeleted=-1;
                lEdgeDeleted=-1;//for local use
                maxtimer.start();
                kLow=3;
                // we first check  kLow=3
                repMsg=kTruss(kLow,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, PlTriCount);
                forall i in 0..Ne-1 {// first keep last time's results
                             lEdgeDeleted[i]=EdgeDeleted[i];
                             PTriCount[i].write(PlTriCount[i].read());
                }


                kUp=getupK(toSymEntry(ag.getNEIGHBOR(), int).a, toSymEntry(ag.getNEIGHBOR_R(), int).a);
                outMsg="Estimated kUp="+kUp:string;
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                if ((!AllRemoved) && (kUp>3)) {// we need to check if max k  >3
                    var ConLoop=true:bool;
                    while ( (ConLoop) && (kLow<kUp)) {
                         // we will continuely check if the up value can remove all edges
                         forall i in 0..Ne-1 {// first keep last time's results
                             lEdgeDeleted[i]=EdgeDeleted[i];
                             PlTriCount[i].write(PTriCount[i].read());
                         }
                         // we check the larget k vaule kUp which is the upper bound of max k
                         // we will use kMid to reduce kUp
                         AllRemoved=SkMaxTruss(kUp,
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
                            kMid= (kLow+kUp)/2;
                            forall i in 0..Ne-1 {
                                lEdgeDeleted[i]=EdgeDeleted[i];
                                PlTriCount[i].write(PTriCount[i].read());
                            }
                            //"Try mid=",kMid);
                            AllRemoved=SkMaxTruss(kMid,
                                 toSymEntry(ag.getNEIGHBOR(), int).a,
                                 toSymEntry(ag.getSTART_IDX(), int).a,
                                 toSymEntry(ag.getSRC(), int).a,
                                 toSymEntry(ag.getDST(), int).a,
                                 toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                 toSymEntry(ag.getSTART_IDX_R(), int).a,
                                 toSymEntry(ag.getSRC_R(), int).a,
                                 toSymEntry(ag.getDST_R(), int).a, PlTriCount,lEdgeDeleted);
                            if (AllRemoved) { // if mid value can remove all edges, we will reduce the up value for checking
                                  kUp=kMid-1;
                            } else { // we will improve both low and mid value
                                if kMid>=kUp-1 {
                                    ConLoop=false;
                                    kUp=kMid;
                                } else {// we will update the low value and then check the mid value 
                                        // until all edges are removed
                                     while ((AllRemoved==false) && (kMid<kUp-1)) {
                                        kLow=kMid;
                                        kMid= (kLow+kUp)/2;
                                        forall i in 0..Ne-1 { 
                                            EdgeDeleted[i]=lEdgeDeleted[i];
                                            PTriCount[i].write(PlTriCount[i].read());
                                        }
                                        //("Try mid again=",kMid);
                                        AllRemoved=SkMaxTruss(kMid,
                                             toSymEntry(ag.getNEIGHBOR(), int).a,
                                             toSymEntry(ag.getSTART_IDX(), int).a,
                                             toSymEntry(ag.getSRC(), int).a,
                                             toSymEntry(ag.getDST(), int).a,
                                             toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                             toSymEntry(ag.getSTART_IDX_R(), int).a,
                                             toSymEntry(ag.getSRC_R(), int).a,
                                             toSymEntry(ag.getDST_R(), int).a, PlTriCount,lEdgeDeleted);
                                     }
                                     if (!AllRemoved) {
                                         kUp=kMid;
                                         ConLoop=false;
                                     } else {
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
                    outMsg="After Max KTruss, Total execution time ="+(maxtimer.elapsed()):string;
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    outMsg="After Max KTruss, Max k="+kUp:string;
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();
                    outMsg="After Max KTruss,Total execution time ="+(maxtimer.elapsed()):string;
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {
                        outMsg="After Max KTruss, Max k=3";
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {
                        outMsg="After Max KTruss,Max k=2";
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }


                //second the Mix method.

                var AtoTriCount=makeDistArray(Ne,atomic int);
                var lAtoTriCount=makeDistArray(Ne,atomic int);
                forall i in AtoTriCount {
                     i.write(0);
                }
                forall i in lAtoTriCount {
                     i.write(0);
                }
                maxtimer.stop();
                maxtimer.clear();
                EdgeDeleted=-1;
                lEdgeDeleted=-1;
                maxtimer.start();
                kLow=3;
            
                // we first initialize the kmax from kLow=3
                repMsg=kTrussMix(kLow,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, lAtoTriCount);
                forall i in 0..Ne-1 {
                             lEdgeDeleted[i]=EdgeDeleted[i];
                             AtoTriCount[i].write(lAtoTriCount[i].read());
                }
                kUp=getupK(toSymEntry(ag.getNEIGHBOR(), int).a, toSymEntry(ag.getNEIGHBOR_R(), int).a);
                outMsg="Estimated kUp="+kUp:string;
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                if ((AllRemoved==false) && (kUp>3)) {// k max >3
                    var ConLoop=true:bool;
                    while ( (ConLoop) && (kLow<kUp)) {
                         // we will continuely check if the up value can remove the all edges
                         forall i in 0..Ne-1 {
                             lEdgeDeleted[i]=EdgeDeleted[i];
                             lAtoTriCount[i].write(AtoTriCount[i].read());
                         }
                         AllRemoved=SkMaxTrussMix(kUp,
                              toSymEntry(ag.getNEIGHBOR(), int).a,
                              toSymEntry(ag.getSTART_IDX(), int).a,
                              toSymEntry(ag.getSRC(), int).a,
                              toSymEntry(ag.getDST(), int).a,
                              toSymEntry(ag.getNEIGHBOR_R(), int).a,
                              toSymEntry(ag.getSTART_IDX_R(), int).a,
                              toSymEntry(ag.getSRC_R(), int).a,
                              toSymEntry(ag.getDST_R(), int).a, lAtoTriCount,lEdgeDeleted);
                         //writeln("Try up=",kUp);
                         if (AllRemoved==false) { //the up value is the max k
                                ConLoop=false;
                         } else {// we will check the mid value to reduce k max
                            kMid= (kLow+kUp)/2;
                            forall i in 0..Ne-1 {
                                lEdgeDeleted[i]=EdgeDeleted[i];
                                lAtoTriCount[i].write(AtoTriCount[i].read());
                            }
                            //writeln("Try mid=",kMid);
                            AllRemoved=SkMaxTrussMix(kMid,
                                  toSymEntry(ag.getNEIGHBOR(), int).a,
                                  toSymEntry(ag.getSTART_IDX(), int).a,
                                  toSymEntry(ag.getSRC(), int).a,
                                  toSymEntry(ag.getDST(), int).a,
                                  toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                  toSymEntry(ag.getSTART_IDX_R(), int).a,
                                  toSymEntry(ag.getSRC_R(), int).a,
                                  toSymEntry(ag.getDST_R(), int).a, lAtoTriCount,lEdgeDeleted);
                            if (AllRemoved==true) { // if mid value can remove all edges, we will reduce the up value for checking
                                  kUp=kMid-1;
                            } else { // we will improve both low and mid value
                                  if kMid==kUp-1 {
                                      ConLoop=false;
                                      kUp=kMid;
                                  } else {// we will update the low value and then check the mid value
                                     while ((AllRemoved==false) && (kMid<kUp-1)) {
                                            kLow=kMid;
                                            kMid= (kLow+kUp)/2;
                                            forall i in 0..Ne-1 { 
                                                EdgeDeleted[i]=lEdgeDeleted[i];
                                                AtoTriCount[i].write(lAtoTriCount[i].read());
                                            }
                                            //writeln("Try mid again=",kMid);
                                            AllRemoved=SkMaxTrussMix(kMid,
                                                toSymEntry(ag.getNEIGHBOR(), int).a,
                                                toSymEntry(ag.getSTART_IDX(), int).a,
                                                toSymEntry(ag.getSRC(), int).a,
                                                toSymEntry(ag.getDST(), int).a,
                                                toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                                toSymEntry(ag.getSTART_IDX_R(), int).a,
                                                toSymEntry(ag.getSRC_R(), int).a,
                                                toSymEntry(ag.getDST_R(), int).a, lAtoTriCount,lEdgeDeleted);
                                     }

                                     if (AllRemoved==false) {
                                         kUp=kMid;
                                         ConLoop=false;
                                     } else {
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
                    outMsg="After Max KTruss Mix ,Total execution time ="+(maxtimer.elapsed()):string;
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    outMsg="After Max KTruss Mix ,Max k="+kUp:string;
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();
                    outMsg="After Max KTruss Mix ,Total execution time ="+(maxtimer.elapsed()):string;
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {
                        outMsg="After Max KTruss Mix ,Max k=3";
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {
                        outMsg="After Max KTruss Mix ,Max k=2";
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }
          }//
      } else {// we have not tested directed graph extensively.


          if (kValue>0) {// k branch

    
                writeln("Enter kTruss k=",kValue);
                repMsg=kTrussDirected(kValue,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a);
          } else if (kValue==-2) {
                //writeln("Enter Truss Directed Naive Decomposition");
                //repMsg=TrussNaiveDecompositionDirected(3,ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a);

                //writeln("Enter Truss Directed Decomposition ");
                //repMsg=TrussDecompositionDirected(3,ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a);

          } else  {//k max branch


          }//








      }
          return new MsgTuple(repMsg, MsgType.NORMAL);
  }

    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedTruss", segTrussMsg);
    }


}


