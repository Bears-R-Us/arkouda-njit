module TrussMsg {
  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  use ServerErrorStrings;
  use ServerConfig;
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use IO;

  use SymArrayDmapCompat;
  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use Time;
  use CommAggregation;
  use Sort;
  use Map;
  use DistributedDeque;
  use Utils;

  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;


  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  var outMsg:string;
  


 proc segTrussMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
  //In this procedure, we implement different Truss analysis methods, including k-truss, max truss and truss decomposition
  
      var repMsg: string;
      //var (kTrussN,n_verticesN, n_edgesN, directedN, weightedN, graphEntryName, restpart )
      //    = payload.splitMsgToTuple(7);



      //var msgArgs = parseMessageArgs(payload, argSize);
      var kTrussN=msgArgs.getValueOf("KValue");
      var n_verticesN=msgArgs.getValueOf("NumOfVertices");
      var n_edgesN=msgArgs.getValueOf("NumOfEdges");
      var directedN=msgArgs.getValueOf("Directed");
      var weightedN=msgArgs.getValueOf("Weighted");
      var graphEntryName=msgArgs.getValueOf("GraphName");




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
      var BigKRange:int=100;
      var BigKDividedBy:int=10;
      var SmallKRange:int=32;
      var SmallKDividedBy:int=5;
      var ToK:int=100000;

      gEdgeDeleted=-1;
      lEdgeDeleted=-1;
      var kLow=3:int;
      var kUp:int;
      var kMid:int;
      var maxtimer:stopwatch;


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
          var timer:stopwatch;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,atomic int);
          forall i in MinNumTri {
                  i.write(100000000);
          }


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

          RemovedEdge.write(0);
          forall i in EdgeDeleted {
               if (i!=-1) {
                    RemovedEdge.add(1);
               }
          }


          
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
                                       if (TriCount[i].read() <MinNumTri[here.id].read()) {
                                            MinNumTri[here.id].write(TriCount[i].read());
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
                                      if (TriCount[i].read() < MinNumTri[here.id].read()) {
                                           MinNumTri[here.id].write(TriCount[i].read());
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

      proc BatchMaxTrussMinSearch(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):int{ 


          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag((int,int),Locales); //use bag to keep the next frontier
          var N1=0:int;
          var N2=0:int;
          var ConFlag=true:bool;
          var RemovedEdge: atomic int;
          var k=kvalue:int;
          var timer:stopwatch;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,atomic int);
          forall i in MinNumTri {
                  i.write(100000000);
          }


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

          forall i in EdgeDeleted {
               if (i!=-1) {
                    RemovedEdge.add(1);
               }
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
                                      if (TriCount[i].read() < MinNumTri[here.id].read()) {
                                           MinNumTri[here.id].write(TriCount[i].read());
                                      }
                                  }
                               }
                         }
                      }// end of  on loc
                  } // end of coforall loc in Locales

                  tmpN2+=1;
                  SetNextF.clear();
              }// end of while 




              if (RemovedEdge.read()>=Ne) {
                       ConFlag=false;
                       AllRemoved=true;
                      
              } else {
                    AllRemoved=false;
                    if k<ToK {
                          k=k+1;
                          ConFlag=true;
                    } else {
                        ConFlag=false;
                    }
              }
              //writeln("k=",k ," Removed Edge=",RemovedEdge.read()," Ne=",Ne, " AllRemoved=",AllRemoved);

          }// end while 

          return k;

      }// end of proc BatchMaxTrussMinSearch

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


                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a, aPlTriCount,lEdgeDeleted);
                forall i in 0..Ne-1 {// first keep last time's results
                             gEdgeDeleted[i]=lEdgeDeleted[i];
                             aPTriCount[i].write(aPlTriCount[i].read());
                             //EdgeDeleted and aPTricount will keep the latest value with no empty subgraph
                }
                kUp=getupK(toSymEntry(ag.getComp("NEIGHBOR"), int).a, toSymEntry(ag.getComp("NEIGHBOR_R"), int).a)+1;
                outMsg="Estimated kUp="+(kUp-1):string;
                smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                if ((!AllRemoved) && (kUp>3)) {// we need to check if max k  >3
                    var ConLoop=true:bool;
                    var FirstEntry:bool=true;



                    while ( ConLoop)  {
                            ToK=kUp-1;
                            // we only check k to ToK
                            //writeln("After ConLoop ToK=",ToK);
                            if ((kUp-kLow<SmallKRange) ||FirstEntry) {
                                if (FirstEntry) {
                                    ToK=min(kLow+SmallKRange,kUp-1);
                                }
                                // for small kUp, we directly get the answer

                                 var tmpkUp=BatchMaxTrussMinSearch(kLow+1,

                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a, aPlTriCount,lEdgeDeleted);
                                 //writeln("After kUp-kLow<SmallKRange tmp kUp=",tmpkUp, " kLow=",kLow," kUp=",kUp, " kMid=",kMid);
                                 if AllRemoved {
                                     kUp=tmpkUp-1;
                                     ConLoop=false;
                                 } else {
                                     kLow=tmpkUp;
                                 }
                                 FirstEntry=false;
                                 continue;
                            }
                            if kUp-kLow>BigKRange {
                                kMid=kLow+(kUp-kLow)/BigKDividedBy;
                            } else {
                                if kUp-kLow>SmallKRange {
                                    kMid=kLow+(kUp-kLow)/SmallKDividedBy;
                                } else {
                                
                                    kMid=(kUp+kLow)/2;
                                }
                            }
                            while ((kMid>kLow) && ConLoop) {
                                ToK=min(kMid+SmallKDividedBy,kUp-1);

                                var tmpK =BatchMaxTrussMinSearch(kMid,

                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a, aPlTriCount,lEdgeDeleted);
                                //writeln("1 After kMid>kLow  tmpK=",tmpK," kMid=",kMid,  " kLow=",kLow," kUp=",kUp);
                                if (AllRemoved) {
                                    if tmpK>kMid {
                                          kMid=tmpK-1;
                                          kUp=kMid;
                                          ConLoop=false;
                                          continue;
                                    }
                                    kUp=kMid;
                                    if (kUp-kLow)>BigKRange {
                                        kMid=kLow+(kUp-kLow)/BigKDividedBy;
                                    } else {
                                        if (kUp-kLow)>SmallKRange {
                                            kMid=kLow+(kUp-kLow)/SmallKDividedBy;
                                        } else {
                                            kMid=(kUp+kLow)/2;
                                        }
                                    }

                                    forall i in 0..Ne-1 {
                                        lEdgeDeleted[i]=gEdgeDeleted[i];
                                        aPlTriCount[i].write(aPTriCount[i].read());
                                    }
                                } else {
                                    kLow=tmpK;
                                    kMid=tmpK;
                                    forall i in 0..Ne-1 {
                                        gEdgeDeleted[i]=lEdgeDeleted[i];
                                        aPTriCount[i].write(aPlTriCount[i].read());
                                    }
                                }
                                //writeln("2 After kMid>kLow  tmpK=",tmpK," kMid=",kMid,  " kLow=",kLow," kUp=",kUp);

                            }

                            if kMid>=kUp-1 {
                                    ConLoop=false;
                                    //writeln("After kMid>kUp kMid=",kMid,  " kLow=",kLow," kUp=",kUp);
                                    kUp=kMid;
                            } 
                    }// end of while
                    var countName = st.nextName();
                    var maxKAry = makeDistArray(2, int);
                    maxKAry[0]=kUp;
                    var countEntry = new shared SymEntry(maxKAry);
                    st.addEntry(countName, countEntry);
                    repMsg =  'created ' + st.attrib(countName);
                    maxtimer.stop();

                    outMsg="After BatchMaxTrussMinSearch, Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                    outMsg="After BatchMaxTrussMinSearch, Max K="+kUp:string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();

                    outMsg="After BatchMaxTrussMinSearch,Total execution time ="+(maxtimer.elapsed()):string;

                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {

                        outMsg="After BatchMaxTrussMinSearch, Max K=3";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {

                        outMsg="After BatchMaxTrussMinSearch,Max K=2";

                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }


          return repMsg;

      }// end of proc MaxTrussMinSearch

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
          var timer:stopwatch;
          var largest:int;
          largest=Ne;
          RemovedEdge.write(0);
          var MinNumTri=makeDistArray(numLocales,atomic int);
          forall i in MinNumTri {
                  i.write(100000000);
          }


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

          RemovedEdge.write(0);
          forall i in EdgeDeleted {
               if (i!=-1) {
                    RemovedEdge.add(1);
               }
          }


          
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
                                       if (TriCount[i].read() <MinNumTri[here.id].read()) {
                                            MinNumTri[here.id].write(TriCount[i].read());
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
                                      if (TriCount[i].read() < MinNumTri[here.id].read()) {
                                           MinNumTri[here.id].write(TriCount[i].read());
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
                          var tmp=MinNumTri[0].read();
                          var oldk=k;
                          for i in 1..numLocales-1 {
                               if tmp>MinNumTri[i].read() {
                                   tmp=MinNumTri[i].read();
                               }
                          }
                          k=max(tmp+2,k+1);
                          forall i in MinNumTri {
                             i.write(1000000);
                          }
                          largest=RemovedEdge.read();
                          AllRemoved=false;
                          //writeln("Improve k from ",oldk, " to ",k);
                  } else {
                      AllRemoved=true;
                  }
                  //writeln("k=", k, " Removed Edge=",RemovedEdge.read()," Ne=",Ne, " AllRemoved=",AllRemoved);
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


                PTriCount=0;
                gEdgeDeleted=-1;


                var AtoTriCount=makeDistArray(Ne,atomic int);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=kTrussMinSearch(kValue,


                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a,


                      AtoTriCount,gEdgeDeleted);
          }// end of k-truss analysis

          if (kValue==-1) {// max k-truss analysis
                var PTriCount=makeDistArray(Ne,int);


                PTriCount=0;
                gEdgeDeleted=-1;


                var AtoTriCount=makeDistArray(Ne,atomic int);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;

                repMsg=MaxTrussMinSearch(kValue,


                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a,


                      AtoTriCount,gEdgeDeleted);
          }// end of max k-truss analysis


          if (kValue==-2) {
                var PTriCount=makeDistArray(Ne,int);


                PTriCount=0;
                gEdgeDeleted=-1;

                kValue=3;

                PTriCount=0;
                gEdgeDeleted=-1;

                kValue=3;

                var AtoTriCount=makeDistArray(Ne,atomic int);


                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;


                kValue=3;
                repMsg=TrussDecoMinSearch(kValue,


                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a,


                      AtoTriCount,gEdgeDeleted);
          }// end of truss decomposition analysis

      } //end of  undirected graph
      
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    use CommandMap;
    registerFunction("segmentedTruss", segTrussMsg);
}
