# We define all k-truss functions as follows
kTrussFuns=[ "kTrussNaiveListIntersection", "kTrussNaiveSetSearchSmall",\
"kTrussNaiveSetSearchSmallSeq", "kTrussNaivePathMerge",\
"kTrussNaiveMinSearch", "kTrussPathMerge",\
"kTrussMinSearch", "kTrussMix"]

# We define all max k-truss functions as follows
MaxTrussFuns=[ "MaxTrussNaiveListIntersection", "MaxTrussNaiveSetSearchSmall",\
"MaxTrussNaiveSetSearchSmallSeq", "MaxTrussNaivePathMerge",\
"MaxTrussNaiveMinSearch", "MaxTrussPathMerge",\
"MaxTrussMinSearch", "MaxTrussMix"]

# We define all truss decomposition functions as follows
TrussDecoFuns=[ "TrussDecoNaiveListIntersection", "TrussDecoNaiveSetSearchSmall",\
"DecoTrussNaiveSetSearchSmallSeq", "TrussDecoNaivePathMerge",\
"TrussDecoNaiveMinSearch", "TrussDecoPathMerge",\
"TrussDecoMinSearch", "TrussDecoMix"]

#We define three kinds of Parameters for our truss functions

Parameters='''(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):string throws{'''

ParametersAtomic='''(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):string throws{'''


ParametersBool='''(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] int, EdgeDeleted:[?D6] int ):bool{ '''

ParametersBoolAtomic='''(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        TriCount:[?D5] atomic int, EdgeDeleted:[?D6] int ):bool{ '''

ConditionEdgeRemove='''
                               if (EdgeDeleted[i]==-1) {
                                  if (TriCount[i] < k-2) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                                  } else {
                                       if (TriCount[i] <MinNumTri[here.id].read()) {
                                            MinNumTri[here.id].write(TriCount[i]);
                                       }
                                  }
                               }
'''

ConditionEdgeRemoveAtomic='''
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
'''


#We define different triangle counting methods
TriCntInit            ="                         TriCount[i]=0;"
TriCntInitAtomic      ="                         TriCount[i].write(0);"

TriCntAssignment      ="                               TriCount[i]=Count;"
TriCntAssignmentAtomic="                               TriCount[i].write(Count);"
emptyline='''

'''
InitialCount='''
                PTriCount=0;
                gEdgeDeleted=-1;
'''
InitialCountAtomic='''
                forall i in AtoTriCount {
                       i.write(0);
                }
                gEdgeDeleted=-1;
'''
#We defind the global variables for all truss functions. 10 spaces
FunStartVariables='''

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
          var MinNumTri=makeDistArray(numLocales,atomic int);
          forall i in MinNumTri {
                  i.write(100000000);
          }

'''
#We define the common local functions for every truss function
FunStartFuncs='''
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
'''

#We defind the preprocessing part that aids to remove duplicated/cycle edges 
#   and edges that cannot support k-2 triangles 
FunStartPreProcessing='''
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
'''


#We defind the starting code of any truss function
kTrussFunStart=FunStartVariables+FunStartFuncs+FunStartPreProcessing
MaxTrussFunStart=FunStartVariables+FunStartFuncs
TrussDecoFunStart=kTrussFunStart
######Function start definetion finished



#We defind the timer before the truss analysis
TimerAndWhileStart='''
          timer.start();
          ConFlag=true;
          while (ConFlag) {
'''

def GenListIntersectionTriCnt(InitAssign,AssignCnt):
#AssignCnt is TriCount[i] = Count; or
#TriCount[i].write(Count);
	text1a='''
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
'''
	text1b='''
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
'''
#                               TriCount[i] = Count;
	text2='''
                               // here we get the number of triangles of edge ID i
                            }// end of if 
                        }//end of if
                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 
'''
	ret=text1a+InitAssign+text1b+AssignCnt+emptyline+text2
	return ret
#We remove the edges based on their supports



MarkDelEdges='''
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
                                       if TriCount[i]<MinNumTri[here.id].read() {
                                           MinNumTri[here.id].write(TriCount[i]);
                                       }
                                   }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());

'''

MarkDelEdgesAtomic='''
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
                               if (EdgeDeleted[i]==-1) {
                                    if  (TriCount[i].read() < k-2) {
                                        EdgeDeleted[i] = k-1;
                                        SetCurF.add(i);
                                    } else {
                                        if (TriCount[i].read()<MinNumTri[here.id].read()) {
                                            MinNumTri[here.id].write(TriCount[i].read());
                                        }
                                    }
                               }
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 
              RemovedEdge.add(SetCurF.getSize());

'''
ListIntersectionTriCount=GenListIntersectionTriCnt(TriCntInit,TriCntAssignment)
ListIntersectionTriCountAtomic=GenListIntersectionTriCnt(TriCntInitAtomic,TriCntAssignmentAtomic)

NaiveListIntersectionBodyCode=TimerAndWhileStart+ListIntersectionTriCount+MarkDelEdges
NaiveListIntersectionBodyCodeAtomic=TimerAndWhileStart+ListIntersectionTriCountAtomic+MarkDelEdgesAtomic



def GenSetSearchSmallTriCnt(InitAssign,AssignCnt):
	text1a='''
              // first we calculate the number of triangles
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;

                     forall i in startEdge..endEdge with(ref SetCurF){
'''
	text1b='''
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
'''

	text2='''
                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 


                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 
'''
	ret=text1a+InitAssign+text1b+AssignCnt+emptyline+text2
	return ret

SetSearchSmallTriCount=GenSetSearchSmallTriCnt(TriCntInit,TriCntAssignment)
SetSearchSmallTriCountAtomic=GenSetSearchSmallTriCnt(TriCntInitAtomic,TriCntAssignmentAtomic)


NaiveSetSearchSmallBodyCode= TimerAndWhileStart+SetSearchSmallTriCount+MarkDelEdges
NaiveSetSearchSmallBodyCodeAtomic= TimerAndWhileStart+SetSearchSmallTriCountAtomic+MarkDelEdgesAtomic


def GenSetSearchSmallSeqTriCnt(InitAssign,AssignCnt):
	text1a='''
              // first we calculate the number of triangles
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;

                     forall i in startEdge..endEdge with(ref SetCurF){
'''
	text1b='''
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
'''
	text2='''

                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 





                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 
'''
	ret=text1a+InitAssign+text1b+AssignCnt+emptyline+text2
	return ret

SetSearchSmallSeqTriCount=GenSetSearchSmallSeqTriCnt(TriCntInit,TriCntAssignment)
SetSearchSmallSeqTriCountAtomic=GenSetSearchSmallSeqTriCnt(TriCntInitAtomic,TriCntAssignmentAtomic)

NaiveSetSearchSmallSeqBodyCode=TimerAndWhileStart+SetSearchSmallSeqTriCount+MarkDelEdges
NaiveSetSearchSmallSeqBodyCodeAtomic=TimerAndWhileStart+SetSearchSmallSeqTriCountAtomic+MarkDelEdgesAtomic

def GenPathMergeTriCount(InitAssign,AssignCnt):
	text1a='''
              // first we calculate the number of triangles
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge {
'''
	text1b='''
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
'''

	text2='''
                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 
'''

	ret=text1a+InitAssign+text1b+AssignCnt+emptyline+text2
	return ret



PathMergeTriCount=GenPathMergeTriCount(TriCntInit,TriCntAssignment)
PathMergeTriCountAtomic=GenPathMergeTriCount(TriCntInitAtomic,TriCntAssignmentAtomic)


NaivePathMergeBodyCode=TimerAndWhileStart+PathMergeTriCount+MarkDelEdges
NaivePathMergeBodyCodeAtomic=TimerAndWhileStart+PathMergeTriCountAtomic+MarkDelEdgesAtomic


def GenMinSearchTriCnt(InitAssign,AssignCnt,SeqFlag:bool=False):
	text1a='''
              // first we calculate the number of triangles using mininum search  method.
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
'''
	text1b='''
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
'''
	if SeqFlag:
		tmpcode1='''
                                         for j in nextStart..nextEnd {
'''
	else:
		tmpcode1='''

                                         forall j in nextStart..nextEnd with (+ reduce Count){
'''
	text1bf1='''
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
'''
	if SeqFlag:
		tmpcode2='''
                                         for j in nextStart..nextEnd {
'''
	else:
		tmpcode2='''
                                         forall j in nextStart..nextEnd with (+ reduce Count ){
'''
	text1bf2='''
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
'''
	emptyline='''

'''   
	assign="                        "+AssignCnt
#                        TriCount[i]=Count;

	text2='''
                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 
'''
	ret=text1a+InitAssign+text1b+tmpcode1+text1bf1+tmpcode2+text1bf2+AssignCnt+emptyline+text2
	return ret





def GenNonMinSearchTriCnt(InitAssign,AssignCnt):
	text1a='''
              // first we calculate the number of triangles using mininum search  method.
              coforall loc in Locales with (ref SetCurF ) {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with(ref SetCurF){
'''
	text1b='''
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
'''
	emptyline='''

'''   
	assign="                        "+AssignCnt
#                        TriCount[i]=Count;

	text2='''
                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 
              } // end of coforall loc in Locales 
'''
	ret=text1a+InitAssign+text1b+AssignCnt+emptyline+text2
	return ret


MinSearchTriCount=GenMinSearchTriCnt(TriCntInit,TriCntAssignment)
MinSearchTriCountAtomic=GenMinSearchTriCnt(TriCntInitAtomic,TriCntAssignmentAtomic)
SeqMinSearchTriCountAtomic=GenMinSearchTriCnt(TriCntInitAtomic,TriCntAssignmentAtomic,True)

NonMinSearchTriCount=GenNonMinSearchTriCnt(TriCntInit,TriCntAssignment)
NonMinSearchTriCountAtomic=GenNonMinSearchTriCnt(TriCntInitAtomic,TriCntAssignmentAtomic)

NaiveMinSearchBodyCode=TimerAndWhileStart+MinSearchTriCount+MarkDelEdges
NaiveMinSearchBodyCodeAtomic=TimerAndWhileStart+MinSearchTriCountAtomic+MarkDelEdgesAtomic
NaiveNonMinSearchBodyCode=TimerAndWhileStart+NonMinSearchTriCount+MarkDelEdges
NaiveNonMinSearchBodyCodeAtomic=TimerAndWhileStart+NonMinSearchTriCountAtomic+MarkDelEdgesAtomic


#We define new start that need to calculate the total number of triangles first
TimerAndNoWhileStart='''
          timer.start();
          //while (ConFlag) {
          {
'''
          


def GenWhileAndAffectEdgeRemoveStart(Condition):
	text1='''
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
'''
	comm='''
                               if ((EdgeDeleted[i]==-1) && (TriCount[i] < k-2)) {
                                     EdgeDeleted[i] = 1-k;
                                     SetCurF.add(i);
                               }
'''
	text2='''
                     }
                  }// end of  on loc 
              } // end of coforall loc in Locales 




              ConFlag=false;


              // we try to remove as many edges as possible in the following code
              var tmpN2=0:int;
'''
	ret=text1+Condition+text2
	return ret


WhileAndAffectEdgeRemoveStart=GenWhileAndAffectEdgeRemoveStart(ConditionEdgeRemove)
WhileAndAffectEdgeRemoveStartAtomic=GenWhileAndAffectEdgeRemoveStart(ConditionEdgeRemoveAtomic)

MinSearchAffectedEdgeRemoval='''
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

'''




SeqMinSearchAffectedEdgeRemoval='''
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
                                         for j in nextStart..nextEnd {
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
                                         for j in nextStart..nextEnd {
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

'''



NonMinSearchAffectedEdgeRemoval='''
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

'''



PathMergeAffectedEdgeRemoval='''
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

'''


PathMergeBodyCode=TimerAndNoWhileStart+PathMergeTriCountAtomic+WhileAndAffectEdgeRemoveStartAtomic+PathMergeAffectedEdgeRemoval


MixMinSearchTriCountAtomic='''
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


'''




MixMinSearchAffectedEdgeRemoval='''

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
                                      if (TriCount[i].read() < MinNumTri[here.id].read()) {
                                           MinNumTri[here.id].write(TriCount[i].read());
                                      }
                                  }
                               }
                         }
                      }// end of  on loc 
                  } // end of coforall loc in Locales 

                  SetNextF.clear();
                  tmpN2+=1;
              }// end of while 

'''

TrussAtomicBodyCode=TimerAndNoWhileStart+MinSearchTriCountAtomic+WhileAndAffectEdgeRemoveStartAtomic+MinSearchAffectedEdgeRemoval
SeqTrussAtomicBodyCode=TimerAndNoWhileStart+SeqMinSearchTriCountAtomic+WhileAndAffectEdgeRemoveStartAtomic+SeqMinSearchAffectedEdgeRemoval

NonMSTrussAtomicBodyCode=TimerAndNoWhileStart+NonMinSearchTriCountAtomic+WhileAndAffectEdgeRemoveStartAtomic+NonMinSearchAffectedEdgeRemoval

TrussMixAtomicBodyCode=TimerAndNoWhileStart+MixMinSearchTriCountAtomic+WhileAndAffectEdgeRemoveStartAtomic+MixMinSearchAffectedEdgeRemoval




MaxTrussStart='''
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
'''


MaxNaivePathMergeBodyCode=NaivePathMergeBodyCode
MaxPathMergeBodyCode=MaxTrussStart+PathMergeAffectedEdgeRemoval



MaxMinSearchBodyCode=MaxTrussStart+MinSearchAffectedEdgeRemoval
MaxSeqMinSearchBodyCode=MaxTrussStart+SeqMinSearchAffectedEdgeRemoval
MaxNonMinSearchBodyCode=MaxTrussStart+NonMinSearchAffectedEdgeRemoval
MaxTrussMixBodyCode= MaxTrussStart+MixMinSearchAffectedEdgeRemoval


#We define three different kinds of function loop ending methods
TrussEndCheck='''


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


'''



MaxTrussEndCheck='''


              
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



'''


DecompositionEndCheck='''


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
                  } 
              }
              
              N2+=1;
          }// end while 

          timer.stop();

'''
def GenTrussOutput(name):

          print('          outMsg="After '+name+', Given K ="+k:string;')
          print("          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);")
          print('          outMsg="After '+name+', Total execution time="+(timer.elapsed()):string;')
          print("          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);")
          print('          outMsg="After '+name+', Total number of iterations ="+N2:string;')
          print("          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);")
          print('          outMsg="After '+name+', The k truss has edges ="+(Ne-RemovedEdge.read()):string;')
          print("          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);")

def GenDecompositionOutput(name):
       
          print('          outMsg="After '+name+', Max K="+(k-1):string;')
          print("          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);")
          print('          outMsg="After '+name+', Total execution time="+(timer.elapsed()):string;')
          print("          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);")
          print('          outMsg="After '+name+', Total number of iterations ="+N2:string;')
          print("          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);")
          print('          outMsg="After '+name+', The largest number of k truss edges ="+(Ne-largest):string;')
          print("          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);")

def GenReturn(FunName):
	text='''
          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
'''
	lastone="      }// end of proc "+FunName


	print(text)
	print(lastone)
	print("")
	print("")
	print("")

def GenMaxReturn(FunName):
	text='''
          return AllRemoved;
'''
	lastone="      }// end of proc "+FunName


	print(text)
	print(lastone)
	print("")
	print("")
	print("")

def GenMaxTestReturn(FunName):
	text='''
          return repMsg;
'''
	lastone="      }// end of proc "+FunName


	print(text)
	print(lastone)
	print("")
	print("")
	print("")

#We define how to generate different truss functions
def GenTrussFun(FunName,Parameters,BodyCode):
	head="      proc "+FunName+Parameters
	print(head)
	print(kTrussFunStart)
	print(BodyCode)

	print(TrussEndCheck)
	GenTrussOutput(FunName)
	GenReturn(FunName)



def GenMaxTrussFun(FunName1,CallFunName,BodyCode):
#We first generate fun1, for once max call
	OnceFunName="Once"+CallFunName
	head="      proc "+OnceFunName+ParametersBool
	print(head)
	print(MaxTrussFunStart)
	print(BodyCode)
	txt='''
              if ( SetCurF.getSize()<=0){
                      ConFlag=false;
              } else {
                      ConFlag=true;
              }
              SetCurF.clear();
'''
	print(txt)
	print(MaxTrussEndCheck)
	GenMaxReturn(OnceFunName)

#We then generate fun2, for achieving the max k truss value
	Fun2Head="      proc "+CallFunName+Parameters
	print(Fun2Head)


	variabledel='''
                var PlTriCount =makeDistArray(Ne,int);
                ref gEdgeDeleted=EdgeDeleted;
                ref PTriCount=TriCount;
                var lEdgeDeleted =makeDistArray(Ne,int);
'''
	print(variabledel)

	text1='''
                PTriCount=0;
                PlTriCount=0;
                gEdgeDeleted=-1;
                lEdgeDeleted=-1;//for local use
                maxtimer.clear();
                maxtimer.start();
                kLow=3;
                // we first check  kLow=3
'''
	text2="                repMsg="+FunName1+"(kLow,"
	text3='''

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
'''
	text4="                         AllRemoved="+OnceFunName+"(kUp,"
	text5='''
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
'''
	text6="                                AllRemoved="+OnceFunName+"(kMid,"
	text7='''
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
'''
	text8="                                        AllRemoved="+OnceFunName+"(kMid,"
	text9='''
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
'''
	text10='                    outMsg="After '+OnceFunName+', Total execution time ="+(maxtimer.elapsed()):string;'
	text11='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
'''
	text12='                    outMsg="After '+OnceFunName+', Max K="+kUp:string;'
	text13='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();
'''
	text14='                    outMsg="After '+OnceFunName+',Total execution time ="+(maxtimer.elapsed()):string;'
	text15='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {
'''
	text16='                        outMsg="After '+OnceFunName+', Max K=3";'
	text17='''
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {
'''
	text18='                        outMsg="After '+OnceFunName+',Max K=2";'
	text19='''
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }
'''
	print(text1)
	print(text2)
	print(text3)


	print(text4)
	print(text5)
	print(text6)
	print(text7)
	print(text8)
	print(text9)
	print(text10)
	print(text11)
	print(text12)
	print(text13)
	print(text14)
	print(text15)
	print(text16)
	print(text17)
	print(text18)
	print(text19)
	GenMaxTestReturn(CallFunName)

def GenMaxTrussFunNoFinish(IsAtomic:bool,FunName1:str,CallFunName:str,BodyCode:str):
#have not finished
#We first generate fun1, for once max call
	OnceFunName="Once"+CallFunName
	if IsAtomic:
		head="      proc "+OnceFunName+ParametersBoolAtomic
	else:
		head="      proc "+OnceFunName+ParametersBool
#	head="      proc "+OnceFunName+ParametersBoolAtomic
	print(head)
	print(MaxTrussFunStart)
	print(BodyCode)
	print(MaxTrussEndCheck)
	GenMaxReturn(OnceFunName)

#We then generate fun2, for achieving the max k truss value
	if IsAtomic:
		Fun2Head="      proc "+CallFunName+ParametersAtomic
	else:
		Fun2Head="      proc "+CallFunName+Parameters
	print(Fun2Head)

	if IsAtomic:

		variabledel0='''
                var aPlTriCount =makeDistArray(Ne,atomic int);
'''
	else:
                variabledel0='''
                var aPlTriCount =makeDistArray(Ne, int);
'''


	variabledel='''
                ref aPTriCount=TriCount;
                ref gEdgeDeleted=EdgeDeleted;
                var lEdgeDeleted =makeDistArray(Ne,int);
'''

	print(variabledel0)
	print(variabledel)

	if IsAtomic:
		text01='''
                forall i in 0..Ne-1 {
                    aPTriCount[i].write(0);
                    aPlTriCount[i].write(0);
                }
'''
	else:
		text01='''
                aPTriCount=0;
                aPlTriCount=0;
'''
	print(text01)

	text1='''
                gEdgeDeleted=-1;
                lEdgeDeleted=-1;//for local use
                maxtimer.clear();
                maxtimer.start();
                kLow=3;
                // we first check  kLow=3
'''
	text2="                repMsg="+FunName1+"(kLow,"
	print(text1)
	print(text2)
	text3='''

                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
'''
	if IsAtomic:
		text30='''
                      toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
'''
	else:
		text30='''
                      toSymEntry(ag.getDST_R(), int).a, PlTriCount,lEdgeDeleted);
'''
	print(text3)
	print(text30)

	text31='''

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
'''
	text4="                         AllRemoved="+OnceFunName+"(kUp,"
	text5='''
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
'''
	text6="                                AllRemoved="+OnceFunName+"(kMid,"
	text7='''
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
                                        //forall i in 0..Ne-1 { 
                                        //    gEdgeDeleted[i]=lEdgeDeleted[i];
                                        //    aPTriCount[i].write(aPlTriCount[i].read());
                                            //store the latest no empty subgraph setup 
                                        //}
'''
	text8="                                        AllRemoved="+OnceFunName+"(kMid,"
	text9='''
                                             toSymEntry(ag.getNEIGHBOR(), int).a,
                                             toSymEntry(ag.getSTART_IDX(), int).a,
                                             toSymEntry(ag.getSRC(), int).a,
                                             toSymEntry(ag.getDST(), int).a,
                                             toSymEntry(ag.getNEIGHBOR_R(), int).a,
                                             toSymEntry(ag.getSTART_IDX_R(), int).a,
                                             toSymEntry(ag.getSRC_R(), int).a,
                                             toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
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
                    var maxKAry:[0..1] int;
                    maxKAry[0]=kUp;
                    var countEntry = new shared SymEntry(maxKAry);
                    st.addEntry(countName, countEntry);
                    repMsg =  'created ' + st.attrib(countName);
                    maxtimer.stop();
'''
	text10='                    outMsg="After '+OnceFunName+', Total execution time ="+(maxtimer.elapsed()):string;'
	text11='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
'''
	text12='                    outMsg="After '+OnceFunName+', Max K="+kUp:string;'
	text13='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();
'''
	text14='                    outMsg="After '+OnceFunName+',Total execution time ="+(maxtimer.elapsed()):string;'
	text15='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {
'''
	text16='                        outMsg="After '+OnceFunName+', Max K=3";'
	text17='''
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {
'''
	text18='                        outMsg="After '+OnceFunName+',Max K=2";'
	text19='''
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }
'''
	print(text1)
	print(text2)
	print(text3)
	print(text4)
	print(text5)
	print(text6)
	print(text7)
	print(text8)
	print(text9)
	print(text10)
	print(text11)
	print(text12)
	print(text13)
	print(text14)
	print(text15)
	print(text16)
	print(text17)
	print(text18)
	print(text19)


def GenMaxTrussAtomicFun(FunName1,CallFunName,BodyCode):
#We first generate fun1, for once max call
	OnceFunName="Once"+CallFunName
	head="      proc "+OnceFunName+ParametersBoolAtomic
	print(head)
	print(MaxTrussFunStart)
	print(BodyCode)
	print(MaxTrussEndCheck)
	GenMaxReturn(OnceFunName)

#We then generate fun2, for achieving the max k truss value
	Fun2Head="      proc "+CallFunName+ParametersAtomic
	print(Fun2Head)


	variabledel='''
                ref aPTriCount=TriCount;
                var aPlTriCount =makeDistArray(Ne,atomic int);
                ref gEdgeDeleted=EdgeDeleted;
                var lEdgeDeleted =makeDistArray(Ne,int);
'''
	print(variabledel)

	text1='''
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
'''
	text2="                repMsg="+FunName1+"(kLow,"
	text3='''

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
'''
	text4="                         AllRemoved="+OnceFunName+"(kUp,"
	text5='''
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
'''
	text6="                                AllRemoved="+OnceFunName+"(kMid,"
	text7='''
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
'''
	text8="                                        AllRemoved="+OnceFunName+"(kMid,"
	text9='''
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
'''
	text10='                    outMsg="After '+OnceFunName+', Total execution time ="+(maxtimer.elapsed()):string;'
	text11='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
'''
	text12='                    outMsg="After '+OnceFunName+', Max K="+kUp:string;'
	text13='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                } else {//kUp<=3 or AllRemoved==true
                    maxtimer.stop();
'''
	text14='                    outMsg="After '+OnceFunName+',Total execution time ="+(maxtimer.elapsed()):string;'
	text15='''
                    smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    if (AllRemoved==false) {
'''
	text16='                        outMsg="After '+OnceFunName+', Max K=3";'
	text17='''
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    } else {
'''
	text18='                        outMsg="After '+OnceFunName+',Max K=2";'
	text19='''
                        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                    }
                }
'''
	print(text1)
	print(text2)
	print(text3)
	print(text4)
	print(text5)
	print(text6)
	print(text7)
	print(text8)
	print(text9)
	print(text10)
	print(text11)
	print(text12)
	print(text13)
	print(text14)
	print(text15)
	print(text16)
	print(text17)
	print(text18)
	print(text19)
	GenMaxTestReturn(CallFunName)



def GenDecompositionFun(FunName,Parameters,BodyCode):
	head="      proc "+FunName+Parameters
	print(head)
	print(TrussDecoFunStart)
	print(BodyCode)
	print(DecompositionEndCheck)
	GenDecompositionOutput(FunName)
	GenReturn(FunName)





def	GenFunCall(IsAtomic:bool,FunName:str):
	text='''

                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,
'''
	NonAtomicVal='''
                      PTriCount,gEdgeDeleted);

'''
	AtomicVal='''
                      AtoTriCount,gEdgeDeleted);
'''
	print("                repMsg="+FunName+"(kValue,")
	print(text)
	if IsAtomic : 
		print(AtomicVal)
	else:
		print(NonAtomicVal)



# This function is used for all the tests
def GenCompleteTest():
#First for Truss Tests
	text1='''
          if (kValue>0) {// k-truss analysis
'''
	text2='''
                var PTriCount=makeDistArray(Ne,int);
'''
	print(text1)
	print(text2)
	print(InitialCount)
#	GenFunCall(False,"kTrussNaiveListIntersection")
	print(InitialCount)
#	GenFunCall(False,"kTrussNaiveSetSearchSmall")
	print(InitialCount)
#	GenFunCall(False,"kTrussNaiveSetSearchSmallSeq")
	print(InitialCount)
	GenFunCall(False,"kTrussNaivePathMerge")
	print(InitialCount)
	GenFunCall(False,"kTrussNaiveMinSearch")
	text3='''
                var AtoTriCount=makeDistArray(Ne,atomic int);
'''
	print(text3)
	print(InitialCountAtomic)
	GenFunCall(True,"kTrussPathMerge")
	print(InitialCountAtomic)
	GenFunCall(True,"kTrussNonMinSearch")
	print(InitialCountAtomic)
	GenFunCall(True,"kTrussSeqMinSearch")
	print(InitialCountAtomic)
	GenFunCall(True,"kTrussMinSearch")
	print(InitialCountAtomic)
	GenFunCall(True,"kTrussMix")

	text4='''

          }// end of k-truss analysis
'''
	print(text4)

#Second, for Max Truss Tests
 
	text21='''
          if (kValue==-1) {// max k-truss analysis
                var PTriCount=makeDistArray(Ne,int);
'''
	print(text21)
	print(InitialCount)
	GenFunCall(False,"MaxTrussNaivePathMerge")
	text23='''
                var AtoTriCount=makeDistArray(Ne,atomic int);
'''

	print(text23)


	print(InitialCountAtomic)
	GenFunCall(True,"MaxTrussPathMerge")
	print(InitialCountAtomic)
	GenFunCall(True,"MaxTrussNonMinSearch")
	print(InitialCountAtomic)
	GenFunCall(True,"MaxTrussSeqMinSearch")
	print(InitialCountAtomic)
	GenFunCall(True,"MaxTrussMinSearch")
	print(InitialCountAtomic)
	GenFunCall(True,"MaxTrussMix")


	text24='''

          }// end of max k-truss analysis
'''
	print(text24)


#Third, for Truss Decomposition Tests
	text31='''
          if (kValue==-2) {
                var PTriCount=makeDistArray(Ne,int);
'''
	print(text31)
	print(InitialCount)
	print("                kValue=3;")
	GenFunCall(False,"TrussDecoNaivePathMerge")
	print(InitialCount)
	print("                kValue=3;")
	GenFunCall(False,"TrussDecoNaiveMinSearch")



	text32='''
                var AtoTriCount=makeDistArray(Ne,atomic int);
'''
	print(text32)
	print(InitialCountAtomic)
	print("                kValue=3;")
	GenFunCall(True,"TrussDecoPathMerge")
	print(InitialCountAtomic)
	print("                kValue=3;")
	GenFunCall(True,"TrussDecoNonMinSearch")
	print(InitialCountAtomic)
	print("                kValue=3;")
	GenFunCall(True,"TrussDecoSeqMinSearch")
	print(InitialCountAtomic)
	print("                kValue=3;")
	GenFunCall(True,"TrussDecoMinSearch")
	print(InitialCountAtomic)
	print("                kValue=3;")
	GenFunCall(True,"TrussDecoMix")

	text34='''

          }// end of truss decomposition analysis
'''
	print(text34)





BeginCode='''
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





'''

#The following is the original code
'''


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
                                  //we find duplicated edge
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
      proc kTrussNaiveListIntersectionSmall(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
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
                                  //we find duplicated edge
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

          outMsg="After KTruss Naive List Intersection Small,Given k="+k:string+" All removed="+AllRemoved:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Small,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Small,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Small,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussNaiveListIntersectionSmall





      // For undirected graph, using naive method. Its performance should be worse, but it is a simple implementation to 
      // check the correctness of the results
      proc kTrussNaiveListIntersectionSmallSeq(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
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
                                  //we find duplicated edge
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
                                   for x in dst[beginTmp..endTmp] {
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

          outMsg="After KTruss Naive List Intersection Small Seq,Given k="+k:string+" All removed="+AllRemoved:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Small Seq,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Small Seq,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Small Seq,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussNaiveListIntersectionSmallSeq



      // For undirected graph, using Naive and list intersection method. It should have worst performance.
      // This procedure is just used for worst case test
      proc kTrussNaiveListIntersectionSeq(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
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
                                  //we find duplicated edge
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
                               for x in dst[beginTmp..endTmp]  {
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
                               for x in dstR[beginTmp..endTmp]  {
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
                               for x in dst[beginTmp..endTmp]  {
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
                               for x in dstR[beginTmp..endTmp]  {
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
                               for s in uadj {
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

          outMsg="After KTruss Naive List Intersection Seq,Given k="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Seq,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Seq,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive List Intersection Seq,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussNaiveListIntersectionSeq




      // For undirected graph, using Naive and list intersection method. It should have worst performance.
      // This procedure is just used for worst case test
      proc kTrussNaivePathMerge(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
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
                                  //we find duplicated edge
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
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge {
                         TriCount[i]=0;
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
                           while ( (iu <=endUf) &&   (jv<=endVf))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dst[jv]!=u) && (dst[iu]!=v) && ( EdgeDeleted[iu] ==-1) && (EdgeDeleted[jv]==-1) ) {
                             {
                                 if dst[iu]==dst[jv] {
                                     TriCount[i]+=1;
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
                           while ( (iu <=endUf) &&   (jv<=endVb))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             ev=findEdge(dstR[jv],v);
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dstR[jv]!=u) && (dst[iu]!=v) && ( EdgeDeleted[iu] ==-1) && (EdgeDeleted[ev]==-1) ) {
                             {
                                 if dst[iu]==dstR[jv] {
                                     TriCount[i]+=1;
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
                           while ( (iu <=endUb) &&   (jv<=endVf))  {
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
                                     TriCount[i]+=1;
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
                           while ( (iu <=endUb) &&   (jv<=endVb))  {
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
                             //if ( (dstR[jv]!=u) && (dstR[iu]!=v) && ( EdgeDeleted[eu] ==-1) && (EdgeDeleted[ev]==-1) ) {
                             {
                                 if dstR[iu]==dstR[jv] {
                                     TriCount[i]+=1;
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

          outMsg="After KTruss Naive Path Merge,Given k="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Path Merge,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Path Merge,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Path Merge,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc KTrussNaivePathMerge





      //For undirected graph, we use list intersection to calculate the number of triangles. 
      //But affected edge search is normal. 
      //This procedure is used to show how list intersection can affect the performance compared with our edges search method.
      proc kTrussNaiveMinSearch(k:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
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
                                  //we find duplicated edge
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
                  AllRemoved=false;
              } else {
                  tmpi+=1;
              }
          }


          outMsg="After KTruss Naive Min Search,Given K="+k:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Min Search,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Min Search,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After KTruss Naive Min Search,Totally remove "+tmpi:string+ " Edges";
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      }// end of proc KTruss Naive Min Search


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
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
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
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
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
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=exactEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ((EdgeDeleted[e] ==-1) && (x !=u) && (i<e)) {
                                                 var e3=exactEdge(x,u);
                                                 if (e3!=-1) {
                                                     if ((EdgeDeleted[e3]==-1)  && (i<e3)) {
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


          outMsg="After KTrussMix,Given K="+k:string +" All Removed="+AllRemoved:string;
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
                                  //we find duplicated edge
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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



      //For undirected graph, using the naive method
      proc TrussDecompositionNaivePathMerge(kvalue:int,nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
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
          var largest:int;
          largest=Ne;


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
                                  //we find duplicated edge
                             }
                        }
                    }
              }        
          }// end of coforall loc        

          //writeln("After Preprocessing");


          timer.start();

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
                           while ( (iu <=endUf) &&   (jv<=endVf))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dst[jv]!=u) && (dst[iu]!=v) && ( EdgeDeleted[iu] ==-1) && (EdgeDeleted[jv]==-1) ) {
                             {
                                 if dst[iu]==dst[jv] {
                                     TriCount[i]+=1;
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
                           while ( (iu <=endUf) &&   (jv<=endVb))  {
                             if  ( (EdgeDeleted[iu] !=-1) || (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             ev=findEdge(dstR[jv],v);
                             if ( (EdgeDeleted[ev]!=-1) || (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dstR[jv]!=u) && (dst[iu]!=v) && ( EdgeDeleted[iu] ==-1) && (EdgeDeleted[ev]==-1) ) {
                             {
                                 if dst[iu]==dstR[jv] {
                                     TriCount[i]+=1;
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
                           while ( (iu <=endUb) &&   (jv<=endVf))  {
                             eu=findEdge(dstR[iu],u);
                             if  ( (EdgeDeleted[eu] !=-1) || (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (EdgeDeleted[jv]!=-1) || (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dst[jv]!=u) && (dstR[iu]!=v) && ( EdgeDeleted[eu] ==-1) && (EdgeDeleted[jv]==-1) ) {
                             {
                                 if dstR[iu]==dst[jv] {
                                     TriCount[i]+=1;
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
                           while ( (iu <=endUb) &&   (jv<=endVb))  {
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
                             //if ( (dstR[jv]!=u) && (dstR[iu]!=v) && ( EdgeDeleted[eu] ==-1) && (EdgeDeleted[ev]==-1) ) {
                             {
                                 if dstR[iu]==dstR[jv] {
                                     TriCount[i]+=1;
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
                     }// end of forall. We get the number of triangles for each edge
                  }// end of  on loc 

              } // end of coforall loc in Locales 

              SetCurF.clear();
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

              var tmpi=0;
              if (ConFlag==false) {
                  while tmpi<Ne  {
                      if (EdgeDeleted[tmpi]==-1) {
                          ConFlag=true;
                          //k=k+1;
                          //break;
                      } else {
                          tmpi+=1;
                      }
                  }
                  if (ConFlag) {
                      k+=1;
                  }
                  if (tmpi>0) {
                      largest=tmpi;
                  }
              }
              


              N2+=1;
          }// end while 



          timer.stop();
          outMsg="After Truss Naive Decomposition Path Merge, Max K ="+(k-1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Naive Decomposition Path Merge,Total execution time="+(timer.elapsed()):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Naive Decomposition Path Merge,Total number of iterations ="+N2:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="After Truss Naive Decomposition Path Merge,The largest k-truss edges="+(Ne-largest):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          AllRemoved=true;
          var countName = st.nextName();
          var countEntry = new shared SymEntry(EdgeDeleted);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;
      } // end of proc TrussDecompositionNaivePathMerge




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
          var largest:int;
          largest=Ne;


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

              var tmpi=0;
              if (ConFlag==false) {
                  while tmpi<Ne  {
                      if (EdgeDeleted[tmpi]==-1) {
                          ConFlag=true;
                          //k=k+1;
                          //break;
                      } else {
                          tmpi+=1;
                      }
                  }
                  if (ConFlag) {
                      k+=1;
                  }
                  if (tmpi>0) {
                      largest=tmpi;
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
          outMsg="After Truss Decomposition List Intersection, The largest k truss edges ="+(Ne-largest):string;
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
          var RemovedEdge: atomic int;
          var timer:Timer;
          var k=kvalue;
          var largest:int;
          RemovedEdge.write(0);
          largest=Ne;


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
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
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
                             if (DupE!=-1) {
                                  //we find duplicated edge
                             }
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
                                   forall x in dst[beginTmp..endTmp] {
                                       var  e=exactEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
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
                                  //we find duplicated edge
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                                  //we find duplicated edge
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
                                       if (e!=-1){
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
                                       if (e!=-1){
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
                repMsg=kTrussNaiveSetSearchSmall(kValue,

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
                repMsg=kTrussNaiveSetSearchSmallSeq(kValue,

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
                repMsg=kTrussNaivePathMerge(kValue,

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
                repMsg=kTrussNaiveMinSearch(kValue,

                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,
                      PTriCount);


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
                var PTriCount=makeDistArray(Ne,int);
                /*
                PTriCount=0;
                repMsg=TrussDecompositionNaive(3,ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,PTriCount);
                */
                PTriCount=0;
                repMsg=TrussDecompositionNaivePathMerge(3,
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a, PTriCount);

                var AtoTriCount=makeDistArray(Ne,atomic int);
                forall i in AtoTriCount {
                      i.write(0);
                }
                repMsg=TrussDecompositionTruss(3,
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
                repMsg=TrussDecompositionTrussMix(3,
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
                var aPlTriCount=makeDistArray(Ne,atomic int);//for local use
                forall i in 0..Ne-1 {
                    PTriCount[i].write(0);
                    aPlTriCount[i].write(0);
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
                      toSymEntry(ag.getDST_R(), int).a, aPlTriCount);
                forall i in 0..Ne-1 {// first keep last time's results
                             lEdgeDeleted[i]=EdgeDeleted[i];
                             PTriCount[i].write(aPlTriCount[i].read());
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
                             aPlTriCount[i].write(PTriCount[i].read());
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
                              toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
                         if (!AllRemoved) { //the up value is the max k
                                ConLoop=false;
                         } else {// we will check the mid value to reduce kUp
                            kMid= (kLow+kUp)/2;
                            forall i in 0..Ne-1 {
                                lEdgeDeleted[i]=EdgeDeleted[i];
                                aPlTriCount[i].write(PTriCount[i].read());
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
                                 toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
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
                                            PTriCount[i].write(aPlTriCount[i].read());
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
                                             toSymEntry(ag.getDST_R(), int).a, aPlTriCount,lEdgeDeleted);
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


      return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedTruss", segTrussMsg);
    }


}



'''




UnDirectedGraphTestBegin='''


      if (!Directed) {//for undirected graph

'''



UnDirectedGraphTestEnd='''

      } //end of  undirected graph
      
'''

EndCode='''

      return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedTruss", segTrussMsg);
    }


}

'''








print(BeginCode)
print("//@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
print("//Begin of K-Truss Functions")
GenTrussFun("kTrussNaiveListIntersection",Parameters,NaiveListIntersectionBodyCode)
GenTrussFun("kTrussNaiveSetSearchSmall",Parameters,NaiveSetSearchSmallBodyCode)
GenTrussFun("kTrussNaiveSetSearchSmallSeq",Parameters,NaiveSetSearchSmallSeqBodyCode)
GenTrussFun("kTrussNaivePathMerge",Parameters,NaivePathMergeBodyCode)
GenTrussFun("kTrussNaiveMinSearch",Parameters,NaiveMinSearchBodyCode)
GenTrussFun("kTrussPathMerge",ParametersAtomic,PathMergeBodyCode)
GenTrussFun("kTrussNonMinSearch",ParametersAtomic,NonMSTrussAtomicBodyCode)
GenTrussFun("kTrussSeqMinSearch",ParametersAtomic,SeqTrussAtomicBodyCode)
GenTrussFun("kTrussMinSearch",ParametersAtomic,TrussAtomicBodyCode)
GenTrussFun("kTrussMix",ParametersAtomic,TrussMixAtomicBodyCode)
print("//End of K-Truss Functions")
print("//@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
print("")
print("")


print("//@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
print("//Begin of Max K-Truss Functions")
GenMaxTrussFun("kTrussNaivePathMerge","MaxTrussNaivePathMerge",MaxNaivePathMergeBodyCode)
GenMaxTrussAtomicFun("kTrussPathMerge","MaxTrussPathMerge",MaxPathMergeBodyCode)
GenMaxTrussAtomicFun("kTrussNonMinSearch","MaxTrussNonMinSearch",MaxNonMinSearchBodyCode)
GenMaxTrussAtomicFun("kTrussSeqMinSearch","MaxTrussSeqMinSearch",MaxSeqMinSearchBodyCode)
GenMaxTrussAtomicFun("kTrussMinSearch","MaxTrussMinSearch",MaxMinSearchBodyCode)
GenMaxTrussAtomicFun("kTrussMix","MaxTrussMix",MaxTrussMixBodyCode)
print("//End of Max K-Truss Functions")
print("//@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
print("")
print("")

print("//@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
print("//Begin of Truss Decomposition Functions")
GenDecompositionFun("TrussDecoNaiveListIntersection",Parameters,NaiveListIntersectionBodyCode)
GenDecompositionFun("TrussDecoNaiveSetSearchSmall",Parameters,NaiveSetSearchSmallBodyCode)
GenDecompositionFun("TrussDecoNaiveSetSearchSmallSeq",Parameters,NaiveSetSearchSmallSeqBodyCode)
GenDecompositionFun("TrussDecoNaivePathMerge",Parameters,NaivePathMergeBodyCode)
GenDecompositionFun("TrussDecoNaiveMinSearch",Parameters,NaiveMinSearchBodyCode)
GenDecompositionFun("TrussDecoPathMerge",ParametersAtomic,PathMergeBodyCode)
GenDecompositionFun("TrussDecoNonMinSearch",ParametersAtomic,NonMSTrussAtomicBodyCode)
GenDecompositionFun("TrussDecoSeqMinSearch",ParametersAtomic,SeqTrussAtomicBodyCode)
GenDecompositionFun("TrussDecoMinSearch",ParametersAtomic,TrussAtomicBodyCode)
GenDecompositionFun("TrussDecoMix",ParametersAtomic,TrussMixAtomicBodyCode)
print("//End of Truss Decomposition Functions")
print("//@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
print("")
print("")
print("//@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
print("//Begin of Undirected Graph ")
print(UnDirectedGraphTestBegin)

GenCompleteTest()

print(UnDirectedGraphTestEnd)
print("//End of Undirected Graph Test")
print("//@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
print("")
print("")
print(EndCode)
