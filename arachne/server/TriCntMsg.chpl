module TriCntMsg {
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


  use AryUtil;
  use List; 
  //use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use Utils;


  private config const logLevel = ServerConfig.logLevel;
  const smLogger = new Logger(logLevel);
  
  /**
   * Utility function to handle try/catch when trying to close objects.
   */
  proc closeFinally(c): bool {
    var success = true;
    try {
        c.close();
    } catch {
        success = false;
    }
    return success;
  }

  //Given a graph, calculate its number of triangles
  proc segTriCntMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
      var repMsg: string;
      //var (n_verticesN,n_edgesN,directedN,weightedN,graphEntryName,restpart )
      //    = payload.splitMsgToTuple(6);


      //var msgArgs = parseMessageArgs(payload, argSize);
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
      if (directedN:int)==1 {
          Directed=true;
      }
      if (weightedN:int)==1 {
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

      // triangle counting for direct graph
      proc tri_kernel(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int):string throws{

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


          coforall loc in Locales {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.lowBound;
                     var endEdge = ld.highBound;
                     var triCount=0:int;


                     forall i in startEdge..endEdge with (+ reduce triCount ){
                         var u = src[i];
                         var v = dst[i];
                         var du=nei[u];
                         var dv=nei[v];
                         {
                             //writeln("1 My Locale=",here.id," Current Edge=",i, "=<",u,",",v,">");
                             var beginTmp=start_i[u];
                             var endTmp=beginTmp+nei[u]-1;
                             if ( (u!=v) ){
                                if ( (nei[u]>1)  ){
                                   forall x in dst[beginTmp..endTmp] with (+ reduce triCount )  {
                                       var  e=findEdge(u,x);//here we find the edge ID to check if it has been removed
                                       if (e!=1){
                                          if ( (x !=v) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                         triCount+=1;
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
                                   forall x in dst[beginTmp..endTmp] with (+ reduce triCount ) {
                                       var  e=findEdge(v,x);//here we find the edge ID to check if it has been removed
                                       if (e!=1){
                                          if ( (x !=u) && (i<e)) {
                                                 var e3=findEdge(x,v);
                                                 if (e3!=-1) {
                                                     if ( (src[e3]==x) && (dst[e3]==u) && (e<e3)) {
                                                         triCount+=1;
                                                     }
                                                 }
                                          }
                                       }
                                   }
                                }
                             }
                         }

                     } // end of forall. We get the number of triangles for each edge
                     subTriSum[here.id]=triCount;
                     RemoteAccessTimes[here.id]=0;
                     LocalAccessTimes[here.id]=0;


                }// end of  on loc 
          } // end of coforall loc in Locales 
          return "success";
      }



      proc tri_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{
          coforall loc in Locales   {
                   on loc {
                       var triCount=0:int;
                       var remoteCnt=0:int;
                       var localCnt=0:int;
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var ld=srcf.localSubdomain();
                       var ldR=srcfR.localSubdomain();

                       // first we divide vertices based on the number of edges
                       var startVer=srcf[ld.lowBound];
                       var endVer=srcf[ld.highBound];

                       StartVerAry[here.id]=startVer;
                       EndVerAry[here.id]=endVer;
                       var startEdge=ld.lowBound;
                       var endEdge=ld.highBound;

                       var lastVer=-1;

                       //writeln("1 Locale=",here.id, " local domain=", ld, ", Reverse local domain=",ldR);

                       if (here.id>0) {
                          if EndVerAry[here.id-1]==StartVerAry[here.id] {
                             startVer+=1;    
                          } else {
                             if (StartVerAry[here.id]-EndVerAry[here.id-1]>2 ){
                                startVer=EndVerAry[here.id-1]+1;
                             }
                          }
                       }
                       if (here.id==numLocales-1) {
                             endVer=nei.size-1;
                       }
                       if (here.id ==0 ) {
                          startVer=0;
                       }

                       //writeln("3 Locale=",here.id, " Updated Starting/End Vertex=[",startVer, ",", endVer, "], StarAry=", StartVerAry, " EndAry=", EndVerAry);
                       forall u in startVer..endVer with (+ reduce triCount,+ reduce remoteCnt, + reduce localCnt) {// for all the u
                           //writeln("4 Locale=",here.id, " u=",u, " Enter coforall path");
                           var uadj= new set(int,parSafe = true);
                           //var uadj= new set(int);
                           //var uadj=  new DistBag(int,Locales); //use bag to keep the adjacency of u
                           var startu_adj:int;
                           var endu_adj:int;
                           var numu_adj:int;

                           var startuR_adj:int;
                           var enduR_adj:int;
                           var numuR_adj:int;

                           var aggu= newSrcAggregator(int);
                           aggu.copy(startu_adj,sf[u]);
                           aggu.copy(endu_adj,sf[u]+nf[u]-1);
                           aggu.copy(numu_adj,nf[u]);

                           aggu.copy(startuR_adj,sfR[u]);
                           aggu.copy(enduR_adj,sfR[u]+nfR[u]-1);
                           aggu.copy(numuR_adj,nfR[u]);
                           aggu.flush();
                           //writeln("6 Locale=",here.id, " u[",startu_adj, ",",endu_adj, "], num=",numu_adj);

                           if (numu_adj>0) {
                               if (startu_adj>=ld.lowBound && endu_adj<=ld.highBound) {
                                   forall i in df[startu_adj..endu_adj] with (ref uadj,+ reduce localCnt) {
                                      if (u<i) {
                                         uadj.add(i);
                                         localCnt+=1;
                                         //writeln("7 Locale=",here.id,  " u=",u, " add local ",i);
                                      }
                                   }
                               } else {
                                   var tmpuadj: [0..numu_adj-1]int;
                                   forall (a,b) in zip(tmpuadj,(startu_adj..endu_adj)) 
                                             with (var agg= newSrcAggregator(int)) {
                                             agg.copy(a,df[b]);
                                   }
                                   forall i in tmpuadj with (ref uadj,+ reduce remoteCnt) {
                                      if (u<i) {
                                         uadj.add(i);
                                         remoteCnt+=1;
                                         //writeln("7 Locale=",here.id,  " u=",u, " add remote ",i);
                                      }
                                   }
                               }
                           }
                           if (numuR_adj>0) {
                               if (startuR_adj>=ldR.lowBound && enduR_adj<=ldR.highBound) {
                                   forall i in dfR[startuR_adj..enduR_adj] with (ref uadj,+ reduce localCnt) {
                                      if (u<i) {
                                         uadj.add(i);
                                         localCnt+=1;
                                         // writeln("8 Locale=",here.id,  " u=",u, " add reverse lodal ",i);
                                      }
                                   }
                               } else {
                                   var tmpuadj: [0..numuR_adj-1]int;
                                   forall (a,b) in zip(tmpuadj,(startuR_adj..enduR_adj)) 
                                             with (var agg= newSrcAggregator(int)) {
                                             agg.copy(a,dfR[b]);
                                   }
                                   forall i in tmpuadj with (ref uadj,+ reduce remoteCnt) {
                                      if (u<i) {
                                         uadj.add(i);
                                         remoteCnt+=1;
                                         //writeln("8 Locale=",here.id,  " u=",u, " add reverse remote ",i);
                                      }
                                   }

                               }

                           }// end of building uadj 
                           //writeln("9 Locale=",here.id, " u=",u," got uadj=",uadj, " numu_adj=", numu_adj," numuR_adj=", numuR_adj);

                           forall v in uadj with (+reduce triCount,ref uadj,+ reduce remoteCnt, + reduce localCnt) {
                               //writeln("10 Locale=",here.id, " u=",u," and v=",v, " enter forall");
                               var vadj= new set(int,parSafe = true);
                               //var vadj= new set(int);
                               //var vadj=  new DistBag(int,Locales); //use bag to keep the adjacency of v
                               var startv_adj:int;
                               var endv_adj:int;
                               var numv_adj:int;

                               var startvR_adj:int;
                               var endvR_adj:int;
                               var numvR_adj:int;

                               var aggv= newSrcAggregator(int);
                               aggv.copy(startv_adj,sf[v]);
                               aggv.copy(endv_adj,sf[v]+nf[v]-1);
                               aggv.copy(numv_adj,nf[v]);

                               aggv.copy(startvR_adj,sfR[v]);
                               aggv.copy(endvR_adj,sfR[v]+nfR[v]-1);
                               aggv.copy(numvR_adj,nfR[v]);
                               aggv.flush();

                               if (numv_adj>0) {
                                   if (startv_adj>=ld.lowBound && endv_adj<=ld.highBound) {
                                       forall i in df[startv_adj..endv_adj] with (ref vadj,+ reduce localCnt) {
                                          if (v<i) {
                                             vadj.add(i);
                                             localCnt+=1;
                                             //writeln("11 Locale=",here.id,  " v=",v, " add local ",i);
                                          }
                                       }
                                   } else {
                                       var tmpvadj: [0..numv_adj-1]int;
                                       forall (a,b) in zip(tmpvadj,(startv_adj..endv_adj)) 
                                             with (var agg= newSrcAggregator(int)) {
                                             agg.copy(a,df[b]);
                                       }
                                       forall i in tmpvadj with (ref vadj,+ reduce remoteCnt) {
                                          if (v<i) {
                                             vadj.add(i);
                                             remoteCnt+=1;
                                             //writeln("11 Locale=",here.id,  " v=",v, " add remote ",i);
                                          }
                                       }

                                   }

                               }
                               if (numvR_adj>0) {
                                   if (startvR_adj>=ldR.lowBound && endvR_adj<=ldR.highBound) {
                                       forall i in dfR[startvR_adj..endvR_adj] with (ref vadj,+ reduce localCnt) {
                                          if (v<i) {
                                             vadj.add(i);
                                             localCnt+=1;
                                             //writeln("12 Locale=",here.id,  " v=",v, " add reverse local ",i);
                                          }
                                       }
                                   } else {
                                       var tmpvadj: [0..numvR_adj-1]int;
                                       forall (a,b) in zip(tmpvadj,(startvR_adj..endvR_adj)) 
                                             with (var agg= newSrcAggregator(int)) {
                                                 agg.copy(a,dfR[b]);
                                       }
                                       forall i in tmpvadj with (ref vadj,+reduce remoteCnt) {
                                          if (v<i) {
                                             vadj.add(i);
                                             remoteCnt+=1;
                                             //writeln("12 Locale=",here.id,  " v=",v, " add reverse remote ",i);
                                          }
                                       }

                                   }

                               }
                               //var triset= new set(int,parSafe=true);
                               //var triset= new set(int);
                               //triset=uadj & vadj;
                               //writeln("30 Locale=",here.id, " u=",u, " v=",v, " uadj=",uadj, " vadj=",vadj);
                               //var num=uadj.getSize();
                               var num=vadj.size;
                               forall i in vadj with (+ reduce triCount) {
                                   if uadj.contains(i) {
                                      triCount+=1;
                                   }
                               }
                               //writeln("31 Locale=",here.id, "tri=", triCount," u=",u, " v=",v);
                               //vadj.clear();
                           }// end forall v adj build
                           //uadj.clear();
                       }// end forall u adj build
                       subTriSum[here.id]=triCount;
                       RemoteAccessTimes[here.id]=remoteCnt;
                       LocalAccessTimes[here.id]=localCnt;
                       //writeln("100 Locale=",here.id, " subTriSum=", subTriSum);
                   }//end on loc
          }//end coforall loc
          return "success";
      }//end of tri_kernel_u

        proc triCtr_kernelPathMerge(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws {
            var NeiNonTriNum=makeDistArray(Nv,atomic int);
            var TriNum=makeDistArray(Nv,atomic int);
            var NeiTriNum=makeDistArray(Nv,atomic int);
            var NeiAry=makeDistArray(Ne,bool);
            NeiAry=false;
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

            var timer:stopwatch;
            timer.start();
            var tmptimer:stopwatch;
            tmptimer.start();
            coforall loc in Locales {
                on loc {
                    var ld = src.localSubdomain();
                    var startEdge = ld.lowBound;
                    var endEdge = ld.highBound;
                    var triCount=0:int;
                    //writeln("Start of CoForall");
                    // each locale only handles the edges owned by itself
                    forall i in startEdge..endEdge with (+ reduce triCount) {
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
                        if ((u!=v) ){
                        iu=beginUf;
                        jv=beginVf;
                        //writeln("Enter while 1 in iteration ",N2 , " and edge=", i);
                        //writeln("Before First While");
                        while ( (iu <=endUf) &&   (jv<=endVf))  {
                            if  ( (dst[iu]==v) ) {
                                iu+=1;
                                continue;
                            }
                            if ((dst[jv]==u) ) {
                                jv+=1;
                                continue;
                            }
                            {
                                if dst[iu]==dst[jv] {
                                    triCount +=1;
                                    TriNum[u].add(1);
                                    TriNum[v].add(1);
                                    TriNum[dst[jv]].add(1);
                                    NeiAry[iu] = true;
                                    NeiAry[jv] = true;
                                    NeiAry[i] = true;
                                    //TriCount[i]+=1;
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
                        //writeln("Enter while 2 in iteration ",N2 , " and edge=", i);
                        var Count=0;
                        //writeln("Before Second While");
                        while ( (iu <=endUf) && (jv<=endVb) && Count < Nv)  {
                            Count +=1;
                            if  ( (dst[iu]==v) ) {
                                iu+=1;
                                continue;
                            }
                            ev=findEdge(dstR[jv],v);
                            if ( (dstR[jv]==u) ) {
                                jv+=1;
                                continue;
                            }
                            {
                                if dst[iu]==dstR[jv] {
                                    triCount += 1;
                                    TriNum[u].add(1);
                                    TriNum[v].add(1);
                                    TriNum[dst[iu]].add(1);
                                    NeiAry[iu] = true;
                                    var tmpe = exactEdge(dstR[jv], srcR[jv]);
                                    NeiAry[tmpe] = true;
                                    NeiAry[i] = true;                                     
                                    //TriCount[i]+=1;
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


                Count = 0;
                        iu=beginUb;
                        jv=beginVf;
                        //writeln("Enter while 3 in iteration ",N2 , " and edge=", i);
                        //writeln("Before Third While");
                        while ( (iu <=endUb) &&   (jv<=endVf) && Count < Nv)  {
                            Count += 1;
                            //eu=findEdge(dstR[iu],u);
                            if  ( (dstR[iu]==v) ) {
                                iu+=1;
                                continue;
                            }
                            if ( (dst[jv]==u) ) {
                                jv+=1;
                                continue;
                            }
                            {
                                if dstR[iu]==dst[jv] {
                                    triCount += 1;
                                    TriNum[u].add(1);
                                    TriNum[v].add(1);
                                    TriNum[dst[jv]].add(1);
                                    var tmpe = exactEdge(dstR[iu], srcR[iu]);
                                    NeiAry[tmpe] = true;
                                    NeiAry[jv] = true;
                                    NeiAry[i] = true;                                     
                                    //TriCount[i]+=1;
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
                        Count = 0;
                        //writeln("Enter while 4 in iteration ",N2 , " and edge=", i);
                        //writeln("Before Fourth While");
                        while ( (iu <=endUb) &&   (jv<=endVb) && Count < Nv)  {
                            Count += 1;
                            //eu=findEdge(dstR[iu],u);
                            //ev=findEdge(dstR[jv],v);
                            if  ( (dstR[iu]==v) ) {
                                iu+=1;
                                continue;
                            }
                            if ( (dstR[jv]==u) ) {
                                jv+=1;
                                continue;
                            }
                            {
                                if dstR[iu]==dstR[jv] {
                                    triCount +=1;
                                    TriNum[u].add(1);
                                    TriNum[v].add(1);
                                    TriNum[dstR[jv]].add(1);
                                    //FindEdge
                                    var tmpe1 = exactEdge(dstR[iu], srcR[iu]);
                                    var tmpe2 = exactEdge(dstR[jv], srcR[jv]);
                                    NeiAry[tmpe1] = true;
                                    NeiAry[tmpe2] = true;
                                    NeiAry[i] = true;                                 
                                    //TriCount[i]+=1;
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
                    subTriSum[here.id]=triCount;
                }// end of  on loc 

            } // end of coforall loc in Locales 
            writeln("Elapsed time for triangle Counting path merge ="+(tmptimer.elapsed()):string);
            return "success";
        }//END TRI_CTR_KERNEL_PATH_MERGE




proc triCtr_vertex(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, vertex:int):string throws {


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
                            

            var timer:Timer;
            timer.start();
            var tmptimer:Timer;
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


            /*
            coforall loc in Locales {
                on loc {
                    var ld = src.localSubdomain();
                    var startEdge = ld.lowBound;
                    var endEdge = ld.highBound;
                    startEdge=max(startEdge,start_i[vertex]);
                    endEdge=min(endEdge,start_i[vertex]+nei[vertex]-1);
                    var triCount=0:int;
                    // each locale only handles the edges owned by itself
                    forall i in startEdge..endEdge with (+ reduce triCount) {
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
                        if ((u!=v) ){
                        iu=beginUf;
                        jv=beginVf;
                        //writeln("Enter while 1 in iteration ",N2 , " and edge=", i);
                        //writeln("Before First While");
                        while ( (iu <=endUf) &&   (jv<=endVf))  {
                            if  ( (dst[iu]==v) ) {
                                iu+=1;
                                continue;
                            }
                            if ((dst[jv]==u) ) {
                                jv+=1;
                                continue;
                            }
                            {
                                if dst[iu]==dst[jv] {
                                    triCount +=1;
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
                        //writeln("Enter while 2 in iteration ",N2 , " and edge=", i);
                        var Count=0;
                        //writeln("Before Second While");
                        while ( (iu <=endUf) && (jv<=endVb) )  {
                            Count +=1;
                            if  ( (dst[iu]==v) ) {
                                iu+=1;
                                continue;
                            }
                            ev=findEdge(dstR[jv],v);
                            if ( (dstR[jv]==u) ) {
                                jv+=1;
                                continue;
                            }
                            {
                                if dst[iu]==dstR[jv] {
                                    triCount += 1;
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
                        //writeln("Before Third While");
                        while ( (iu <=endUb) &&   (jv<=endVf) )  {
                            //eu=findEdge(dstR[iu],u);
                            if  ( (dstR[iu]==v) ) {
                                iu+=1;
                                continue;
                            }
                            if ( (dst[jv]==u) ) {
                                jv+=1;
                                continue;
                            }
                            {
                                if dstR[iu]==dst[jv] {
                                    triCount += 1;
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
            tartEdge=max(startEdge,start_i[vertex]);
                    endEdge=min(endEdge,start_i[vertex]+nei[vertex]-1);
           //writeln("Enter while 4 in iteration ",N2 , " and edge=", i);
                        //writeln("Before Fourth While");
                        while ( (iu <=endUb) &&   (jv<=endVb) )  {
                            if  ( (dstR[iu]==v) ) {
                                iu+=1;
                                continue;
                            }
                            if ( (dstR[jv]==u) ) {
                                jv+=1;
                                continue;
                            }
                            {
                                if dstR[iu]==dstR[jv] {
                                    triCount +=1;
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
                    subTriSum[here.id]=triCount;
                }// end of  on loc 
            } // end of coforall loc in Locales 
            */
            //writeln("Elapsed time for triangle Counting path merge ="+(tmptimer.elapsed()):string);
            return "success";
        }//END TRI_CTR_KERNEL_PATH_MERGE



      proc return_tri_count(): string throws{
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
          writeln("$#$#$ Triangle Number=", TotalCnt[0]);
          //writeln("LocalRatio=", (totalLocal:real)/((totalRemote+totalLocal):real),", TotalTimes=",totalRemote+totalLocal);
          //writeln("LocalAccessTimes=", totalLocal,", RemoteAccessTimes=",totalRemote);
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TotalCnt);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

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

      /*
      if (Weighted) {
           graph.withEDGE_WEIGHT(new shared SymEntry(e_weight):GenSymEntry)
                .withVERTEX_WEIGHT(new shared SymEntry(v_weight):GenSymEntry);
      }
      */

      if (Directed) {
              tri_kernel(
                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a
            );
      }
      else {

              if (vertexArray[0]==-1) { 
              triCtr_kernelPathMerge(
                toSymEntry(ag.getComp("NEIGHBOR"), int).a,
                toSymEntry(ag.getComp("START_IDX"), int).a,
                toSymEntry(ag.getComp("SRC"), int).a,
                toSymEntry(ag.getComp("DST"), int).a,
                toSymEntry(ag.getComp("NEIGHBOR_R"), int).a,
                toSymEntry(ag.getComp("START_IDX_R"), int).a,
                toSymEntry(ag.getComp("SRC_R"), int).a,
                toSymEntry(ag.getComp("DST_R"), int).a
            );
              returnary[0]=return_count();
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
                       returnary[i]=return_count();

                  }
               }

      }
      //repMsg = return_tri_count();
      repMsg = return_tri_count_array();
      timer.stop();
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }// end of segTriMsg

   use CommandMap;
   registerFunction("segmentedGraphTri", segTriCntMsg,getModuleName());
}


