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

      var TotalCnt:[0..0] int;
      var subTriSum: [0..numLocales-1] int;

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



	  var timer:Timer;
	  timer.start();
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
                         }
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 

          coforall loc in Locales {
                on loc {

                     var ld = nei.localSubdomain();
                     var startVer = ld.low;
                     var endVer = ld.high;
                     var curnum=0:int;
                     forall i in startVer..endVer with (+ reduce curnum){
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
                             TriCtr[i]=(curnum-(NeiTriNum[i].read()+TriNum[i].read())*2/3+TriNum[i].read()):real/TotalCnt[0]:real;
                             writeln("NAIVE Number of Triangles for vertex ", i," =",TriNum[i].read());
                             writeln("NAIVE Sum of number of Triangles for vertex ", i,"'s neighbour =",NeiTriNum[i].read());
                             writeln("NAIVE Triangle Centrality of  vertex ", i," =",TriCtr[i]);
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TriCtr);
          st.addEntry(countName, countEntry);
	  timer.stop();
	  writeln("Elapsed time for naive Triangle Centrality="+(timer.elapsed()):string); 
          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }//END TRI_CTR_KERNEL
      
      proc triCtr_kernelMST(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{
	  var timer:Timer;
          TriCtr=0.0;
          forall i in TriNum {
              i.write(0);
          }
          forall i in NeiTriNum {
              i.write(0);
          }


          TotalCnt=0;
          subTriSum=0;	  
	  timer.start();
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
                         }
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 

          coforall loc in Locales {
                on loc {

                     var ld = nei.localSubdomain();
                     var startVer = ld.low;
                     var endVer = ld.high;
                     var curnum=0:int;
                     forall i in startVer..endVer with (+ reduce curnum){
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
                             TriCtr[i]=(curnum-(NeiTriNum[i].read()+TriNum[i].read())*2/3+TriNum[i].read()):real/TotalCnt[0]:real;
                             writeln("MST Number of Triangles for vertex ", i," =",TriNum[i].read());
                             writeln("MST Sum of number of Triangles for vertex ", i,"'s neighbour =",NeiTriNum[i].read());
                             writeln("MST Triangle Centrality of  vertex ", i," =",TriCtr[i]);
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

      proc triCtr_kernelPathMerge(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{
	  //writeln("Beginning of PM method");
          TriCtr=0.0;
          forall i in TriNum {
              i.write(0);
          }
          forall i in NeiTriNum {
              i.write(0);
          }


          TotalCnt=0;
          subTriSum=0;	
          
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



	  var timer:Timer;
	  timer.start();
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
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
                             eu=findEdge(dstR[iu],u);
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
                             eu=findEdge(dstR[iu],u);
                             ev=findEdge(dstR[jv],v);
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


	  //writeln("Beginning of subTriSum");
          for i in subTriSum {
             TotalCnt[0]+=i;
          }

	   //writeln("Beginning of NeiTriNum");
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
                         }
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 

          coforall loc in Locales {
                on loc {

                     var ld = nei.localSubdomain();
                     var startVer = ld.low;
                     var endVer = ld.high;
                     var curnum=0:int;
                     forall i in startVer..endVer with (+ reduce curnum){
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
                             TriCtr[i]=(curnum-(NeiTriNum[i].read()+TriNum[i].read())*2/3+TriNum[i].read()):real/TotalCnt[0]:real;
                             writeln("Path Merge Number of Triangles for vertex ", i," =",TriNum[i].read());
                             writeln("Path Merge Sum of number of Triangles for vertex ", i,"'s neighbour =",NeiTriNum[i].read());
                             writeln("Path Merge Triangle Centrality of  vertex ", i," =",TriCtr[i]);
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TriCtr);
          st.addEntry(countName, countEntry);
	  timer.stop();
	  writeln("Elapsed time for Path Merge Triangle Centrality="+(timer.elapsed()):string); 
          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }//END TRI_CTR_KERNEL_PATH_MERGE
      
      proc triCtr_kernel_smallSet(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{

          TriCtr=0.0;
          forall i in TriNum {
              i.write(0);
          }
          forall i in NeiTriNum {
              i.write(0);
          }


          TotalCnt=0;
          subTriSum=0;	
          
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



	  var timer:Timer;
	  timer.start();
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     var triCount=0:int;
                     // each locale only handles the edges owned by itself
                     forall i in startEdge..endEdge with (+ reduce triCount) {
                         //TriCount[i]=0;
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
                           while ( (iu <=endUf) &&   (jv<=endVf))  {
                             if  ( (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dst[jv]!=u) && (dst[iu]!=v) ) {
                             {
                                 if dst[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     triCount += 1;
                                     NeiAry[i] = true;
                                     NeiAry[iu] = true;
                                     NeiAry[jv] = true;
                                     TriNum[u].add(1);
                                     TriNum[v].add(1);
                                     TriNum[dst[jv]].add(1);                            
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
                           while ( (iu <=endUf) &&   (jv<=endVb))  {
                             if  ( (dst[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             ev=findEdge(dstR[jv],v);
                             if (  (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dstR[jv]!=u) && (dst[iu]!=v) ) {
                             {
                                 if dst[iu]==dstR[jv] {
                                     //TriCount[i]+=1;
                                     triCount += 1;
                                     NeiAry[i] = true;
                                     NeiAry[iu] = true;
                                     var tmpe = exactEdge(dstR[jv], srcR[jv]);
                                     NeiAry[tmpe] = true;
                                     TriNum[u].add(1);
                                     TriNum[v].add(1);
                                     TriNum[dst[iu]].add(1);                                         
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
                           //writeln("Enter while 3 in iteration ",N2 , " and edge=", i);
                           while ( (iu <=endUb) &&   (jv<=endVf))  {
                             eu=findEdge(dstR[iu],u);
                             if  ( (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (dst[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dst[jv]!=u) && (dstR[iu]!=v) ) {
                             {
                                 if dstR[iu]==dst[jv] {
                                     //TriCount[i]+=1;
                                     triCount += 1;
                                     TriNum[u].add(1);
                                     TriNum[v].add(1);
                                     TriNum[dst[jv]].add(1);
                                     var tmpe = exactEdge(dstR[iu], srcR[iu]);
                                     NeiAry[tmpe] = true;
                                     NeiAry[jv] = true;
                                     NeiAry[i] = true;                                       
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
                           //writeln("Enter while 4 in iteration ",N2 , " and edge=", i);
                           while ( (iu <=endUb) &&   (jv<=endVb))  {
                             eu=findEdge(dstR[iu],u);
                             ev=findEdge(dstR[jv],v);
                             if  ( (dstR[iu]==v) ) {
                                  iu+=1;
                                  continue;
                             }
                             if ( (dstR[jv]==u) ) {
                                  jv+=1;
                                  continue;
                             }
                             //if ( (dstR[jv]!=u) && (dstR[iu]!=v) ) {
                             {
                                 if dstR[iu]==dstR[jv] {
                                 //TriCount
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
                         }
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 

          coforall loc in Locales {
                on loc {

                     var ld = nei.localSubdomain();
                     var startVer = ld.low;
                     var endVer = ld.high;
                     var curnum=0:int;
                     forall i in startVer..endVer with (+ reduce curnum){
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
                             TriCtr[i]=(curnum-(NeiTriNum[i].read()+TriNum[i].read())*2/3+TriNum[i].read()):real/TotalCnt[0]:real;
                             writeln("NAIVE Number of Triangles for vertex ", i," =",TriNum[i].read());
                             writeln("NAIVE Sum of number of Triangles for vertex ", i,"'s neighbour =",NeiTriNum[i].read());
                             writeln("NAIVE Triangle Centrality of  vertex ", i," =",TriCtr[i]);
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TriCtr);
          st.addEntry(countName, countEntry);
	  timer.stop();
	  writeln("Elapsed time for Triangle Centrality Small Set Seq="+(timer.elapsed()):string); 
          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }//END TRI_CTR_KERNEL  
      
      
      proc triCtr_kernelSetSmallSearch(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{

          TriCtr=0.0;
          forall i in TriNum {
              i.write(0);
          }
          forall i in NeiTriNum {
              i.write(0);
          }


          TotalCnt=0;
          subTriSum=0;	
                    
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



	  var timer:Timer;
	  timer.start();
              coforall loc in Locales {
                  on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
                     var triCount = 0:int;

                     forall i in startEdge..endEdge with (+ reduce triCount){
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
                             if ((sV!=lV) ){
                                if ( (nei[sV]>0)  ){
                                   forall x in dst[beginTmp..endTmp] with (ref sVadj) {
                                       var  e=exactEdge(sV,x);//here we find the edge ID to check if it has been removed
                                       if (e!=-1){
                                          if ( (x !=lV)) {
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
                                          if ((x !=lV)) {
                                                 sVadj.add(x);
                                          }
                                       }  
                                   }
                                }
                                if  (! sVadj.isEmpty() ){
                                   var Count=0:int;
                                   forall s in sVadj with ( + reduce triCount) {
                                       var ds1=nei[s]+neiR[s];
                                       var e:int;
                                       if (ds1<ldV) {
                                          e=findEdge(s,lV);
                                       } else {
                                          e=findEdge(lV,s);
                                       }
                                       if ( (e!=-1)  && (e!=i) ) {
                                              triCount +=1;
                                              TriNum[u].add(1);
                                              TriNum[v].add(1);
                                              TriNum[s].add(1);
                                              NeiAry[e] = true;
                                              NeiAry[i] = true;
                                              var tmpe = findEdge(sV, s);
                                              NeiAry[tmpe] = true;
                                       }
                                   }
                                   //TriCount[i] = Count;
                                   // here we get the number of triangles of edge ID i
                                }// end of if 
                            }//end of if EdgeDeleted[i]==-1
                         }// end of triangle counting 





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
                         }
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 

          coforall loc in Locales {
                on loc {

                     var ld = nei.localSubdomain();
                     var startVer = ld.low;
                     var endVer = ld.high;
                     var curnum=0:int;
                     forall i in startVer..endVer with (+ reduce curnum){
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
                             TriCtr[i]=(curnum-(NeiTriNum[i].read()+TriNum[i].read())*2/3+TriNum[i].read()):real/TotalCnt[0]:real;
                             writeln("NAIVE Number of Triangles for vertex ", i," =",TriNum[i].read());
                             writeln("NAIVE Sum of number of Triangles for vertex ", i,"'s neighbour =",NeiTriNum[i].read());
                             writeln("NAIVE Triangle Centrality of  vertex ", i," =",TriCtr[i]);
                     }

                }// end of  on loc 
          } // end of coforall loc in Locales 
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TriCtr);
          st.addEntry(countName, countEntry);
	  timer.stop();
	  writeln("Elapsed time for Set Small Search Triangle Centrality="+(timer.elapsed()):string); 
          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }//END TRI_CTR_KERNEL          
      

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
              repMsg=triCtr_kernelMST(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a);
              repMsg=triCtr_kernelPathMerge(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a); 
              repMsg=triCtr_kernel_smallSet(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a);     
              repMsg=triCtr_kernelSetSmallSearch(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a);                                                               
      }
      
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }// end of seg







    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedGraphTriCtr", segTriCtrMsg);
    }


}

