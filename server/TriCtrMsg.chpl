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





      coforall loc in Locales {
          on loc {
             var ld = src.localSubdomain();
             var startEdge = ld.low;
             var endEdge = ld.high;
             var triCount=0:int;
             // each locale only handles the edges owned by itself
             forall i in startEdge..endEdge with (+ reduce triCount){
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
                                         triCount+=1;
                                         TriNum[sv1].add(1);
                                         TriNum[lv2].add(1);
                                         TriNum[v4].add(1);					     
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
                                if (( lv2!=v4 ) ) {
                                       // we first check if  the two different vertices can be the third edge
                                       var dv4=nei[v4]+neiR[v4];
                                       if ldv2<dv4 {
                                          tmpe=findEdge(lv2,v4);
                                       } else {
                                          tmpe=findEdge(v4,lv2);
                                       }
                                       if (tmpe!=-1) {// there is such third edge
                                         triCount+=1;
                                         TriNum[sv1].add(1);
                                         TriNum[lv2].add(1);
                                         TriNum[v4].add(1);
                                       }
                                }
                             }
                         }// end of  forall j in nextStart..nextEnd 
                      }// end of if
                  }// end of triangle counting

           // i is an undeleted edge
	      
             }// end of forall. We get the number of triangles for each edge
             subTriSum[here.id]=triCount;
          }// end of  on loc 
      } // end of coforall loc in Locales  


          for i in subTriSum {
             TotalCnt[0]+=i;
          }

          for u in 0..Nv-1 {
          //Go through u's adjacency list
          writeln("Checking for, ", u);
              var startEdge = start_i[u];
              var endEdge = start_i[u] + nei[u] -1;
              
              for x in startEdge..endEdge {
                  //For each edge in u's adjacency list
                  var eOneVOne = src[x];
                  var eOneVTwo = dst[x];
                  writeln("adj 1 ", eOneVOne, ", ", eOneVTwo);
                  var eOneVTwoStart = start_i[eOneVTwo];
                  var eOneVTwoEnd = eOneVTwoStart + nei[eOneVTwoStart] -1;
                  var check=true:bool;
                  if (nei[eOneVTwoStart] > 0) {
                  for y in eOneVTwoStart..eOneVTwoEnd {
		       var w = dst[y];
		       writeln("adj 2F ", w, " check against ", u);
		       var e1 = findEdge(w,u);
		       writeln("And e1", e1);
		       if (e1 != -1) {
		           check = false;
		       }
		       else {
		       writeln("No problem for ", u, ", ", dst[x], ", ", w);
		       }
                  }
                  }
                  eOneVTwoStart = start_iR[eOneVTwo];
                  eOneVTwoEnd = eOneVTwoStart + neiR[eOneVTwo] -1;
                  if (neiR[eOneVTwo] > 0) {                  
                  for y in eOneVTwoStart..eOneVTwoEnd {
		       var w = dstR[y];
		       writeln("adj 2R ", w, " check against ", u);
		       var e1 = findEdge(w,u);
		       writeln("And e1", e1);
		       if (e1 != -1) {
		           check = false;
		       }
		       else {
		       writeln("No problem for ", u, ", ", dst[x], ", ", w);
		       }
                  }
                  }                
                  if check == true {
                      writeln("Adding ", x, " to u ", u);
                      NeiTriNum[u].add(TriNum[dst[x]].read());
                  }
              }
          
          }
	  writeln("NeiTriNum, ", NeiTriNum);
	  writeln("TriNum, ", TriNum);
	  writeln("TotalCnt, ", TotalCnt[0]);
	  
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
                             //TriCtr[i]=(curnum-(NeiTriNum[i].read()+TriNum[i].read())*2/3+TriNum[i].read()):real/TotalCnt[0]:real;
                             TriCtr[i] = (NeiTriNum[i].read() + TriNum[i].read()):real/TotalCnt[0]:real;
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

