module TriCntMsg {


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


  use AryUtil;
  use List; 
  use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;


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


  // directly read a stream from given file and build a  Graph  sketch in memory
  proc segStreamFileMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS, FileName,FactorS) = payload.splitMsgToTuple(6);
      //writeln("======================Graph Reading=====================");
      //writeln(NeS,NvS,ColS,DirectedS, FileName);
      var Ne=NeS:int;
      var Nv=NvS:int;
      var Factor=FactorS:int;
      var StreamNe=Ne/Factor:int;
      var StreamNv=Nv/Factor:int;
      var NumCol=ColS:int;


      var directed=false:bool;
      var weighted=false:bool;
      var timer: Timer;
      var RCMFlag=false:bool;
      var DegreeSortFlag=false:bool;



      if (DirectedS:int==1) {
          directed=true;
      }
      if NumCol>2 {
           weighted=true;
      }

      timer.start();
      var src=makeDistArray(StreamNe,int);
      var dst=makeDistArray(StreamNe,int);
      //var length=makeDistArray(StreamNv,int);
      var neighbour=makeDistArray(StreamNv,int);
      var start_i=makeDistArray(StreamNv,int);

      var e_weight = makeDistArray(StreamNe,int);
      var v_weight = makeDistArray(StreamNv,int);

      var iv=makeDistArray(StreamNe,int);

      var srcR=makeDistArray(StreamNe,int);
      var dstR=makeDistArray(StreamNe,int);
      var neighbourR=makeDistArray(StreamNv,int);
      var start_iR=makeDistArray(StreamNv,int);
      ref  ivR=iv;

      var linenum=0:int;

      var repMsg: string;

      var startpos, endpos:int;
      var sort_flag:int;
      var filesize:int;






      try {
           var f = open(FileName, iomode.r);
           // we check if the file can be opened correctly
           f.close();
      } catch {
                  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "Open file error");
      }



      proc readLinebyLine() throws {
           coforall loc in Locales  {
              on loc {
                  var randv = new RandomStream(real, here.id, false);
                  var f = open(FileName, iomode.r);
                  var r = f.reader(kind=ionative);
                  defer {
                        closeFinally(r);
                        closeFinally(f);
                  }
                  var line:string;
                  var a,b,c:string;
                  var curline=0:int;
                  var Streamcurline=0:int;
                  var srclocal=src.localSubdomain();
                  var ewlocal=e_weight.localSubdomain();

                  while r.readline(line) {
                      if NumCol==2 {
                           (a,b)=  line.splitMsgToTuple(2);
                      } else {
                           (a,b,c)=  line.splitMsgToTuple(3);
                            if ewlocal.contains(Streamcurline){
                                e_weight[Streamcurline]=c:int;
                            }
                      }
                      if srclocal.contains(Streamcurline) {
                          //if ((curline<StreamNe) || (randv.getNext()< 1.0/Factor:real) ) {
                              src[Streamcurline]=(a:int) % StreamNv;
                              dst[Streamcurline]=(b:int) % StreamNv;
                          //}
                      }
                      curline+=1;
                      Streamcurline=curline%StreamNe;
                  } 
                  forall i in src.localSubdomain() {
                       src[i]=src[i]+(src[i]==dst[i]);
                       src[i]=src[i]%StreamNv;
                       dst[i]=dst[i]%StreamNv;
                  }
                  forall i in start_i.localSubdomain()  {
                       start_i[i]=-1;
                  }
                  forall i in neighbour.localSubdomain()  {
                       neighbour[i]=0;
                  }
                  forall i in start_iR.localSubdomain()  {
                       start_iR[i]=-1;
                  }
                  forall i in neighbourR.localSubdomain()  {
                       neighbourR[i]=0;
                  }
               }// end on loc
           }//end coforall
      }//end readLinebyLine
      
      readLinebyLine();
      //start_i=-1;
      //start_iR=-1;
      timer.stop();
      //writeln("$$$$$$$$$$$$ Reading File takes ", timer.elapsed()," $$$$$$$$$$$$$$$$$$$$$$$");
      timer.start();

      proc combine_sort() throws {
             param bitsPerDigit = RSLSD_bitsPerDigit;
             var bitWidths: [0..1] int;
             var negs: [0..1] bool;
             var totalDigits: int;
             var size=StreamNe: int;

             for (bitWidth, ary, neg) in zip(bitWidths, [src,dst], negs) {
                       (bitWidth, neg) = getBitWidth(ary); 
                       totalDigits += (bitWidth + (bitsPerDigit-1)) / bitsPerDigit;
             }
             proc mergedArgsort(param numDigits) throws {
                    //overMemLimit(((4 + 3) * size * (numDigits * bitsPerDigit / 8))
                    //             + (2 * here.maxTaskPar * numLocales * 2**16 * 8));
                    var merged = makeDistArray(size, numDigits*uint(bitsPerDigit));
                    var curDigit = numDigits - totalDigits;
                    for (ary , nBits, neg) in zip([src,dst], bitWidths, negs) {
                        proc mergeArray(type t) {
                            ref A = ary;
                            const r = 0..#nBits by bitsPerDigit;
                            for rshift in r {
                                 const myDigit = (r.high - rshift) / bitsPerDigit;
                                 const last = myDigit == 0;
                                 forall (m, a) in zip(merged, A) {
                                     m[curDigit+myDigit] =  getDigit(a, rshift, last, neg):uint(bitsPerDigit);
                                 }
                            }
                            curDigit += r.size;
                        }
                        mergeArray(int); 
                    }
                    var tmpiv = argsortDefault(merged);
                    return tmpiv;
             }

             try {
                 if totalDigits <=  4 { 
                      iv = mergedArgsort( 4); 
                 } else if (totalDigits >  4) && ( totalDigits <=  8) { 
                      iv =  mergedArgsort( 8); 
                 } else if (totalDigits >  8) && ( totalDigits <=  16) { 
                      iv = mergedArgsort(16); 
                 } else if (totalDigits >  16) && ( totalDigits <=  32) { 
                      iv = mergedArgsort(32); 
                 } else if (totalDigits >32) {    
                      return "Error, TotalDigits >32";
                 }

             } catch e: Error {
                  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      e.message());
                    return "Error: %t".format(e.message());
             }
             var tmpedges=src[iv];
             src=tmpedges;
             tmpedges=dst[iv];
             dst=tmpedges;
             if (weighted){
                tmpedges=e_weight[iv];
                e_weight=tmpedges;
             }

             return "success";
      }//end combine_sort

      proc set_neighbour(){ 
          for i in 0..StreamNe-1 do {
             neighbour[src[i]]+=1;
             if (start_i[src[i]] ==-1){
                 start_i[src[i]]=i;
             }
          }
      }

      combine_sort();
      set_neighbour();



      // Make a composable SegGraph object that we can store in a GraphSymEntry later
      var graph = new shared SegGraph(StreamNe, StreamNv, directed);
      graph.withSRC(new shared SymEntry(src):GenSymEntry)
           .withDST(new shared SymEntry(dst):GenSymEntry)
           .withSTART_IDX(new shared SymEntry(start_i):GenSymEntry)
           .withNEIGHBOR(new shared SymEntry(neighbour):GenSymEntry);



      if (directed==false) { //undirected graph

          proc combine_sortR() throws {
             /* we cannot use the coargsort version because it will break the memory limit */
             param bitsPerDigit = RSLSD_bitsPerDigit;
             var bitWidths: [0..1] int;
             var negs: [0..1] bool;
             var totalDigits: int;
             var size=StreamNe: int;
             for (bitWidth, ary, neg) in zip(bitWidths, [srcR,dstR], negs) {
                 (bitWidth, neg) = getBitWidth(ary); 
                 totalDigits += (bitWidth + (bitsPerDigit-1)) / bitsPerDigit;

             }
             proc mergedArgsort(param numDigits) throws {
               //overMemLimit(((4 + 3) * size * (numDigits * bitsPerDigit / 8))
               //          + (2 * here.maxTaskPar * numLocales * 2**16 * 8));
               var merged = makeDistArray(size, numDigits*uint(bitsPerDigit));
               var curDigit = numDigits - totalDigits;
               for (ary , nBits, neg) in zip([srcR,dstR], bitWidths, negs) {
                  proc mergeArray(type t) {
                     ref A = ary;
                     const r = 0..#nBits by bitsPerDigit;
                     for rshift in r {
                        const myDigit = (r.high - rshift) / bitsPerDigit;
                        const last = myDigit == 0;
                        forall (m, a) in zip(merged, A) {
                             m[curDigit+myDigit] =  getDigit(a, rshift, last, neg):uint(bitsPerDigit);
                        }
                     }
                     curDigit += r.size;
                  }
                  mergeArray(int); 
               }
               var tmpiv = argsortDefault(merged);
               return tmpiv;
             } 

             try {
                 if totalDigits <=  2 { 
                      ivR = mergedArgsort( 2); 
                 }
                 if (totalDigits >  2) && ( totalDigits <=  8) { 
                      ivR =  mergedArgsort( 8); 
                 }
                 if (totalDigits >  8) && ( totalDigits <=  16) { 
                      ivR = mergedArgsort(16); 
                 }
                 if (totalDigits >  16) && ( totalDigits <=  32) { 
                      ivR = mergedArgsort(32); 
                 }
             } catch e: Error {
                  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      e.message());
                    return "Error: %t".format(e.message());
             }

             var tmpedges = srcR[ivR]; 
             srcR=tmpedges;
             tmpedges = dstR[ivR]; 
             dstR=tmpedges;
             return "success";

          }// end combine_sortR


          proc set_neighbourR(){
             for i in 0..StreamNe-1 do {
                neighbourR[srcR[i]]+=1;
                if (start_iR[srcR[i]] ==-1){
                    start_iR[srcR[i]]=i;
                }
             }
          }

          coforall loc in Locales  {
              on loc {
                  forall i in srcR.localSubdomain(){
                        srcR[i]=dst[i];
                        dstR[i]=src[i];
                   }
              }
          }
          combine_sortR();
          set_neighbourR();

          graph.withSRC_R(new shared SymEntry(srcR):GenSymEntry)
               .withDST_R(new shared SymEntry(dstR):GenSymEntry)
               .withSTART_IDX_R(new shared SymEntry(start_iR):GenSymEntry)
               .withNEIGHBOR_R(new shared SymEntry(neighbourR):GenSymEntry);


      }//end of undirected


      var ewName ,vwName:string;
      if (weighted) {
        fillInt(v_weight,1,1000);
        //fillRandom(v_weight,0,100);
        /*
        ewName = st.nextName();
        vwName = st.nextName();
        var vwEntry = new shared SymEntry(v_weight);
        var ewEntry = new shared SymEntry(e_weight);
        st.addEntry(vwName, vwEntry);
        st.addEntry(ewName, ewEntry);
        */
        graph.withEDGE_WEIGHT(new shared SymEntry(e_weight):GenSymEntry)
                .withVERTEX_WEIGHT(new shared SymEntry(v_weight):GenSymEntry);

      }



      var sNv=StreamNv:string;
      var sNe=StreamNe:string;
      var sDirected=directed:string;
      var sWeighted=weighted:string;

      var graphEntryName = st.nextName();
      var graphSymEntry = new shared GraphSymEntry(graph);
      st.addEntry(graphEntryName, graphSymEntry);
      repMsg =  sNv + '+ ' + sNe + '+ ' + sDirected + ' +' + sWeighted + '+created ' + graphEntryName;
      timer.stop();

      var outMsg="Sorting Edges takes "+ timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);


  }




  //Given a graph, calculate its number of triangles
  proc segTriCntMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
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


          coforall loc in Locales {
                on loc {
                     var ld = src.localSubdomain();
                     var startEdge = ld.low;
                     var endEdge = ld.high;
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
                       var startVer=srcf[ld.low];
                       var endVer=srcf[ld.high];

                       StartVerAry[here.id]=startVer;
                       EndVerAry[here.id]=endVer;
                       var startEdge=ld.low;
                       var endEdge=ld.high;

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
                               if (startu_adj>=ld.low && endu_adj<=ld.high) {
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
                               if (startuR_adj>=ldR.low && enduR_adj<=ldR.high) {
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
                                   if (startv_adj>=ld.low && endv_adj<=ld.high) {
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
                                   if (startvR_adj>=ldR.low && endvR_adj<=ldR.high) {
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
          //TotalCnt[0]/=3;
          //writeln("TriangleNumber=", TotalCnt[0]);
          //writeln("LocalRatio=", (totalLocal:real)/((totalRemote+totalLocal):real),", TotalTimes=",totalRemote+totalLocal);
          //writeln("LocalAccessTimes=", totalLocal,", RemoteAccessTimes=",totalRemote);
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TotalCnt);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }




      /*
      if (Weighted) {
           graph.withEDGE_WEIGHT(new shared SymEntry(e_weight):GenSymEntry)
                .withVERTEX_WEIGHT(new shared SymEntry(v_weight):GenSymEntry);
      }
      */

      if (Directed) {
              tri_kernel(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a);
      }
      else {

              tri_kernel_u(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a);

      }
      repMsg=return_tri_count();
      timer.stop();
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }// end of seg





// directly read a stream from given file and build the SegGraph class in memory
  proc segStreamTriCntMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS, FileName,FactorS) = payload.splitMsgToTuple(6);
      //writeln("======================Graph Reading=====================");
      //writeln(NeS,NvS,ColS,DirectedS, FileName);
      var Ne=NeS:int;
      var Nv=NvS:int;
      var Factor=FactorS:int;
      var StreamNe=Ne/Factor:int;
      var StreamNv=Nv/Factor:int;
      var NumCol=ColS:int;
      var directed=false:bool;
      var weighted=false:bool;
      if ((DirectedS:int)==1) {
          directed=true;
      }
      var timer: Timer;
      if NumCol>2 {
           weighted=true;
      }

      timer.start();
      var src=makeDistArray(StreamNe,int);
      var dst=makeDistArray(StreamNe,int);
      //var length=makeDistArray(StreamNv,int);
      var neighbour=makeDistArray(StreamNv,int);
      var start_i=makeDistArray(StreamNv,int);

      var e_weight = makeDistArray(StreamNe,int);
      var e_cnt = makeDistArray(StreamNe,int);
      var v_weight = makeDistArray(StreamNv,int);
      var v_cnt = makeDistArray(StreamNv,int);

      var iv=makeDistArray(StreamNe,int);

      var srcR=makeDistArray(StreamNe,int);
      var dstR=makeDistArray(StreamNe,int);
      var neighbourR=makeDistArray(StreamNv,int);
      var start_iR=makeDistArray(StreamNv,int);
      ref  ivR=iv;

      var linenum=0:int;

      var repMsg: string;

      var startpos, endpos:int;
      var sort_flag:int;
      var filesize:int;

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

      try {
           var f = open(FileName, iomode.r);
           // we check if the file can be opened correctly
           f.close();
      } catch {
                  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "Open file error");
      }


      proc readLinebyLine() throws {
           coforall loc in Locales  {
              on loc {
                  var randv = new RandomStream(real, here.id, false);
                  var f = open(FileName, iomode.r);
                  var r = f.reader(kind=ionative);
                  defer {
                        closeFinally(r);
                        closeFinally(f);
                  }

                  var line:string;
                  var a,b,c:string;
                  var curline=0:int;
                  var Streamcurline=0:int;
                  var srclocal=src.localSubdomain();
                  var neilocal=neighbour.localSubdomain();
                  var ewlocal=e_weight.localSubdomain();
                  forall i in srclocal {
                        src[i]=-1;
                        dst[i]=-1;
                        srcR[i]=-1;
                        dstR[i]=-1;
                        e_weight[i]=0;
                        e_cnt[i]=0;
                  }
                  forall i in neilocal {
                        neighbour[i]=0;
                        neighbourR[i]=0;
                        v_weight[i]=0;
                        v_cnt[i]=0;
                        start_i[i]=-1;
                        start_iR[i]=-1;
                  }

                  while r.readline(line) {
                      if NumCol==2 {
                           (a,b)=  line.splitMsgToTuple(2);
                      } else {
                           (a,b,c)=  line.splitMsgToTuple(3);
                            //if ewlocal.contains(Streamcurline){
                            //    e_weight[Streamcurline]=c:int;
                            //}
                      }
                      var a_hash=(a:int) % StreamNv;
                      var b_hash=(b:int) % StreamNv;
                      if srclocal.contains(Streamcurline) {
                          //if ((curline<StreamNe) || (randv.getNext()>= 1.0/Factor:real) ) {
                              src[Streamcurline]=a_hash;
                              dst[Streamcurline]=b_hash;
                              e_cnt[Streamcurline]+=1;
                          //}
                      }
                      if neilocal.contains(a_hash) {
                          v_cnt[a_hash]+=1;
                      }
                      if neilocal.contains(b_hash) {
                          v_cnt[b_hash]+=1;
                      }
                      curline+=1;
                      Streamcurline=curline%StreamNe;
                  } 
                  forall i in src.localSubdomain() {
                       src[i]=src[i]+(src[i]==dst[i]);
                       src[i]=src[i]%StreamNv;
                       dst[i]=dst[i]%StreamNv;
                  }
               }// end on loc
           }//end coforall
      }//end readLinebyLine
      
      readLinebyLine();
      //start_i=-1;
      //start_iR=-1;
      timer.stop();
      //writeln("$$$$$$$$$$$$ Reading File takes ", timer.elapsed()," $$$$$$$$$$$$$$$$$$$$$$$");
      timer.start();

      proc combine_sort() throws {
             param bitsPerDigit = RSLSD_bitsPerDigit;
             var bitWidths: [0..1] int;
             var negs: [0..1] bool;
             var totalDigits: int;
             var size=StreamNe: int;
             for (bitWidth, ary, neg) in zip(bitWidths, [src,dst], negs) {
                       (bitWidth, neg) = getBitWidth(ary); 
                       totalDigits += (bitWidth + (bitsPerDigit-1)) / bitsPerDigit;
             }
             proc mergedArgsort(param numDigits) throws {
                    //overMemLimit(((4 + 3) * size * (numDigits * bitsPerDigit / 8))
                    //             + (2 * here.maxTaskPar * numLocales * 2**16 * 8));
                    var merged = makeDistArray(size, numDigits*uint(bitsPerDigit));
                    var curDigit = numDigits - totalDigits;
                    for (ary , nBits, neg) in zip([src,dst], bitWidths, negs) {
                        proc mergeArray(type t) {
                            ref A = ary;
                            const r = 0..#nBits by bitsPerDigit;
                            for rshift in r {
                                 const myDigit = (r.high - rshift) / bitsPerDigit;
                                 const last = myDigit == 0;
                                 forall (m, a) in zip(merged, A) {
                                     m[curDigit+myDigit] =  getDigit(a, rshift, last, neg):uint(bitsPerDigit);
                                 }
                            }
                            curDigit += r.size;
                        }
                        mergeArray(int); 
                    }
                    var tmpiv = argsortDefault(merged);
                    return tmpiv;
             }

             try {
                 if totalDigits <=  4 { 
                      iv = mergedArgsort( 4); 
                 }
                 if (totalDigits >  4) && ( totalDigits <=  8) { 
                      iv =  mergedArgsort( 8); 
                 }
                 if (totalDigits >  8) && ( totalDigits <=  16) { 
                      iv = mergedArgsort(16); 
                 }
                 if (totalDigits >  16) && ( totalDigits <=  32) { 
                      iv = mergedArgsort(32); 
                 }
                 if (totalDigits >32) {    
                      return "Error, TotalDigits >32";
                 }

             } catch e: Error {
                  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      e.message());
                    return "Error: %t".format(e.message());
             }
             var tmpedges=src[iv];
             src=tmpedges;
             tmpedges=dst[iv];
             dst=tmpedges;
             tmpedges=e_cnt[iv];
             e_cnt=tmpedges;

             return "success";
      }//end combine_sort

      proc set_neighbour(){ 
          coforall loc in Locales  {
              on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=neighbour;
                       ref sf=start_i;
                       var ld=srcf.localSubdomain();
                       // first we divide vertices based on the number of edges
                       var startVer=srcf[ld.low];
                       var endVer=srcf[ld.high];

                       StartVerAry[here.id]=startVer;
                       EndVerAry[here.id]=endVer;
                       var startEdge=ld.low;
                       var endEdge=ld.high;

                       forall i in startEdge..endEdge {
                          var srci=src[i];
                          if ((srci>=startVer) && (srci<=endVer)) {
                              neighbour[srci]+=1;
                             
                          } else {
                              var tmpn:int;
                              var tmpstart:int;
                              var aggs= newSrcAggregator(int);
                              aggs.copy(tmpn,neighbour[srci]);
                              aggs.flush();
                              tmpn+=1;
                              var aggd= newDstAggregator(int);
                              aggd.copy(neighbour[srci],tmpn);
                              aggd.flush();
                          }

                       }

              }
          }
          for i in 0..StreamNe-1 do {
             if (start_i[src[i]] ==-1){
                 start_i[src[i]]=i;
             }
          }
      }

      combine_sort();
      set_neighbour();

      if (directed==false) { //undirected graph

          proc combine_sortR() throws {
             /* we cannot use the coargsort version because it will break the memory limit */
             param bitsPerDigit = RSLSD_bitsPerDigit;
             var bitWidths: [0..1] int;
             var negs: [0..1] bool;
             var totalDigits: int;
             var size=StreamNe: int;
             for (bitWidth, ary, neg) in zip(bitWidths, [srcR,dstR], negs) {
                 (bitWidth, neg) = getBitWidth(ary); 
                 totalDigits += (bitWidth + (bitsPerDigit-1)) / bitsPerDigit;

             }
             proc mergedArgsort(param numDigits) throws {
               //overMemLimit(((4 + 3) * size * (numDigits * bitsPerDigit / 8))
               //          + (2 * here.maxTaskPar * numLocales * 2**16 * 8));
               var merged = makeDistArray(size, numDigits*uint(bitsPerDigit));
               var curDigit = numDigits - totalDigits;
               for (ary , nBits, neg) in zip([srcR,dstR], bitWidths, negs) {
                  proc mergeArray(type t) {
                     ref A = ary;
                     const r = 0..#nBits by bitsPerDigit;
                     for rshift in r {
                        const myDigit = (r.high - rshift) / bitsPerDigit;
                        const last = myDigit == 0;
                        forall (m, a) in zip(merged, A) {
                             m[curDigit+myDigit] =  getDigit(a, rshift, last, neg):uint(bitsPerDigit);
                        }
                     }
                     curDigit += r.size;
                  }
                  mergeArray(int); 
               }
               var tmpiv = argsortDefault(merged);
               return tmpiv;
             } 

             try {
                 if totalDigits <=  4 { 
                      ivR = mergedArgsort( 4); 
                 }
                 if (totalDigits >  4) && ( totalDigits <=  8) { 
                      ivR =  mergedArgsort( 8); 
                 }
                 if (totalDigits >  8) && ( totalDigits <=  16) { 
                      ivR = mergedArgsort(16); 
                 }
                 if (totalDigits >  16) && ( totalDigits <=  32) { 
                      ivR = mergedArgsort(32); 
                 }
             } catch e: Error {
                  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      e.message());
                    return "Error: %t".format(e.message());
             }

             var tmpedges = srcR[ivR]; 
             srcR=tmpedges;
             tmpedges = dstR[ivR]; 
             dstR=tmpedges;
             return "success";

          }// end combine_sortR


          proc set_neighbourR(){ 
              coforall loc in Locales  {
                  on loc {
                       ref srcfR=srcR;
                       ref nfR=neighbourR;
                       ref sfR=start_iR;
                       var ldR=srcfR.localSubdomain();
                       // first we divide vertices based on the number of edges
                       var startVer=srcfR[ldR.low];
                       var endVer=srcfR[ldR.high];

                       var startEdge=ldR.low;
                       var endEdge=ldR.high;

                       forall i in startEdge..endEdge {
                          var srci=srcR[i];
                          if ((srci>=startVer) && (srci<=endVer)) {
                              neighbourR[srci]+=1;
                             
                          } else {
                              var tmpn:int;
                              var tmpstart:int;
                              var aggs= newSrcAggregator(int);
                              aggs.copy(tmpn,neighbourR[srci]);
                              aggs.flush();
                              tmpn+=1;
                              var aggd= newSrcAggregator(int);
                              aggd.copy(neighbourR[srci],tmpn);
                              aggd.flush();
                          }

                       }

                  }//on loc
              }//coforall
              for i in 0..StreamNe-1 do {
                 if (start_iR[srcR[i]] ==-1){
                     start_iR[srcR[i]]=i;
                 }
              }
          }


          coforall loc in Locales  {
              on loc {
                  forall i in srcR.localSubdomain(){
                        srcR[i]=dst[i];
                        dstR[i]=src[i];
                   }
              }
          }
          combine_sortR();
          set_neighbourR();

      }//end of undirected

      timer.stop();
      //writeln("$$$$$$$$$$$$Sorting Edges takes ", timer.elapsed()," $$$$$$$$$$$$$$$$$$$$$$$");



      timer.start();

      coforall loc in Locales  {
              on loc {
                  forall i in neighbour.localSubdomain(){
                      if ( v_cnt[i]<=1 ) {
                          neighbour[i]=0;
                          neighbourR[i]=0;
                      }
                  }
              }
      }

      proc stream_tri_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{
          var number_edge=0:int;
          var sum_ratio1=0.0:real;
          var sum_ratio2=0.0:real;
          coforall loc in Locales with (+ reduce number_edge, + reduce sum_ratio1,+reduce sum_ratio2)  {
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
                       var startVer=srcf[ld.low];
                       var endVer=srcf[ld.high];

                       StartVerAry[here.id]=startVer;
                       EndVerAry[here.id]=endVer;
                       var startEdge=ld.low;
                       var endEdge=ld.high;

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
                       forall u in startVer..endVer with (+ reduce triCount,+ reduce remoteCnt, + reduce localCnt,+ reduce number_edge, + reduce sum_ratio1,+reduce sum_ratio2) {// for all the u
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
                               if (startu_adj>=ld.low && endu_adj<=ld.high) {
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
                               if (startuR_adj>=ldR.low && enduR_adj<=ldR.high) {
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

                           forall v in uadj with (+reduce triCount,ref uadj,+ reduce remoteCnt, + reduce localCnt,+ reduce number_edge, + reduce sum_ratio1,+reduce sum_ratio2) {
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
                                   if (startv_adj>=ld.low && endv_adj<=ld.high) {
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
                                   if (startvR_adj>=ldR.low && endvR_adj<=ldR.high) {
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
                               var localtricnt=0:int;
                               forall i in vadj with (+ reduce triCount,+reduce localtricnt) {
                                   if uadj.contains(i) {
                                      triCount+=1;
                                      localtricnt+=1;
                                   }
                               }
                               if (localtricnt>0) {
                                   number_edge+=1;
                                   sum_ratio1+=(v_cnt[u]-neighbour[u]-neighbourR[u]+v_cnt[v]-neighbour[v]-neighbourR[v])/localtricnt:real;
                                   sum_ratio2+=(v_cnt[u]+v_cnt[v]):real/(neighbour[u]+neighbourR[u]+neighbour[v]+neighbourR[v]):real;
                                   //writeln("3333 Locale=",here.id, " tri=", localtricnt," u=",u, " v=",v, " u_cnt=", v_cnt[u], " v_cnt=", v_cnt[v], " ratio=", (v_cnt[u]-neighbour[u]-neighbourR[u]+v_cnt[v]-neighbour[v]-neighbourR[v])/localtricnt:real);
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
          var averageratio1=sum_ratio1/number_edge/2;
          var averageratio2=sum_ratio2/number_edge;
          //writeln("Average ratio1=", averageratio1, " Total number of edges=",number_edge);
          //writeln("Average ratio2=", averageratio2, " Total number of edges=",number_edge);
          var totaltri=0;
          for i in subTriSum {
             totaltri+=i;
          }
          //writeln("Estimated triangles 1=",totaltri*Factor*max(1,averageratio1**(0.02)));
          //writeln("Estimated triangles 2=",totaltri*Factor*max(1,averageratio2**(0.1)));
          //writeln("Estimated triangles 3=",totaltri*Factor*max(1,averageratio2**(0.05)));
          //writeln("Estimated triangles 4=",totaltri*Factor*max(1,averageratio2**(0.01)));
          return "success";
      }//end of stream_tri_kernel_u


      proc return_stream_tri_count(): string throws{
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
          //TotalCnt[0]/=3;
          //writeln("TriangleNumber=", TotalCnt[0]);
          //writeln("LocalRatio=", (totalLocal:real)/((totalRemote+totalLocal):real),", TotalTimes=",totalRemote+totalLocal);
          //writeln("LocalAccessTimes=", totalLocal,", RemoteAccessTimes=",totalRemote);
          var countName = st.nextName();
          var countEntry = new shared SymEntry(TotalCnt);
          st.addEntry(countName, countEntry);

          var cntMsg =  'created ' + st.attrib(countName);
          return cntMsg;

      }//end of proc return_stream


      stream_tri_kernel_u(neighbour, start_i,src,dst,
                           neighbourR, start_iR,srcR,dstR);
      repMsg=return_stream_tri_count();
      
      timer.stop();
      //writeln("$$$$$$$$$$$$ Streaming Triangle Counting time= ", timer.elapsed()," $$$$$$$$$$$$$$$$$$$$$$$");
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);

  }






// directly read a stream from given file and build the Graph class in memory
  proc segStreamPLTriCntMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS, FileName,FactorS, CaseS) = payload.splitMsgToTuple(7);
      //writeln("======================Graph Reading=====================");
      //writeln(NeS,NvS,ColS,DirectedS, FileName);
      var Ne=NeS:int;
      var Nv=NvS:int;
      var Factor=FactorS:int;
      var NumSketch=3:int;// head, middle, and tail three parts as different sketchs
      var StreamNe=Ne/(Factor*NumSketch):int;
      var StreamNv=Nv/(Factor*NumSketch):int;
      var CaseNum=CaseS:int;
      var NumCol=ColS:int;
      var directed=DirectedS:int;
      var weighted=0:int;
      var timer: Timer;
      if NumCol>2 {
           weighted=1;
      }
      //writeln("StreamNe=",StreamNe, " StreameNv=",StreamNv);

      timer.start();
      var src=makeDistArray(StreamNe,int);
      var dst=makeDistArray(StreamNe,int);
      var neighbour=makeDistArray(StreamNv,int);
      var start_i=makeDistArray(StreamNv,int);
      var e_weight = makeDistArray(StreamNe,int);
      var e_cnt = makeDistArray(StreamNe,int);
      var v_weight = makeDistArray(StreamNv,int);
      var v_cnt = makeDistArray(StreamNv,int);
      var iv=makeDistArray(StreamNe,int);

      var src1=makeDistArray(StreamNe,int);
      var dst1=makeDistArray(StreamNe,int);
      var neighbour1=makeDistArray(StreamNv,int);
      var start_i1=makeDistArray(StreamNv,int);
      var e_weight1 = makeDistArray(StreamNe,int);
      var e_cnt1 = makeDistArray(StreamNe,int);
      var v_weight1 = makeDistArray(StreamNv,int);
      var v_cnt1 = makeDistArray(StreamNv,int);
      var iv1=makeDistArray(StreamNe,int);
      var srcR1=makeDistArray(StreamNe,int);
      var dstR1=makeDistArray(StreamNe,int);
      var neighbourR1=makeDistArray(StreamNv,int);
      var start_iR1=makeDistArray(StreamNv,int);
      ref  ivR1=iv1;
      ref  iv2=iv1;
      ref  ivR2=iv1;
      ref  iv3=iv1;
      ref  ivR3=iv1;



      var src2=makeDistArray(StreamNe,int);
      var dst2=makeDistArray(StreamNe,int);
      var neighbour2=makeDistArray(StreamNv,int);
      var start_i2=makeDistArray(StreamNv,int);
      var e_weight2 = makeDistArray(StreamNe,int);
      var e_cnt2 = makeDistArray(StreamNe,int);
      var v_weight2 = makeDistArray(StreamNv,int);
      var v_cnt2 = makeDistArray(StreamNv,int);
      //var iv2=makeDistArray(StreamNe,int);
      var srcR2=makeDistArray(StreamNe,int);
      var dstR2=makeDistArray(StreamNe,int);
      var neighbourR2=makeDistArray(StreamNv,int);
      var start_iR2=makeDistArray(StreamNv,int);
      //ref  ivR2=iv2;


      var src3=makeDistArray(StreamNe,int);
      var dst3=makeDistArray(StreamNe,int);
      var neighbour3=makeDistArray(StreamNv,int);
      var start_i3=makeDistArray(StreamNv,int);
      var e_weight3 = makeDistArray(StreamNe,int);
      var e_cnt3 = makeDistArray(StreamNe,int);
      var v_weight3 = makeDistArray(StreamNv,int);
      var v_cnt3 = makeDistArray(StreamNv,int);
      //var iv3=makeDistArray(StreamNe,int);
      var srcR3=makeDistArray(StreamNe,int);
      var dstR3=makeDistArray(StreamNe,int);
      var neighbourR3=makeDistArray(StreamNv,int);
      var start_iR3=makeDistArray(StreamNv,int);
      //ref  ivR3=iv3;

      var linenum=0:int;
      var repMsg: string;
      var sort_flag:int;
      var filesize:int;

      var TotalCnt:[0..0] int;
      var subTriSum1: [0..numLocales-1] int;
      var StartVerAry1: [0..numLocales-1] int;
      var EndVerAry1: [0..numLocales-1] int;
      var RemoteAccessTimes1: [0..numLocales-1] int;
      var LocalAccessTimes1: [0..numLocales-1] int;

      TotalCnt=0;
      subTriSum1=0;
      StartVerAry1=-1;
      EndVerAry1=-1;
      RemoteAccessTimes1=0;
      LocalAccessTimes1=0;

      //var TotalCnt2=0:[0..0] int;
      var subTriSum2: [0..numLocales-1] int;
      var StartVerAry2: [0..numLocales-1] int;
      var EndVerAry2: [0..numLocales-1] int;
      var RemoteAccessTimes2: [0..numLocales-1] int;
      var LocalAccessTimes2: [0..numLocales-1] int;
      subTriSum2=0;
      StartVerAry2=-1;
      EndVerAry2=-1;
      RemoteAccessTimes2=0;
      LocalAccessTimes2=0;

      //var TotalCnt3=0:[0..0] int;
      var subTriSum3: [0..numLocales-1] int;
      var StartVerAry3: [0..numLocales-1] int;
      var EndVerAry3: [0..numLocales-1] int;
      var RemoteAccessTimes3: [0..numLocales-1] int;
      var LocalAccessTimes3: [0..numLocales-1] int;
      subTriSum3=0;
      StartVerAry3=-1;
      EndVerAry3=-1;
      RemoteAccessTimes3=0;
      LocalAccessTimes3=0;

      proc readLinebyLine() throws {
           coforall loc in Locales  {
              on loc {
                  var f = open(FileName, iomode.r);
                  var r = f.reader(kind=ionative);
                  defer {
                        closeFinally(r);
                        closeFinally(f);
                  }

                  var line:string;
                  var a,b,c:string;
                  var curline=0:int;
                  var Streamcurline=0:int;
                  var edgedomain=src1.localSubdomain();
                  var nodedomain=neighbour1.localSubdomain();
                  //writeln("Locale ID=",here.id," edge local domain=", edgedomain, " node local domain=",nodedomain);
                  proc initvalue(ref ary:[?D1] int,intvalue:int) {
                      //writeln("Locale ID=",here.id, " sub domain=", ary.localSubdomain());
                      forall i in ary.localSubdomain() {
                         ary[i]=intvalue;
                      }
                  }
                  initvalue(src1,-1);
                  initvalue(dst1,-1);
                  initvalue(srcR1,-1);
                  initvalue(dstR1,-1);
                  initvalue(e_weight1,0);
                  initvalue(e_cnt1,0);

                  initvalue(src2,-1);
                  initvalue(dst2,-1);
                  initvalue(srcR2,-1);
                  initvalue(dstR2,-1);
                  initvalue(e_weight2,0);
                  initvalue(e_cnt2,0);

                  initvalue(src3,-1);
                  initvalue(dst3,-1);
                  initvalue(srcR3,-1);
                  initvalue(dstR3,-1);
                  initvalue(e_weight3,0);
                  initvalue(e_cnt3,0);


                  initvalue(neighbour1,0);
                  initvalue(neighbourR1,0);
                  initvalue(v_weight1,0);
                  initvalue(v_cnt1,0);
                  initvalue(start_i1,-1);
                  initvalue(start_iR1,-1);


                  initvalue(neighbour2,0);
                  initvalue(neighbourR2,0);
                  initvalue(v_weight2,0);
                  initvalue(v_cnt2,0);
                  initvalue(start_i2,-1);
                  initvalue(start_iR2,-1);


                  initvalue(neighbour3,0);
                  initvalue(neighbourR3,0);
                  initvalue(v_weight3,0);
                  initvalue(v_cnt3,0);
                  initvalue(start_i3,-1);
                  initvalue(start_iR3,-1);

                  while r.readline(line) {
                      if NumCol==2 {
                           (a,b)=  line.splitMsgToTuple(2);
                      } else {
                           (a,b,c)=  line.splitMsgToTuple(3);
                            //if ewlocal.contains(Streamcurline){
                            //    e_weight[Streamcurline]=c:int;
                            //}
                      }
                      var a_hash=(a:int) % StreamNv;
                      var b_hash=(b:int) % StreamNv;
                      if edgedomain.contains(Streamcurline) {
                          if (curline<(Ne/3):int) {
                              src1[Streamcurline]=a_hash;
                              dst1[Streamcurline]=b_hash;
                          } else {
                              if (curline>=(Ne*2/3):int) {
                                  src3[Streamcurline]=a_hash;
                                  dst3[Streamcurline]=b_hash;
                               } else {
                                  src2[Streamcurline]=a_hash;
                                  dst2[Streamcurline]=b_hash;
                               }
                          }
                      }

                      if nodedomain.contains(a_hash) {
                          if (curline<(Ne/3):int) {
                              v_cnt1[a_hash]+=1;
                          } else {
                              if (curline>(Ne*2/3):int) {
                                 v_cnt3[a_hash]+=1;
                              } else {
                                 v_cnt2[a_hash]+=1;
                              }
                          }
                      }
                      if nodedomain.contains(b_hash) {
                          if (curline<(Ne/3):int) {
                              v_cnt1[b_hash]+=1;
                          } else {
                              if (curline>(Ne*2/3):int) {
                                 v_cnt3[b_hash]+=1;
                              } else {
                                 v_cnt2[b_hash]+=1;
                              }
                          }
                      }

                      curline+=1;
                      Streamcurline=curline%StreamNe;
                  }
 
                  forall i in edgedomain {
                       src1[i]=src1[i]+(src1[i]==dst1[i]);
                       src1[i]=src1[i]%StreamNv;
                       dst1[i]=dst1[i]%StreamNv;

                       src2[i]=src2[i]+(src2[i]==dst2[i]);
                       src2[i]=src2[i]%StreamNv;
                       dst2[i]=dst2[i]%StreamNv;


                       src3[i]=src3[i]+(src3[i]==dst3[i]);
                       src3[i]=src3[i]%StreamNv;
                       dst3[i]=dst3[i]%StreamNv;
                  }
               }// end on loc
           }//end coforall
      }//end readLinebyLine
      
      readLinebyLine();
      timer.stop();
      writeln("$$$$$$$$$$$$  $$$$$$$$$$$$$$$$$$$$$$$");
      writeln("$$$$$$$$$$$$  $$$$$$$$$$$$$$$$$$$$$$$");
      writeln("$$$$$$$$$$$$ Reading File takes ", timer.elapsed()," $$$$$$$$$$$$$$$$$$$$$$$");
      writeln("$$$$$$$$$$$$  $$$$$$$$$$$$$$$$$$$$$$$");
      writeln("$$$$$$$$$$$$  $$$$$$$$$$$$$$$$$$$$$$$");
      timer.start();
      //writeln("src1=",src1," dst1=",dst1);
      //writeln("neighbour1=",neighbour1," start_i1=",start_i1);
      //writeln("v_cnt1=",v_cnt1 );

      //writeln("src2=",src2," dst2=",dst2);
      //writeln("neighbour2=",neighbour2," start_i2=",start_i2);
      //writeln("v_cnt2=",v_cnt2 );

      //writeln("src3=",src3," dst3=",dst3);
      //writeln("neighbour3=",neighbour3," start_i3=",start_i3);
      //writeln("v_cnt3=",v_cnt3 );

  
      //proc combine_sort(ref src:[?D1] int, ref dst:[?D2] int, ref iv:[?D3] int) throws {
      proc combine_sort() throws {
             param bitsPerDigit = RSLSD_bitsPerDigit;
             var bitWidths: [0..1] int;
             var negs: [0..1] bool;
             var totalDigits=0: int;
             var size=StreamNe: int;
             for (bitWidth, ary, neg) in zip(bitWidths, [src,dst], negs) {
                       (bitWidth, neg) = getBitWidth(ary); 
                       //writeln("bitWidth=",bitWidth," neg=",neg);
                       totalDigits += (bitWidth + (bitsPerDigit-1)) / bitsPerDigit;
             }
             //writeln("total digits=",totalDigits);
             proc mergedArgsort(param numDigits) throws {
                    //overMemLimit(((4 + 3) * size * (numDigits * bitsPerDigit / 8))
                    //             + (2 * here.maxTaskPar * numLocales * 2**16 * 8));
                    var merged = makeDistArray(size, numDigits*uint(bitsPerDigit));
                    var curDigit = numDigits - totalDigits;
                    //writeln("curDigit=",curDigit);
                    for (ary , nBits, neg) in zip([src,dst], bitWidths, negs) {
                        proc mergeArray(type t) {
                            ref A = ary;
                            const r = 0..#nBits by bitsPerDigit;
                            for rshift in r {
                                 const myDigit = (r.high - rshift) / bitsPerDigit;
                                 const last = myDigit == 0;
                                 forall (m, a) in zip(merged, A) {
                                     //writeln("merged element=",m," a=",a);
                                     //writeln("curDigit=", curDigit, " myDigit=", myDigit);
                                     m[curDigit+myDigit] =  getDigit(a, rshift, last, neg):uint(bitsPerDigit);
                                     //writeln("m[curDigit+myDigit] =",m[curDigit+myDigit] );
                                 }
                            }
                            curDigit += r.size;
                            //writeln("curDigit=",curDigit, " r.size=",r.size);
                        }
                        mergeArray(int); 
                    }
                    //writeln("after merge=",merged);
                    //var tmpiv = argsortDefault(merged);
                    //writeln("after sort iv=",tmpiv);
                    return  argsortDefault(merged);
                    //return tmpiv;
             }

             if totalDigits ==  2 { 
                      //writeln("Before merged sort");
                      iv = mergedArgsort( 2); 
                      //writeln("after merged sort");
             }

             //writeln("before assign src to tmpedges");
             //writeln("src=",src);
             //writeln("iv=",iv);
             //writeln("src[iv]=",src[iv]);
             var tmpedges=src[iv];
             src=tmpedges;
             //writeln("after assign src to tmpedges");
             tmpedges=dst[iv];
             dst=tmpedges;
             //writeln("after assign dst to tmpedges");

      }//end combine_sort

      //proc set_neighbour(ref src:[?D1] int,ref  dst:[?D2] int,ref  neighbour:[?D3] int,ref start_i:[?D4] int) {
      proc set_neighbour() {
          coforall loc in Locales  {
              on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=neighbour;
                       ref sf=start_i;
                       var ld=src.localSubdomain();
                       // first we divide vertices based on the number of edges
                       var startVer=srcf[ld.low];
                       var endVer=srcf[ld.high];
                       var startEdge=ld.low;
                       var endEdge=ld.high;

                       forall i in startEdge..endEdge {
                          var srci=src[i];
                          if ((srci>=startVer) && (srci<=endVer)) {
                              neighbour[srci]+=1;
                          } else {
                              var tmpn:int;
                              var tmpstart:int;
                              var aggs= newSrcAggregator(int);
                              aggs.copy(tmpn,neighbour[srci]);
                              aggs.flush();
                              tmpn+=1;
                              var aggd= newDstAggregator(int);
                              aggd.copy(neighbour[srci],tmpn);
                              aggd.flush();
                          }
                       }
              }
          }
          for i in 0..StreamNe-1 do {
             if (start_i[src[i]] ==-1){
                 start_i[src[i]]=i;
             }
          }
      }
      proc sameshape_array_assignment(A:[?D1],B:[?D2]) {
          coforall loc in Locales  {
              on loc {
                  forall i in A.localSubdomain(){
                       A[i]=B[i];
                  }
              }
          }
      }

      sameshape_array_assignment(src,src1);
      sameshape_array_assignment(dst,dst1);
      combine_sort();
      sameshape_array_assignment(neighbour,neighbour1);
      sameshape_array_assignment(start_i,start_i1);
      set_neighbour();
      sameshape_array_assignment(src1,src);
      sameshape_array_assignment(dst1,dst);
      sameshape_array_assignment(neighbour1,neighbour);
      sameshape_array_assignment(start_i1,start_i);


      sameshape_array_assignment(src,src2);
      sameshape_array_assignment(dst,dst2);
      combine_sort();
      sameshape_array_assignment(neighbour,neighbour2);
      sameshape_array_assignment(start_i,start_i2);
      set_neighbour();
      sameshape_array_assignment(src2,src);
      sameshape_array_assignment(dst2,dst);
      sameshape_array_assignment(neighbour2,neighbour);
      sameshape_array_assignment(start_i2,start_i);

      sameshape_array_assignment(src,src3);
      sameshape_array_assignment(dst,dst3);
      combine_sort();
      sameshape_array_assignment(neighbour,neighbour3);
      sameshape_array_assignment(start_i,start_i3);
      set_neighbour();
      sameshape_array_assignment(src3,src);
      sameshape_array_assignment(dst3,dst);
      sameshape_array_assignment(neighbour3,neighbour);
      sameshape_array_assignment(start_i3,start_i);



      sameshape_array_assignment(srcR1,dst1);
      sameshape_array_assignment(dstR1,src1);
      sameshape_array_assignment(srcR2,dst2);
      sameshape_array_assignment(dstR2,src2);
      sameshape_array_assignment(srcR3,dst3);
      sameshape_array_assignment(dstR3,src3);




      sameshape_array_assignment(src,srcR1);
      sameshape_array_assignment(dst,dstR1);
      combine_sort();
      sameshape_array_assignment(neighbour,neighbourR1);
      sameshape_array_assignment(start_i,start_iR1);
      set_neighbour();
      sameshape_array_assignment(srcR1,src);
      sameshape_array_assignment(dstR1,dst);
      sameshape_array_assignment(neighbourR1,neighbour);
      sameshape_array_assignment(start_iR1,start_i);


      sameshape_array_assignment(src,srcR2);
      sameshape_array_assignment(dst,dstR2);
      combine_sort();
      sameshape_array_assignment(neighbour,neighbourR2);
      sameshape_array_assignment(start_i,start_iR2);
      set_neighbour();
      sameshape_array_assignment(srcR2,src);
      sameshape_array_assignment(dstR2,dst);
      sameshape_array_assignment(neighbourR2,neighbour);
      sameshape_array_assignment(start_iR2,start_i);

      sameshape_array_assignment(src,srcR3);
      sameshape_array_assignment(dst,dstR3);
      combine_sort();
      sameshape_array_assignment(neighbour,neighbourR3);
      sameshape_array_assignment(start_i,start_iR3);
      set_neighbour();
      sameshape_array_assignment(srcR3,src);
      sameshape_array_assignment(dstR3,dst);
      sameshape_array_assignment(neighbourR3,neighbour);
      sameshape_array_assignment(start_iR3,start_i);


      timer.stop();
      //writeln("$$$$$$$$$$$$  Sorting Edges takes ", timer.elapsed()," $$$$$$$$$$$$$$$$$$$$$$$");



      timer.start();

      coforall loc in Locales  {
              on loc {
                  forall i in neighbour1.localSubdomain(){
                      if ( v_cnt1[i]<=1 ) {
                          neighbour1[i]=0;
                          neighbourR1[i]=0;
                      }
                      if ( v_cnt2[i]<=1 ) {
                          neighbour2[i]=0;
                          neighbourR2[i]=0;
                      }
                      if ( v_cnt3[i]<=1 ) {
                          neighbour3[i]=0;
                          neighbourR3[i]=0;
                      }
                  }
              }
      }

      proc stream_tri_kernel_u(neighbour:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neighbourR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                        StartVerAry:[?D5] int, EndVerAry:[?D6] int,subTriSum:[?D7] int,
                        RemoteAccessTimes:[?D8] int,LocalAccessTimes:[?D9] int,v_cnt:[?D10] int  ):int throws{

          var number_edge=0:int;
          var sum_ratio1=0.0:real;
          var sum_ratio2=0.0:real;
          coforall loc in Locales with (+ reduce number_edge, + reduce sum_ratio1,+reduce sum_ratio2)  {
                   on loc {
                       var triCount=0:int;
                       var remoteCnt=0:int;
                       var localCnt=0:int;
                       ref srcf=src;
                       ref df=dst;
                       ref nf=neighbour;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neighbourR;
                       ref sfR=start_iR;

                       var ld=srcf.localSubdomain();
                       var ldR=srcfR.localSubdomain();

                       // first we divide vertices based on the number of edges
                       var startVer=srcf[ld.low];
                       var endVer=srcf[ld.high];

                       StartVerAry[here.id]=startVer;
                       EndVerAry[here.id]=endVer;
                       var startEdge=ld.low;
                       var endEdge=ld.high;

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
                             endVer=neighbour.size-1;
                       }
                       if (here.id ==0 ) {
                          startVer=0;
                       }

                       //writeln("3 Locale=",here.id, " Updated Starting/End Vertex=[",startVer, ",", endVer, "], StarAry=", StartVerAry, " EndAry=", EndVerAry);
                       forall u in startVer..endVer with (+ reduce triCount,+ reduce remoteCnt, + reduce localCnt,+ reduce number_edge, + reduce sum_ratio1,+reduce sum_ratio2) {// for all the u
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
                               if (startu_adj>=ld.low && endu_adj<=ld.high) {
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
                               if (startuR_adj>=ldR.low && enduR_adj<=ldR.high) {
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

                           forall v in uadj with (+reduce triCount,ref uadj,+ reduce remoteCnt, + reduce localCnt,+ reduce number_edge, + reduce sum_ratio1,+reduce sum_ratio2) {
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
                                   if (startv_adj>=ld.low && endv_adj<=ld.high) {
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
                                   if (startvR_adj>=ldR.low && endvR_adj<=ldR.high) {
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
                               var localtricnt=0:int;
                               forall i in vadj with (+ reduce triCount,+reduce localtricnt) {
                                   if uadj.contains(i) {
                                      triCount+=1;
                                      localtricnt+=1;
                                   }
                               }
                               if (localtricnt>0) {
                                   number_edge+=1;
                                   sum_ratio1+=(v_cnt[u]-neighbour[u]-neighbourR[u]+v_cnt[v]-neighbour[v]-neighbourR[v])/localtricnt:real;
                                   sum_ratio2+=(v_cnt[u]+v_cnt[v]):real/(neighbour[u]+neighbourR[u]+neighbour[v]+neighbourR[v]):real;
                                   //writeln("3333 Locale=",here.id, " tri=", localtricnt," u=",u, " v=",v, " u_cnt=", v_cnt[u], " v_cnt=", v_cnt[v], " ratio=", (v_cnt[u]-neighbour[u]-neighbourR[u]+v_cnt[v]-neighbour[v]-neighbourR[v])/localtricnt:real);
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
          
          var averageratio1:real;
          var averageratio2:real;
          if (number_edge>0) {
              averageratio1=sum_ratio1/number_edge/2:real;
              averageratio2=sum_ratio2/number_edge:real;
          }
          writeln("Average ratio1=", averageratio1, " Total number of edges=",number_edge);
          writeln("Average ratio2=", averageratio2, " Total number of edges=",number_edge);
          var totaltri=0:int;
          for i in subTriSum {
             totaltri+=i;
          }
          //writeln("Estimated triangles 1=",totaltri*Factor*max(1,averageratio1**(0.02)));
          //writeln("Estimated triangles 2=",totaltri*Factor*max(1,averageratio2**(0.1)));
          //writeln("Estimated triangles 3=",totaltri*Factor*max(1,averageratio2**(0.05)));
          //writeln("Estimated triangles 4=",totaltri*Factor*max(1,averageratio2**(0.01)));
          return totaltri;
      }//end of stream_tri_kernel_u



      var sum1=stream_tri_kernel_u(neighbour1, start_i1,src1,dst1,
                           neighbourR1, start_iR1,srcR1,dstR1,StartVerAry1,EndVerAry1,
                           subTriSum1, RemoteAccessTimes1,LocalAccessTimes1,v_cnt1);

      var totalRemote=0:int;
      var totalLocal=0:int;
      for i in RemoteAccessTimes1 {
              totalRemote+=i;
      }
      for i in LocalAccessTimes1 {
              totalLocal+=i;
      }
      //writeln("TriangleNumber=", sum1);
      //writeln("LocalRatio=", (totalLocal:real)/((totalRemote+totalLocal):real),", TotalTimes=",totalRemote+totalLocal);
      //writeln("LocalAccessTimes=", totalLocal,", RemoteAccessTimes=",totalRemote);


      var sum2=stream_tri_kernel_u(neighbour2, start_i2,src2,dst2,
                           neighbourR2, start_iR2,srcR2,dstR2,StartVerAry2,EndVerAry2,
                           subTriSum2, RemoteAccessTimes2,LocalAccessTimes2,v_cnt2);


      totalRemote=0;
      totalLocal=0;
      for i in RemoteAccessTimes2 {
              totalRemote+=i;
      }
      for i in LocalAccessTimes2 {
              totalLocal+=i;
      }
      //writeln("TriangleNumber=", sum2);
      //writeln("LocalRatio=", (totalLocal:real)/((totalRemote+totalLocal):real),", TotalTimes=",totalRemote+totalLocal);
      //writeln("LocalAccessTimes=", totalLocal,", RemoteAccessTimes=",totalRemote);

      var sum3=stream_tri_kernel_u(neighbour3, start_i3,src3,dst3,
                           neighbourR3, start_iR3,srcR3,dstR3,StartVerAry3,EndVerAry3,
                           subTriSum3, RemoteAccessTimes3,LocalAccessTimes3,v_cnt3);


      totalRemote=0;
      totalLocal=0;
      for i in RemoteAccessTimes3 {
              totalRemote+=i;
      }
      for i in LocalAccessTimes3 {
              totalLocal+=i;
      }
      //writeln("TriangleNumber=", sum3);
      //writeln("LocalRatio=", (totalLocal:real)/((totalRemote+totalLocal):real),", TotalTimes=",totalRemote+totalLocal);
      //writeln("LocalAccessTimes=", totalLocal,", RemoteAccessTimes=",totalRemote);

      var tmp:[0..2] int;
      tmp[0]=sum1;
      tmp[1]=sum2;
      tmp[2]=sum3;
      sort(tmp);
      select (CaseS) {
          when "0" {
            TotalCnt[0]=((tmp[0]+tmp[1]+tmp[2])*Factor):int; //average
          }
          when "1" {
            TotalCnt[0]=((-7.835*tmp[0]+6.887*tmp[1]+3.961*tmp[2])*Factor):int; //power law regression
          }
          when "2" {
            TotalCnt[0]=((3.697*tmp[0]-2.236*tmp[1]-1.737*tmp[2])*Factor):int; //normal regression
          } 
          otherwise { 
              var errorMsg = "not implemented case ="+ CaseS;      
              smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);  
              return new MsgTuple(errorMsg, MsgType.ERROR);    
          }

      }

      //writeln("Combine three estimates together, triangles=",TotalCnt[0]);
      var countName = st.nextName();
      var countEntry = new shared SymEntry(TotalCnt);
      st.addEntry(countName, countEntry);
      repMsg =  'created ' + st.attrib(countName);

      timer.stop();
      //writeln("$$$$$$$$$$$$ Streaming Triangle Counting time= ", timer.elapsed()," $$$$$$$$$$$$$$$$$$$$$$$");
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);

  }



    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedStreamFile", segStreamFileMsg);
        registerFunction("segmentedGraphTri", segTriCntMsg);
        registerFunction("segmentedStreamTri", segStreamTriCntMsg);
        registerFunction("segmentedPLStreamTri", segStreamPLTriCntMsg);
    }


}


