module GraphMsg {

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
  use GraphArray;


  use List; 
  use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use AryUtil;



  //private config const logLevel = ServerConfig.logLevel;
  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  var outMsg:string;
  



  config const start_min_degree = 1000000;

  private proc xlocal(x :int, low:int, high:int):bool {
      return low<=x && x<=high;
  }

  private proc xremote(x :int, low:int, high:int):bool {
      return !xlocal(x, low, high);
  }


 /*
  * based on the src array, we calculate the start_i and neighbour arrays
  */

  private proc set_neighbour(lsrc:[?D1]int, lstart_i :[?D2] int, lneighbour :[?D3] int ){ 
          var Ne=D1.size;
          forall i in lstart_i {
               i=-1;
          }
          forall i in lneighbour {
               i=0;
          }
          for i in 0..Ne-1 do {
             lneighbour[lsrc[i]]+=1;
             if (lstart_i[lsrc[i]] ==-1){
                 lstart_i[lsrc[i]]=i;
             }
          }
  }

  private proc binSearchV(ary:[?D] int,l:int,h:int,key:int):int {
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
                              return binSearchV(ary,m+1,h,key);
                            }
                            else {
                                    return binSearchV(ary,l,m-1,key);
                            }
                       }
  }// end of proc

  // map vertex ID from a large range to 0..Nv-1
  private proc vertex_remap( lsrc:[?D1] int, ldst:[?D2] int, numV:int) :int throws {

          var numE=lsrc.size;
          var tmpe:[D1] int;
          var VertexMapping:[0..numV-1] int;

          var VertexSet= new set(int,parSafe = true);
          forall (i,j) in zip (lsrc,ldst) with (ref VertexSet) {
                VertexSet.add(i);
                VertexSet.add(j);
          }
          var vertexAry=VertexSet.toArray();
          if vertexAry.size!=numV {
               smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                         "number of vertices is not equal to the given number`");
          }
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                         "Total Vertices="+vertexAry.size:string+" ? Nv="+numV:string);


          sort(vertexAry);
          forall i in 0..numE-1 {
               lsrc[i]=binSearchV(vertexAry,0,vertexAry.size-1,lsrc[i]);
               ldst[i]=binSearchV(vertexAry,0,vertexAry.size-1,ldst[i]);
          }
          return vertexAry.size; 

  }
      /* 
       * we sort the combined array [src dst] here
       */
  private proc combine_sort( lsrc:[?D1] int, ldst:[?D2] int, le_weight:[?D3] int,  lWeightedFlag: bool, sortw=false: bool )   {
             param bitsPerDigit = RSLSD_bitsPerDigit;
             var bitWidths: [0..1] int;
             var negs: [0..1] bool;
             var totalDigits: int;
             var size=D1.size;
             var iv:[D1] int;



             for (bitWidth, ary, neg) in zip(bitWidths, [lsrc,ldst], negs) {
                       (bitWidth, neg) = getBitWidth(ary);
                       totalDigits += (bitWidth + (bitsPerDigit-1)) / bitsPerDigit;
             }
             proc mergedArgsort(param halfDig):[D1] int throws {
                    param numBuckets = 1 << bitsPerDigit; // these need to be const for comms/performance reasons
                    param maskDigit = numBuckets-1;
                    var merged = makeDistArray(size, halfDig*2*uint(bitsPerDigit));
                    for jj in 0..size-1 {
                    //for (m,s,d ) in zip(merged, lsrc,ldst) {
                          forall i in 0..halfDig-1 {
                              // here we assume the vertex ID>=0
                              //m[i]=(  ((s:uint) >> ((halfDig-i-1)*bitsPerDigit)) & (maskDigit:uint) ):uint(bitsPerDigit);
                              //m[i+halfDig]=( ((d:uint) >> ((halfDig-i-1)*bitsPerDigit)) & (maskDigit:uint) ):uint(bitsPerDigit);
                              merged[jj][i]=(  ((lsrc[jj]:uint) >> ((halfDig-i-1)*bitsPerDigit)) & (maskDigit:uint) ):uint(bitsPerDigit);
                              merged[jj][i+halfDig]=( ((ldst[jj]:uint) >> ((halfDig-i-1)*bitsPerDigit)) & (maskDigit:uint) ):uint(bitsPerDigit);
                          }
                          //    writeln("[src[",jj,"],dst[",jj,"]=",lsrc[jj],",",ldst[jj]);
                          //    writeln("merged[",jj,"]=",merged[jj]);
                    }
                    var tmpiv = argsortDefault(merged);
                    return tmpiv;
             }

             try {
                      iv = mergedArgsort(2);

             } catch  {
                  try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "merge array error" );
             }

             var tmpedges=lsrc[iv];
             lsrc=tmpedges;
             tmpedges=ldst[iv];
             ldst=tmpedges;
             //if (lWeightedFlag && sortw ){
             //   tmpedges=le_weight[iv];
             //   le_weight=tmpedges;
             //}

  }//end combine_sort

  /*
   * here we preprocess the graph using reverse Cuthill.McKee algorithm to improve the locality.
   * the basic idea of RCM is relabeling the vertex based on their BFS visiting order
   */
  private proc RCM( lsrc:[?D1] int, ldst:[?D2] int, lstart_i:[?D3] int, lneighbour:[?D4] int, ldepth:[?D5] int,le_weight:[?D6] int,lWeightedFlag :bool )  {
          var Ne=D1.size;
          var Nv=D3.size;            
          var cmary: [0..Nv-1] int;
          // visiting order vertex array
          var indexary:[0..Nv-1] int;
          var iv:[D1] int;
          ldepth=-1;
          proc smallVertex() :int {
                var minindex:int;
                var tmpmindegree:int=9999999;
                for i in 0..Nv-1 {
                   if (lneighbour[i]<tmpmindegree) && (lneighbour[i]>0) {
                      //here we did not consider the reverse neighbours
                      tmpmindegree=lneighbour[i];
                      minindex=i;
                   }
                }
                return minindex;
          }

          var currentindex=0:int;
          var x=smallVertex();
          cmary[0]=x;
          ldepth[x]=0;

          var SetCurF= new set(int,parSafe = true);//use set to keep the current frontier
          var SetNextF=new set(int,parSafe = true);//use set to keep the next fromtier
          SetCurF.add(x);
          var numCurF=1:int;
          var GivenRatio=0.021:real;
          var topdown=0:int;
          var bottomup=0:int;
          var LF=1:int;
          var cur_level=0:int;
          
          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                //topdown, bottomup are reduce variables
                   on loc {
                       ref srcf=lsrc;
                       ref df=ldst;
                       ref nf=lneighbour;
                       ref sf=lstart_i;

                       var edgeBegin=lsrc.localSubdomain().low;
                       var edgeEnd=lsrc.localSubdomain().high;
                       var vertexBegin=lsrc[edgeBegin];
                       var vertexEnd=lsrc[edgeEnd];


                       var switchratio=(numCurF:real)/nf.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (ldepth[j]==-1) {
                                               ldepth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              } 
                           }//end coforall
                       }else {// bottom up
                           bottomup+=1;
                           forall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if ldepth[i]==-1 {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               ldepth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                              }
                           }
                       }
                   }//end on loc
                }//end coforall loc
                cur_level+=1;
                numCurF=SetNextF.size;

                if (numCurF>0) {
                    //var tmpary:[0..numCurF-1] int;
                    var sortary:[0..numCurF-1] int;
                    var numary:[0..numCurF-1] int;
                    var tmpa=0:int;
                    var tmpary=SetNextF.toArray();
                    //forall (a,b)  in zip (tmpary,SetNextF.toArray()) {
                    //    a=b;
                    //}
                    forall i in 0..numCurF-1 {
                         numary[i]=lneighbour[tmpary[i]];
                    }
                    var tmpiv:[0..numCurF-1]int;
                    try {
                        tmpiv =  argsortDefault(numary);
                    } catch {
                        try! smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),"error");
                    }    
                    sortary=tmpary[tmpiv];
                    cmary[currentindex+1..currentindex+numCurF]=sortary;
                    currentindex=currentindex+numCurF;
                }


                SetCurF=SetNextF;
                SetNextF.clear();
          }//end while  

          if (currentindex+1<Nv) {
                 forall i in 0..Nv-1 with (+reduce currentindex) {
                 //unvisited vertices are put to the end of cmary
                     if ldepth[i]==-1 {
                       cmary[currentindex+1]=i;
                       currentindex+=1;  
                     }
                 }
          }
          cmary.reverse();
          forall i in 0..Nv-1{
              indexary[cmary[i]]=i;
          }

          var tmpary:[0..Ne-1] int;
          forall i in 0..Ne-1 {
                  tmpary[i]=indexary[lsrc[i]];
          }
          lsrc=tmpary;
          forall i in 0..Ne-1 {
                  tmpary[i]=indexary[ldst[i]];
          }
          ldst=tmpary;

          try  { combine_sort(lsrc, ldst,le_weight,lWeightedFlag, false);
              } catch {
                  try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
          }
          set_neighbour(lsrc,lstart_i,lneighbour);
  }//end RCM

  // RCM for undirected graph.
  private proc RCM_u( lsrc:[?D1] int, ldst:[?D2] int, lstart_i:[?D3] int, lneighbour:[?D4] int, 
                      lsrcR:[?D5] int, ldstR:[?D6] int, lstart_iR:[?D7] int, lneighbourR:[?D8] int, 
                      ldepth:[?D9] int, le_weight:[?D10] int, lWeightedFlag:bool )  {
              var Ne=D1.size;
              var Nv=D3.size;
              var cmary: [0..Nv-1] int;
              var indexary:[0..Nv-1] int;
              var iv:[D1] int;
              ldepth=-1;
              proc smallVertex() :int {
                    var minindex:int;
                    var tmpmindegree:int=999999;
                    for i in 0..Nv-1 {
                       if (lneighbour[i]+lneighbourR[i]<tmpmindegree) {
                          tmpmindegree=lneighbour[i]+lneighbourR[i];
                          minindex=i;
                       }
                    }
                    return minindex;
              }

              var currentindex=0:int;
              var x=smallVertex();
              cmary[0]=x;
              ldepth[x]=0;

              var SetCurF= new set(int,parSafe = true);//use set to keep the current frontier
              var SetNextF=new set(int,parSafe = true);//use set to keep the next fromtier
              SetCurF.add(x);
              var numCurF=1:int;
              var GivenRatio=0.25:real;
              var topdown=0:int;
              var bottomup=0:int;
              var LF=1:int;
              var cur_level=0:int;
          
         while (numCurF>0) {
                    coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                       on loc {
                           ref srcf=lsrc;
                           ref df=ldst;
                           ref nf=lneighbour;
                           ref sf=lstart_i;

                           ref srcfR=lsrcR;
                           ref dfR=ldstR;
                           ref nfR=lneighbourR;
                           ref sfR=lstart_iR;

                           var edgeBegin=lsrc.localSubdomain().low;
                           var edgeEnd=lsrc.localSubdomain().high;
                           var vertexBegin=lsrc[edgeBegin];
                           var vertexEnd=lsrc[edgeEnd];
                           var vertexBeginR=lsrcR[edgeBegin];
                           var vertexEndR=lsrcR[edgeEnd];

                           var switchratio=(numCurF:real)/nf.size:real;
                           if (switchratio<GivenRatio) {//top down
                               topdown+=1;
                               forall i in SetCurF with (ref SetNextF) {
                                  if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                      var    numNF=nf[i];
                                      var    edgeId=sf[i];
                                      var nextStart=max(edgeId,edgeBegin);
                                      var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                      ref NF=df[nextStart..nextEnd];
                                      forall j in NF with (ref SetNextF){
                                             if (ldepth[j]==-1) {
                                                   ldepth[j]=cur_level+1;
                                                   SetNextF.add(j);
                                             }
                                      }
                                  } 
                                  if ((xlocal(i,vertexBeginR,vertexEndR)) )  {
                                      var    numNF=nfR[i];
                                      var    edgeId=sfR[i];
                                      var nextStart=max(edgeId,edgeBegin);
                                      var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                      ref NF=dfR[nextStart..nextEnd];
                                      forall j in NF with (ref SetNextF)  {
                                             if (ldepth[j]==-1) {
                                                   ldepth[j]=cur_level+1;
                                                   SetNextF.add(j);
                                             }
                                      }
                                  }
                               }//end coforall
                           }else {// bottom up
                               bottomup+=1;
                               forall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                                  if ldepth[i]==-1 {
                                      var    numNF=nf[i];
                                      var    edgeId=sf[i];
                                      var nextStart=max(edgeId,edgeBegin);
                                      var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                      ref NF=df[nextStart..nextEnd];
                                      forall j in NF with (ref SetNextF){
                                             if (SetCurF.contains(j)) {
                                                   ldepth[i]=cur_level+1;
                                                   SetNextF.add(i);
                                             }
                                      }

                                  }
                               }
                               forall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                                  if ldepth[i]==-1 {
                                      var    numNF=nfR[i];
                                      var    edgeId=sfR[i];
                                      var nextStart=max(edgeId,edgeBegin);
                                      var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                      ref NF=dfR[nextStart..nextEnd];
                                      forall j in NF with (ref SetNextF)  {
                                             if (SetCurF.contains(j)) {
                                                   ldepth[i]=cur_level+1;
                                                   SetNextF.add(i);
                                             }
                                      }
                                  }
                               }
                           }
                       }//end on loc
                    }//end coforall loc
                    cur_level+=1;
                    numCurF=SetNextF.size;

                    if (numCurF>0) {
                        var sortary:[0..numCurF-1] int;
                        var numary:[0..numCurF-1] int;
                        var tmpa=0:int;
                        var tmpary=SetNextF.toArray();
                        forall i in 0..numCurF-1 {
                             numary[i]=lneighbour[tmpary[i]]+lneighbourR[tmpary[i]];
                        }
                        var tmpiv:[0..numCurF-1] int;
                        try {
                           tmpiv =  argsortDefault(numary);
                        } catch {
                             try! smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),"error");
                        }    
                        sortary=tmpary[tmpiv];
                        cmary[currentindex+1..currentindex+numCurF]=sortary;
                        currentindex=currentindex+numCurF;
                    }


                    SetCurF=SetNextF;
                    SetNextF.clear();
              }//end while  
              if (currentindex+1<Nv) {
                 forall i in 0..Nv-1 with(+reduce currentindex) {
                 //unvisited vertices are put to the end of cmary
                     if ldepth[i]==-1 {
                       cmary[currentindex+1]=i;
                       currentindex+=1;  
                     }
                 }
              }
              cmary.reverse();
              forall i in 0..Nv-1{
                  indexary[cmary[i]]=i;
              }
    
              var tmpary:[0..Ne-1] int;
              forall i in 0..Ne-1 {
                      tmpary[i]=indexary[lsrc[i]];
              }
              lsrc=tmpary;
              forall i in 0..Ne-1 {
                      tmpary[i]=indexary[ldst[i]];
              }
              ldst=tmpary;
 
        
              try  { combine_sort(lsrc, ldst,le_weight,lWeightedFlag, true);
                  } catch {
                  try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
              }
              set_neighbour(lsrc,lstart_i,lneighbour);
              coforall loc in Locales  {
                  on loc {
                      forall i in lsrcR.localSubdomain(){
                            lsrcR[i]=ldst[i];
                            ldstR[i]=lsrc[i];
                       }
                  }
               }
               try  { combine_sort(lsrcR, ldstR,le_weight,lWeightedFlag, false);
                  } catch {
                  try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
               }
               set_neighbour(lsrcR,lstart_iR,lneighbourR);
               //return true;
  }//end RCM_u



  //sorting the vertices based on their degrees.
  private proc part_degree_sort(lsrc:[?D1] int, ldst:[?D2] int, lstart_i:[?D3] int, lneighbour:[?D4] int,le_weight:[?D5] int,lneighbourR:[?D6] int,lWeightedFlag:bool) {
             var DegreeArray, VertexMapping: [D4] int;
             var tmpedge:[D1] int;
             var Nv=D4.size;
             var iv:[D1] int;

             coforall loc in Locales  {
                on loc {
                  forall i in lneighbour.localSubdomain(){
                        DegreeArray[i]=lneighbour[i]+lneighbourR[i];
                  }
                }
             }
 
             var tmpiv:[D4] int;
             try {
                 tmpiv =  argsortDefault(DegreeArray);
                 //get the index based on each vertex's degree
             } catch {
                  try! smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),"error");
             }
             forall i in 0..Nv-1 {
                 VertexMapping[tmpiv[i]]=i;
                 // we assume the vertex ID is in 0..Nv-1
                 //given old vertex ID, map it to the new vertex ID
             }

             coforall loc in Locales  {
                on loc {
                  forall i in lsrc.localSubdomain(){
                        tmpedge[i]=VertexMapping[lsrc[i]];
                  }
                }
             }
             lsrc=tmpedge;
             coforall loc in Locales  {
                on loc {
                  forall i in ldst.localSubdomain(){
                        tmpedge[i]=VertexMapping[ldst[i]];
                  }
                }
             }
             ldst=tmpedge;
             coforall loc in Locales  {
                on loc {
                  forall i in lsrc.localSubdomain(){
                        if lsrc[i]>ldst[i] {
                           lsrc[i]<=>ldst[i];
                        }
                   }
                }
             }

             try  { combine_sort(lsrc, ldst,le_weight,lWeightedFlag, true);
             } catch {
                  try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
             }
             set_neighbour(lsrc,lstart_i,lneighbour);
  }

  //degree sort for an undirected graph.
  private  proc degree_sort_u(lsrc:[?D1] int, ldst:[?D2] int, lstart_i:[?D3] int, lneighbour:[?D4] int,
                      lsrcR:[?D5] int, ldstR:[?D6] int, lstart_iR:[?D7] int, lneighbourR:[?D8] int,le_weight:[?D9] int,lWeightedFlag:bool) {

             part_degree_sort(lsrc, ldst, lstart_i, lneighbour,le_weight,lneighbourR,lWeightedFlag);
             coforall loc in Locales  {
               on loc {
                  forall i in lsrcR.localSubdomain(){
                        lsrcR[i]=ldst[i];
                        ldstR[i]=lsrc[i];
                   }
               }
             }
             try  { combine_sort(lsrcR, ldstR,le_weight,lWeightedFlag, false);
             } catch {
                  try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
             }
             set_neighbour(lsrcR,lstart_iR,lneighbourR);

  }





  // directly read a graph from given file and build the SegGraph class in memory
  proc segGraphPreProcessingMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS,FileName,SkipLineS, RemapVertexS,DegreeSortS,RCMS,RwriteS) = payload.splitMsgToTuple(10);

      var Ne:int =(NeS:int);
      var Nv:int =(NvS:int);
     
      var NumCol=ColS:int;
      var DirectedFlag:bool=false;
      var WeightedFlag:bool=false;

      var SkipLineNum:int=(SkipLineS:int);
      var timer: Timer;
      var RCMFlag:bool=false;
      var DegreeSortFlag:bool=false;
      var RemapVertexFlag:bool=false;
      var WriteFlag:bool=false;
      outMsg="read file ="+FileName;
      smLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

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


      timer.start();
    
      var NewNe,NewNv:int;


      if (DirectedS:int)==1 {
          DirectedFlag=true;
      }
      if NumCol>2 {
           WeightedFlag=true;
      }
      if (RemapVertexS:int)==1 {
          RemapVertexFlag=true;
      }
      if (DegreeSortS:int)==1 {
          DegreeSortFlag=true;
      }
      if (RCMS:int)==1 {
          RCMFlag=true;
      }
      if (RwriteS:int)==1 {
          WriteFlag=true;
      }
      var src=makeDistArray(Ne,int);
      var edgeD=src.domain;


      var neighbour=makeDistArray(Nv,int);
      var vertexD=neighbour.domain;


      var dst,e_weight,srcR,dstR, iv: [edgeD] int ;
      var start_i,neighbourR, start_iR,depth, v_weight: [vertexD] int;

      var linenum:int=0;
      var repMsg: string;

      var tmpmindegree:int =start_min_degree;

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
                  var f = open(FileName, iomode.r);
                  var r = f.reader(kind=ionative);
                  var line:string;
                  var a,b,c:string;
                  var curline=0:int;
                  var srclocal=src.localSubdomain();
                  var ewlocal=e_weight.localSubdomain();
                  var mylinenum=SkipLineNum;

                  while r.readline(line) {
                      if line[0]=="%" || line[0]=="#" {
                          continue;
                      }
                      if mylinenum>0 {
                          mylinenum-=1;
                          continue;
                      }
                      if NumCol==2 {
                           (a,b)=  line.splitMsgToTuple(2);
                      } else {
                           (a,b,c)=  line.splitMsgToTuple(3);
                            //if ewlocal.contains(curline){
                            //    e_weight[curline]=c:int;
                            //}
                      }
                      if a==b {
                          smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                "self cycle "+ a +"->"+b);
                      }
                      if srclocal.contains(curline) {
                               src[curline]=(a:int);
                               dst[curline]=(b:int);
                      }
                      curline+=1;
                      if curline>srclocal.high {
                          break;
                      }
                  } 
                  if (curline<=srclocal.high) {
                     var myoutMsg="The input file " + FileName + " does not give enough edges for locale " + here.id:string +" current line="+curline:string;
                     smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),myoutMsg);
                  }
                  r.close();
                  f.close();
               }// end on loc
           }//end coforall
      }//end readLinebyLine
      
      // readLinebyLine sets ups src, dst, start_i, neightbor.  e_weights will also be set if it is an edge weighted graph
      // currently we ignore the weight.

      readLinebyLine(); 
      NewNv=vertex_remap(src,dst,Nv);
      
      try  { combine_sort(src, dst,e_weight,WeightedFlag, false);
      } catch {
             try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
      }

      set_neighbour(src,start_i,neighbour);

      if (!DirectedFlag) { //undirected graph
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                      "Handle undirected graph");
          coforall loc in Locales  {
              on loc {
                  forall i in srcR.localSubdomain(){
                        srcR[i]=dst[i];
                        dstR[i]=src[i];
                   }
              }
          }
          try  { combine_sort(srcR, dstR,e_weight,WeightedFlag, false);
          } catch {
                 try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
          }
          set_neighbour(srcR,start_iR,neighbourR);

          if (DegreeSortFlag) {
                    degree_sort_u(src, dst, start_i, neighbour, srcR, dstR, start_iR, neighbourR,e_weight,WeightedFlag);
          }



      }//end of undirected
      else {
          //part_degree_sort(src, dst, start_i, neighbour,e_weight,neighbour,WeightedFlag);
      }

      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                      "Handle self loop and duplicated edges");
      var cur=0;
      var tmpsrc=src;
      var tmpdst=dst;
      for i in 0..Ne-1 {
          if src[i]==dst[i] {
              continue;
              //self loop
          }
          if (cur==0) {
             tmpsrc[cur]=src[i];
             tmpdst[cur]=dst[i]; 
             cur+=1;
             continue;
          }
          if (tmpsrc[cur-1]==src[i]) && (tmpdst[cur-1]==dst[i]) {
              //duplicated edges
              continue;
          } else {
               if (src[i]>dst[i]) {

                    var u=src[i]:int;
                    var v=dst[i]:int;
                    var lu=start_i[u]:int;
                    var nu=neighbour[u]:int;
                    var lv=start_i[v]:int;
                    var nv=neighbour[v]:int;
                    var DupE:int;
                    DupE=binSearchE(dst,lv,lv+nv-1,u);
                    if DupE!=-1 {
                         //find v->u 
                         continue;
                    }
               }

               tmpsrc[cur]=src[i];
               tmpdst[cur]=dst[i]; 
               cur+=1;
          }
      }
      NewNe=cur;    
 
      if (NewNe<Ne ) {
      
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                      "removed "+(Ne-NewNe):string +" edges");

          var mysrc=makeDistArray(NewNe,int);
          var myedgeD=mysrc.domain;

          var myneighbour=makeDistArray(NewNv,int);
          var myvertexD=myneighbour.domain;

          var mydst,mye_weight,mysrcR,mydstR, myiv: [myedgeD] int ;
          var mystart_i,myneighbourR, mystart_iR,mydepth, myv_weight: [myvertexD] int;



          forall i in 0..NewNe-1 {
             mysrc[i]=tmpsrc[i];
             mydst[i]=tmpdst[i];
          }
          try  { combine_sort(mysrc, mydst,mye_weight,WeightedFlag, false);
          } catch {
                 try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
          }

          set_neighbour(mysrc,mystart_i,myneighbour);


          if (!DirectedFlag) { //undirected graph
              coforall loc in Locales  {
                  on loc {
                       forall i in mysrcR.localSubdomain(){
                            mysrcR[i]=mydst[i];
                            mydstR[i]=mysrc[i];
                       }
                  }
              }
              try  { combine_sort(mysrcR, mydstR,mye_weight,WeightedFlag, false);
              } catch {
                     try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                          "combine sort error");
              }
              set_neighbour(mysrcR,mystart_iR,myneighbourR);
              if (DegreeSortFlag) {
                    degree_sort_u(mysrc, mydst, mystart_i, myneighbour, mysrcR, mydstR, mystart_iR, myneighbourR,mye_weight,WeightedFlag);
              }

          }//end of undirected
          else {
              if (DegreeSortFlag) {
                 part_degree_sort(mysrc, mydst, mystart_i, myneighbour,mye_weight,myneighbour,WeightedFlag);

              }  
          }  
          if (WriteFlag) {
                  var wf = open(FileName+".pr", iomode.cw);
                  var mw = wf.writer(kind=ionative);
                  for i in 0..NewNe-1 {
                      mw.writeln("%-15i    %-15i".format(mysrc[i],mydst[i]));
                  }
                  mw.writeln("Num Edge=%i  Num Vertex=%i".format(NewNe, NewNv));
                  mw.close();
                  wf.close();
          }
      } else {
    
          if (WriteFlag) {
                  var wf = open(FileName+".pr", iomode.cw);
                  var mw = wf.writer(kind=ionative);
                  for i in 0..NewNe-1 {
                      mw.writeln("%-15i    %-15i".format(src[i],dst[i]));
                  }
                  mw.writeln("Num Edge=%i  Num Vertex=%i".format(NewNe, NewNv));
                  mw.close();
                  wf.close();
          }
      }
      timer.stop();
      outMsg="PreProcessing  File takes " + timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      repMsg =  "PreProcessing success"; 
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }





  // directly read a graph from given file and build the SegGraph class in memory
  proc segGraphNDEMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS,FileName,SkipLineS, RemapVertexS,DegreeSortS,RCMS,RwriteS) = payload.splitMsgToTuple(10);

      var Ne:int =(NeS:int);
      var Nv:int =(NvS:int);
     
      var NumCol=ColS:int;
      var DirectedFlag:bool=false;
      var WeightedFlag:bool=false;

      var SkipLineNum:int=(SkipLineS:int);
      var timer: Timer;
      var RCMFlag:bool=false;
      var DegreeSortFlag:bool=false;
      var RemapVertexFlag:bool=false;
      var WriteFlag:bool=false;
      outMsg="read file ="+FileName;
      smLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

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


      timer.start();
    
      var NewNe,NewNv:int;


      if (DirectedS:int)==1 {
          DirectedFlag=true;
      }
      if NumCol>2 {
           WeightedFlag=true;
      }
      if (RemapVertexS:int)==1 {
          RemapVertexFlag=true;
      }
      if (DegreeSortS:int)==1 {
          DegreeSortFlag=true;
      }
      if (RCMS:int)==1 {
          RCMFlag=true;
      }
      if (RwriteS:int)==1 {
          WriteFlag=true;
      }
      var src=makeDistArray(Ne,int);
      var edgeD=src.domain;


      var neighbour=makeDistArray(Nv,int);
      var vertexD=neighbour.domain;


      var dst,e_weight,srcR,dstR, iv: [edgeD] int ;
      var start_i,neighbourR, start_iR,depth, v_weight: [vertexD] int;

      var linenum:int=0;
      var repMsg: string;

      var tmpmindegree:int =start_min_degree;

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
                  var f = open(FileName, iomode.r);
                  var r = f.reader(kind=ionative);
                  var line:string;
                  var a,b,c:string;
                  var curline=0:int;
                  var srclocal=src.localSubdomain();
                  var ewlocal=e_weight.localSubdomain();
                  var mylinenum=SkipLineNum;

                  while r.readline(line) {
                      if line[0]=="%" || line[0]=="#" {
                          continue;
                      }
                      if mylinenum>0 {
                          mylinenum-=1;
                          continue;
                      }
                      if NumCol==2 {
                           (a,b)=  line.splitMsgToTuple(2);
                      } else {
                           (a,b,c)=  line.splitMsgToTuple(3);
                            //if ewlocal.contains(curline){
                            //    e_weight[curline]=c:int;
                            //}
                      }
                      if a==b {
                          smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                "self cycle "+ a +"->"+b);
                      }
                      if srclocal.contains(curline) {
                               src[curline]=(a:int);
                               dst[curline]=(b:int);
                      }
                      curline+=1;
                      if curline>srclocal.high {
                          break;
                      }
                  } 
                  if (curline<=srclocal.high) {
                     var myoutMsg="The input file " + FileName + " does not give enough edges for locale " + here.id:string +" current line="+curline:string;
                     smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),myoutMsg);
                  }
                  r.close();
                  f.close();
               }// end on loc
           }//end coforall
      }//end readLinebyLine
      
      // readLinebyLine sets ups src, dst, start_i, neightbor.  e_weights will also be set if it is an edge weighted graph
      // currently we ignore the weight.

      readLinebyLine(); 
      NewNv=vertex_remap(src,dst,Nv);
      
      try  { combine_sort(src, dst,e_weight,WeightedFlag, false);
      } catch {
             try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
      }

      set_neighbour(src,start_i,neighbour);

      if (!DirectedFlag) { //undirected graph
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                      "Handle undirected graph");
          coforall loc in Locales  {
              on loc {
                  forall i in srcR.localSubdomain(){
                        srcR[i]=dst[i];
                        dstR[i]=src[i];
                   }
              }
          }
          try  { combine_sort(srcR, dstR,e_weight,WeightedFlag, false);
          } catch {
                 try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
          }
          set_neighbour(srcR,start_iR,neighbourR);

          if (DegreeSortFlag) {
                    degree_sort_u(src, dst, start_i, neighbour, srcR, dstR, start_iR, neighbourR,e_weight,WeightedFlag);
          }



      }//end of undirected
      else {
          //part_degree_sort(src, dst, start_i, neighbour,e_weight,neighbour,WeightedFlag);
      }

      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                      "Handle self loop and duplicated edges");
      var cur=0;
      var tmpsrc=src;
      var tmpdst=dst;
      for i in 0..Ne-1 {
          if src[i]==dst[i] {
              continue;
              //self loop
          }
          if (cur==0) {
             tmpsrc[cur]=src[i];
             tmpdst[cur]=dst[i]; 
             cur+=1;
             continue;
          }
          if (tmpsrc[cur-1]==src[i]) && (tmpdst[cur-1]==dst[i]) {
              //duplicated edges
              continue;
          } else {
               if (src[i]>dst[i]) {

                    var u=src[i]:int;
                    var v=dst[i]:int;
                    var lu=start_i[u]:int;
                    var nu=neighbour[u]:int;
                    var lv=start_i[v]:int;
                    var nv=neighbour[v]:int;
                    var DupE:int;
                    DupE=binSearchE(dst,lv,lv+nv-1,u);
                    if DupE!=-1 {
                         //find v->u 
                         continue;
                    }
               }

               tmpsrc[cur]=src[i];
               tmpdst[cur]=dst[i]; 
               cur+=1;
          }
      }
      NewNe=cur;    
 
      if (NewNe<Ne ) {
      
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                      "removed "+(Ne-NewNe):string +" edges");

          var mysrc=makeDistArray(NewNe,int);
          var myedgeD=mysrc.domain;

          var myneighbour=makeDistArray(NewNv,int);
          var myvertexD=myneighbour.domain;

          var mydst,mye_weight,mysrcR,mydstR, myiv: [myedgeD] int ;
          var mystart_i,myneighbourR, mystart_iR,mydepth, myv_weight: [myvertexD] int;



          forall i in 0..NewNe-1 {
             mysrc[i]=tmpsrc[i];
             mydst[i]=tmpdst[i];
          }
          try  { combine_sort(mysrc, mydst,mye_weight,WeightedFlag, false);
          } catch {
                 try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
          }

          set_neighbour(mysrc,mystart_i,myneighbour);


          if (!DirectedFlag) { //undirected graph
              coforall loc in Locales  {
                  on loc {
                       forall i in mysrcR.localSubdomain(){
                            mysrcR[i]=mydst[i];
                            mydstR[i]=mysrc[i];
                       }
                  }
              }
              try  { combine_sort(mysrcR, mydstR,mye_weight,WeightedFlag, false);
              } catch {
                     try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                          "combine sort error");
              }
              set_neighbour(mysrcR,mystart_iR,myneighbourR);
              if (DegreeSortFlag) {
                    degree_sort_u(mysrc, mydst, mystart_i, myneighbour, mysrcR, mydstR, mystart_iR, myneighbourR,mye_weight,WeightedFlag);
              }

          }//end of undirected
          else {
              if (DegreeSortFlag) {
                 part_degree_sort(mysrc, mydst, mystart_i, myneighbour,mye_weight,myneighbour,WeightedFlag);

              }  
          }  
          if (WriteFlag) {
                  var wf = open(FileName+".nde", iomode.cw);
                  var mw = wf.writer(kind=ionative);
                  mw.writeln("%-15i".format(NewNv));
                  for i in 0..NewNv-1 {
                      mw.writeln("%-15i    %-15i".format(i,myneighbour[i]+myneighbourR[i]));
                  }
                  for i in 0..NewNe-1 {
                      mw.writeln("%-15i    %-15i".format(mysrc[i],mydst[i]));
                  }
                  mw.close();
                  wf.close();
          }
      } else {
    
          if (WriteFlag) {
                  var wf = open(FileName+".nde", iomode.cw);
                  var mw = wf.writer(kind=ionative);
                  mw.writeln("%-15i".format(NewNv));
                  for i in 0..NewNv-1 {
                      mw.writeln("%-15i    %-15i".format(i,neighbour[i]+neighbourR[i]));
                  }
                  for i in 0..NewNe-1 {
                      mw.writeln("%-15i    %-15i".format(src[i],dst[i]));
                  }
                  mw.close();
                  wf.close();
          }
      }
      timer.stop();
      outMsg="Transfermation  File takes " + timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      repMsg =  "To NDE  success"; 
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }




  // directly read a graph from given file and build the SegGraph class in memory
  proc segGraphFileMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS, FileName,RemapVertexS,DegreeSortS,RCMS,RwriteS) = payload.splitMsgToTuple(9);

      var Ne:int =(NeS:int);
      var Nv:int =(NvS:int);
      var NumCol=ColS:int;
      var DirectedFlag:bool=false;
      var WeightedFlag:bool=false;
      var timer: Timer;
      var RCMFlag:bool=false;
      var DegreeSortFlag:bool=false;
      var RemapVertexFlag:bool=false;
      var WriteFlag:bool=false;
      outMsg="read file ="+FileName;
      smLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.start();



      if (DirectedS:int)==1 {
          DirectedFlag=true;
      }
      if NumCol>2 {
           WeightedFlag=true;
      }
      if (RemapVertexS:int)==1 {
          RemapVertexFlag=true;
      }
      if (DegreeSortS:int)==1 {
          DegreeSortFlag=true;
      }
      if (RCMS:int)==1 {
          RCMFlag=true;
      }
      if (RwriteS:int)==1 {
          WriteFlag=true;
      }
      var src=makeDistArray(Ne,int);
      var edgeD=src.domain;

      /*
      var dst=makeDistArray(Ne,int);
      var e_weight=makeDistArray(Ne,int);
      var srcR=makeDistArray(Ne,int);
      var dstR=makeDistArray(Ne,int);
      var iv=makeDistArray(Ne,int);
      */

      var neighbour=makeDistArray(Nv,int);
      var vertexD=neighbour.domain;

      /*
      var start_i=makeDistArray(Nv,int);
      var neighbourR=makeDistArray(Nv,int);
      var start_iR=makeDistArray(Nv,int);
      var depth=makeDistArray(Nv,int);
      var v_weight=makeDistArray(Nv,int);
      */

      var dst,e_weight,srcR,dstR, iv: [edgeD] int ;
      var start_i,neighbourR, start_iR,depth, v_weight: [vertexD] int;

      var linenum:int=0;
      var repMsg: string;

      var tmpmindegree:int =start_min_degree;

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
                  var f = open(FileName, iomode.r);
                  var r = f.reader(kind=ionative);
                  var line:string;
                  var a,b,c:string;
                  var curline=0:int;
                  var srclocal=src.localSubdomain();
                  var ewlocal=e_weight.localSubdomain();

                  while r.readline(line) {
                      if line[0]=="%" {
                          smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                "edge  error");
                          continue;
                      }
                      if NumCol==2 {
                           (a,b)=  line.splitMsgToTuple(2);
                      } else {
                           (a,b,c)=  line.splitMsgToTuple(3);
                            //if ewlocal.contains(curline){
                            //    e_weight[curline]=c:int;
                            //}
                      }
                      if a==b {
                          smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                "self cycle "+ a +"->"+b);
                      }
                      if (RemapVertexFlag) {
                          if srclocal.contains(curline) {
                               src[curline]=(a:int);
                               dst[curline]=(b:int);
                          }
                      } else {
                          if srclocal.contains(curline) {
                              src[curline]=(a:int)%Nv;
                              dst[curline]=(b:int)%Nv;
                          }
                      }
                      curline+=1;
                      if curline>srclocal.high {
                          break;
                      }
                  } 
                  if (curline<=srclocal.high) {
                     var myoutMsg="The input file " + FileName + " does not give enough edges for locale " + here.id:string +" current line="+curline:string;
                     smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),myoutMsg);
                  }
                  r.close();
                  f.close();
               }// end on loc
           }//end coforall
      }//end readLinebyLine
      
      // readLinebyLine sets ups src, dst, start_i, neightbor.  e_weights will also be set if it is an edge weighted graph
      // currently we ignore the weight.

      readLinebyLine(); 
      if (RemapVertexFlag) {
          vertex_remap(src,dst,Nv);
      }
      timer.stop();
      

      outMsg="Reading File takes " + timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);


      timer.clear();
      timer.start();
      try  { combine_sort(src, dst,e_weight,WeightedFlag, false);
      } catch {
             try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
      }

      set_neighbour(src,start_i,neighbour);

      // Make a composable SegGraph object that we can store in a GraphSymEntry later
      var graph = new shared SegGraph(Ne, Nv, DirectedFlag);
      graph.withSRC(new shared SymEntry(src):GenSymEntry)
           .withDST(new shared SymEntry(dst):GenSymEntry)
           .withSTART_IDX(new shared SymEntry(start_i):GenSymEntry)
           .withNEIGHBOR(new shared SymEntry(neighbour):GenSymEntry);

      if (!DirectedFlag) { //undirected graph
          coforall loc in Locales  {
              on loc {
                  forall i in srcR.localSubdomain(){
                        srcR[i]=dst[i];
                        dstR[i]=src[i];
                   }
              }
          }
          try  { combine_sort(srcR, dstR,e_weight,WeightedFlag, false);
          } catch {
                 try!  smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
          }
          set_neighbour(srcR,start_iR,neighbourR);

          if (DegreeSortFlag) {
             degree_sort_u(src, dst, start_i, neighbour, srcR, dstR, start_iR, neighbourR,e_weight,WeightedFlag);
          }
          if (RCMFlag) {
             RCM_u(src, dst, start_i, neighbour, srcR, dstR, start_iR, neighbourR, depth,e_weight,WeightedFlag);
          }   


          graph.withSRC_R(new shared SymEntry(srcR):GenSymEntry)
               .withDST_R(new shared SymEntry(dstR):GenSymEntry)
               .withSTART_IDX_R(new shared SymEntry(start_iR):GenSymEntry)
               .withNEIGHBOR_R(new shared SymEntry(neighbourR):GenSymEntry);

      }//end of undirected
      else {
        if (DegreeSortFlag) {
             part_degree_sort(src, dst, start_i, neighbour,e_weight,neighbour,WeightedFlag);
        }
        if (RCMFlag) {
             RCM(src, dst, start_i, neighbour, depth,e_weight,WeightedFlag);
        }

      }
      //if (WeightedFlag) {
      //     graph.withEDGE_WEIGHT(new shared SymEntry(e_weight):GenSymEntry)
      //          .withVERTEX_WEIGHT(new shared SymEntry(v_weight):GenSymEntry);
      //}
      if (WriteFlag) {
                  var wf = open(FileName+".my.gr", iomode.cw);
                  var mw = wf.writer(kind=ionative);
                  for i in 0..Ne-1 {
                      mw.writeln("%-15n    %-15n".format(src[i],dst[i]));
                  }
                  mw.close();
                  wf.close();
      }
      var sNv=Nv:string;
      var sNe=Ne:string;
      var sDirected:string;
      var sWeighted:string;
      if (DirectedFlag) {
           sDirected="1";
      } else {
           sDirected="0";
      }

      if (WeightedFlag) {
           sWeighted="1";
      } else {
           sWeighted="0";
      }
      var graphEntryName = st.nextName();
      var graphSymEntry = new shared GraphSymEntry(graph);
      st.addEntry(graphEntryName, graphSymEntry);
      repMsg =  sNv + '+ ' + sNe + '+ ' + sDirected + '+ ' + sWeighted + '+' +  graphEntryName; 
      timer.stop();
      outMsg="Sorting Edges takes "+ timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }





  // directly read a graph from given file and build the SegGraph class in memory
  proc segGraphFileMtxMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS, FileName,RemapVertexS,DegreeSortS,RCMS,RwriteS) = payload.splitMsgToTuple(9);

      var Ne:int =(NeS:int);
      var Nv:int =(NvS:int);
      var NumCol:int =(ColS:int);
      var DirectedFlag:bool=false;
      var WeightedFlag:bool=false;
      var timer: Timer;
      var RCMFlag:bool=false;
      var DegreeSortFlag:bool=false;
      var RemapVertexFlag:bool=false;
      var WriteFlag:bool=false;
      outMsg="read file ="+FileName;
      writeln(outMsg);

      smLogger.info(getModuleName(),getRoutineName(),getLineNumber(), outMsg);
      timer.start();

      if (DirectedS:int)==1 {
          DirectedFlag=true;
      }
      if NumCol>2 {
           WeightedFlag=true;
      }
      if (DegreeSortS:int)==1 {
          DegreeSortFlag=true;
      }
      if (RCMS:int)==1 {
          RCMFlag=true;
      }
      if (RemapVertexS:int)==1 {
          RemapVertexFlag=true;
      }
      if (RwriteS:int)==1 {
          WriteFlag=true;
      }
      var src=makeDistArray(Ne,int);
      var edgeD=src.domain;
      /*
      var dst=makeDistArray(Ne,int);
      var e_RwRwrght=makeDistArray(Ne,int);
      RwRwr srcR=makeDistArray(Ne,int);
      var dstR=makeDistArray(Ne,int);
      var iv=makeDistArray(Ne,int);
      */
      var neighbour=makeDistArray(Nv,int);
      var vertexD=neighbour.domain;
      /*
      var start_i=makeDistArray(Nv,int);
      var neighbourR=makeDistArray(Nv,int);
      var start_iR=makeDistArray(Nv,int);
      var depth=makeDistArray(Nv,int);
      var v_weight=makeDistArray(Nv,int);
      */
      var dst,e_weight,srcR,dstR, iv: [edgeD] int ;
      var start_i,neighbourR, start_iR,depth, v_weight: [vertexD] int;

      var linenum:int=0;
      var repMsg: string;

      var VminID=makeDistArray(numLocales,int);
      var VmaxID=makeDistArray(numLocales,int);
      VminID=100000;
      VmaxID=0;

      var tmpmindegree:int =start_min_degree;

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
                  var f = open(FileName, iomode.r);
                  var r = f.reader(kind=ionative);
                  var line:string;
                  var a,b,c:string;
                  var curline=0:int;
                  var srclocal=src.localSubdomain();
                  var ewlocal=e_weight.localSubdomain();
                  var StartF:bool=false;
                  var Nvsrc,Nvdst,Nedge:string;


                  while r.readline(line) {
                      if line[0]=="%" {
                          continue;
                      }
                      if ((curline==0) && (!StartF)) {
                          (Nvsrc,Nvdst,Nedge)=  line.splitMsgToTuple(3);
                          var errmsg:string;
                          if ( (Nvsrc:int) != (Nvdst:int) || (Nvsrc:int!=Nv) || (Nedge:int!=Ne) ) {
                             errmsg="v and e not matched"+" read vertex="+Nvsrc+" read edges="+Nedge;
                             smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                    errmsg);

                          }
                          StartF=true;
                          continue;
                      }
                      if NumCol==2 {
                           (a,b)=  line.splitMsgToTuple(2);
                      } else {
                           (a,b,c)=  line.splitMsgToTuple(3);
                            //if ewlocal.contains(curline){
                            //    e_weight[curline]=c:int;
                            //}
                      }
                      if (a==b) {
                             smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                    "self cycle "+ a +"->" +b);
                      }
                      if (RemapVertexFlag) {
                          if srclocal.contains(curline) {
                               src[curline]=(a:int);
                               dst[curline]=(b:int);
                          }
                      } else {
                          if srclocal.contains(curline) {
                              src[curline]=(a:int)%Nv;
                              dst[curline]=(b:int)%Nv;
                          }
                      }
                      curline+=1;
                      if curline>srclocal.high {
                          break;
                      }
                  } 
                  if (curline<=srclocal.high) {
                     var myoutMsg="The input file " + FileName + " does not give enough edges for locale " + here.id:string;
                     smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),myoutMsg);
                  }
                  //forall i in start_i.localSubdomain()  {
                  //     start_i[i]=-1;
                  //}
                  //forall i in start_iR.localSubdomain()  {
                  //     start_iR[i]=-1;
                  //}
                  r.close();
                  f.close();
               }// end on loc
           }//end coforall
      }//end readLinebyLine
      
      // readLinebyLine sets ups src, dst, start_i, neightbor.  e_weights will also be set if it is an edge weighted graph
      // currently we ignore the weight.

      readLinebyLine(); 
      if (RemapVertexFlag) {
          vertex_remap(src,dst,Nv);
      }
      timer.stop();
      

      outMsg="Reading File takes " + timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);


      timer.clear();
      timer.start();
      try  { combine_sort(src, dst,e_weight,WeightedFlag, false);
          } catch {
             try!      smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
      }
      set_neighbour(src,start_i,neighbour);

      // Make a composable SegGraph object that we can store in a GraphSymEntry later
      var graph = new shared SegGraph(Ne, Nv, DirectedFlag);
      graph.withSRC(new shared SymEntry(src):GenSymEntry)
           .withDST(new shared SymEntry(dst):GenSymEntry)
           .withSTART_IDX(new shared SymEntry(start_i):GenSymEntry)
           .withNEIGHBOR(new shared SymEntry(neighbour):GenSymEntry);

      if (!DirectedFlag) { //undirected graph
          coforall loc in Locales  {
              on loc {
                  forall i in srcR.localSubdomain(){
                        srcR[i]=dst[i];
                        dstR[i]=src[i];
                   }
              }
          }
          try  { combine_sort(srcR, dstR,e_weight,WeightedFlag, false);
              } catch {
               try!    smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
          }
          set_neighbour(srcR,start_iR,neighbourR);

          if (DegreeSortFlag) {
             degree_sort_u(src, dst, start_i, neighbour, srcR, dstR, start_iR, neighbourR,e_weight,WeightedFlag);
          }
          if (RCMFlag) {
             RCM_u(src, dst, start_i, neighbour, srcR, dstR, start_iR, neighbourR, depth,e_weight,WeightedFlag);
          }   


          graph.withSRC_R(new shared SymEntry(srcR):GenSymEntry)
               .withDST_R(new shared SymEntry(dstR):GenSymEntry)
               .withSTART_IDX_R(new shared SymEntry(start_iR):GenSymEntry)
               .withNEIGHBOR_R(new shared SymEntry(neighbourR):GenSymEntry);

      }//end of undirected
      else {
        if (DegreeSortFlag) {
             part_degree_sort(src, dst, start_i, neighbour,e_weight,neighbour,WeightedFlag);
        }
        if (RCMFlag) {
             RCM(src, dst, start_i, neighbour, depth,e_weight,WeightedFlag);
        }

      }
      //if (WeightedFlag) {
      //     graph.withEDGE_WEIGHT(new shared SymEntry(e_weight):GenSymEntry)
      //          .withVERTEX_WEIGHT(new shared SymEntry(v_weight):GenSymEntry);
      //}
      if (WriteFlag) {
                  var wf = open(FileName+".my.pr", iomode.cw);
                  var mw = wf.writer(kind=ionative);
                  for i in 0..Ne-1 {
                      mw.writeln("%-12n    %-12n".format(src[i],dst[i]));
                  }
                  mw.close();
                  wf.close();
      }
      var sNv=Nv:string;
      var sNe=Ne:string;
      var sDirected:string;
      var sWeighted:string;
      if (DirectedFlag) {
           sDirected="1";
      } else {
           sDirected="0";
      }

      if (WeightedFlag) {
           sWeighted="1";
      } else {
           sWeighted="0";
           
      }
      var graphEntryName = st.nextName();
      var graphSymEntry = new shared GraphSymEntry(graph);
      st.addEntry(graphEntryName, graphSymEntry);
      repMsg =  sNv + '+ ' + sNe + '+ ' + sDirected + '+ ' + sWeighted + '+' +  graphEntryName; 
      timer.stop();
      outMsg="Sorting Edges takes "+ timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }




  //generate a graph using RMAT method.
  proc segrmatgenMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var repMsg: string;
      var (slgNv, sNe_per_v, sp, sdire,swei,RCMs )
          = payload.splitMsgToTuple(6);

      var lgNv = slgNv: int;
      var Ne_per_v = sNe_per_v: int;
      var p = sp: real;
      var DirectedFlag=false:bool;
      var WeightedFlag=false:bool;
      var RCMFlag=false:bool;
      var DegreeSortFlag=false:bool;
      var tmpmindegree=start_min_degree;

      if (sdire: int)==1 {
         DirectedFlag=true;
      }
      if (swei: int)==1 {
          WeightedFlag=true;
      }
      
      if (RCMs:int)==1 {
          RCMFlag=true;
      }



      var Nv = 2**lgNv:int;
      // number of edges
      var Ne = Ne_per_v * Nv:int;

      var timer:Timer;
      timer.clear();
      timer.start();
      var n_vertices=Nv;
      var n_edges=Ne;
      var src=makeDistArray(Ne,int);
      var dst=makeDistArray(Ne,int);
      var e_weight=makeDistArray(Ne,int);
      var srcR=makeDistArray(Ne,int);
      var dstR=makeDistArray(Ne,int);
      var iv=makeDistArray(Ne,int);
      //var edgeD=src.domain;
      //var vertexD=neighbour.domain;
      var neighbour=makeDistArray(Nv,int);
      var start_i=makeDistArray(Nv,int);
      var neighbourR=makeDistArray(Nv,int);
      var start_iR=makeDistArray(Nv,int);
      var depth=makeDistArray(Nv,int);
      var v_weight=makeDistArray(Nv,int);

      /*
      var src=makeDistArray(Ne,int);
      var edgeD=src.domain;
      var neighbour=makeDistArray(Nv,int);
      var vertexD=neighbour.domain;
    

      var dst,e_weight,srcR,dstR, iv: [edgeD] int ;
      var start_i, depth,neighbourR, start_iR, v_weight : [vertexD] int;
      */

 
      coforall loc in Locales  {
          on loc {
              forall i in src.localSubdomain() {
                  src[i]=1;
              }
              forall i in dst.localSubdomain() {
                  dst[i]=0;
              }
              //forall i in start_i.localSubdomain() {
              //    start_i[i]=-1;
              //}
              //forall i in neighbour.localSubdomain() {
              //    neighbour[i]=0;
              //}
          }
      }
      var srcName:string ;
      var dstName:string ;
      var startName:string ;
      var neiName:string ;
      var sNv:string;
      var sNe:string;
      var sDirected:string;
      var sWeighted:string;

      proc rmat_gen() {
             var a = p;
             var b = (1.0 - a)/ 3.0:real;
             var c = b;
             var d = b;
             var ab=a+b;
             var c_norm = c / (c + d):real;
             var a_norm = a / (a + b):real;
             // generate edges
             //var src_bit=: [0..Ne-1]int;
             //var dst_bit: [0..Ne-1]int;
             var src_bit=src;
             var dst_bit=dst;

             for ib in 1..lgNv {
                 //var tmpvar: [0..Ne-1] real;
                 var tmpvar=src;
                 fillRandom(tmpvar);
                 coforall loc in Locales  {
                       on loc {
                           forall i in src_bit.localSubdomain() {
                                 src_bit[i]=tmpvar[i]>ab;
                           }       
                       }
                 }
                 //src_bit=tmpvar>ab;
                 fillRandom(tmpvar);
                 coforall loc in Locales  {
                       on loc {
                           forall i in dst_bit.localSubdomain() {
                                 dst_bit[i]=tmpvar[i]>(c_norm * src_bit[i] + a_norm * (~ src_bit[i]));
                           }       
                       }
                 }
                 //dst_bit=tmpvar>(c_norm * src_bit + a_norm * (~ src_bit));
                 coforall loc in Locales  {
                       on loc {
                           forall i in dst.localSubdomain() {
                                 dst[i]=dst[i]+ ((2**(ib-1)) * dst_bit[i]);
                           }       
                           forall i in src.localSubdomain() {
                                 src[i]=src[i]+ ((2**(ib-1)) * src_bit[i]);
                           }       
                       }
                 }
                 //src = src + ((2**(ib-1)) * src_bit);
                 //dst = dst + ((2**(ib-1)) * dst_bit);
             }
             coforall loc in Locales  {
                       on loc {
                           forall i in src_bit.localSubdomain() {
                                 src[i]=src[i]+(src[i]==dst[i]);
                                 src[i]=src[i]%Nv;
                                 dst[i]=dst[i]%Nv;
                           }       
                       }
             }

      }//end rmat_gen
      


      rmat_gen();
      timer.stop();
      outMsg="RMAT generate the graph takes "+timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.clear();
      timer.start();


 
      try  { combine_sort(src, dst,e_weight,WeightedFlag, false);
              } catch {
             try!      smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
      }
      set_neighbour(src,start_i,neighbour);

      // Make a composable SegGraph object that we can store in a GraphSymEntry later
      var graph = new shared SegGraph(Ne, Nv,DirectedFlag);
      graph.withSRC(new shared SymEntry(src):GenSymEntry)
               .withDST(new shared SymEntry(dst):GenSymEntry)
               .withSTART_IDX(new shared SymEntry(start_i):GenSymEntry)
               .withNEIGHBOR(new shared SymEntry(neighbour):GenSymEntry);

      if (!DirectedFlag) { //undirected graph
              coforall loc in Locales  {
                  on loc {
                      forall i in srcR.localSubdomain(){
                            srcR[i]=dst[i];
                            dstR[i]=src[i];
                       }
                  }
              }
              try  { combine_sort(srcR, dstR,e_weight,WeightedFlag, false);
              } catch {
                  try! smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                      "combine sort error");
              }
              set_neighbour(srcR,start_iR,neighbourR);

              if (DegreeSortFlag) {
                 degree_sort_u(src, dst, start_i, neighbour, srcR, dstR, start_iR, neighbourR,e_weight,WeightedFlag);
              }
              if (RCMFlag) {
                 RCM_u( src, dst, start_i, neighbour, srcR, dstR, start_iR, neighbourR, depth,e_weight,WeightedFlag);
              }   

              graph.withSRC_R(new shared SymEntry(srcR):GenSymEntry)
                   .withDST_R(new shared SymEntry(dstR):GenSymEntry)
                   .withSTART_IDX_R(new shared SymEntry(start_iR):GenSymEntry)
                   .withNEIGHBOR_R(new shared SymEntry(neighbourR):GenSymEntry);
      }//end of undirected
      else {
            //if (DegreeSortFlag) {
            //     degree_sort(src, dst, start_i, neighbour,e_weight,neighbourR,WeightedFlag);
            //}
            if (RCMFlag) {
                 RCM( src, dst, start_i, neighbour, depth,e_weight,WeightedFlag);
            }

      }//end of 
      if (WeightedFlag) {
               fillInt(e_weight,1,1000);
               fillInt(v_weight,1,1000);
               graph.withEDGE_WEIGHT(new shared SymEntry(e_weight):GenSymEntry)
                    .withVERTEX_WEIGHT(new shared SymEntry(v_weight):GenSymEntry);
      }
      var gName = st.nextName();
      st.addEntry(gName, new shared GraphSymEntry(graph));

      if (DirectedFlag) {
           sDirected="1";
      } else {
           sDirected="0";
      }

      if (WeightedFlag) {
           sWeighted="1";
      } else {
           sWeighted="0";
           
      }
      repMsg =  sNv + '+ ' + sNe + '+ ' + sDirected + '+ ' + sWeighted + '+ '+ gName;

      timer.stop();
      //writeln("$$$$$$$$$$$$  $$$$$$$$$$$$$$$$$$$$$$$");
      //writeln("$$$$$$$$$$$$  $$$$$$$$$$$$$$$$$$$$$$$");
      //writeln("$$$$$$$$$$$$$$$$$ sorting RMAT graph takes ",timer.elapsed(), "$$$$$$$$$$$$$$$$$$");
      outMsg="sorting RMAT graph takes "+timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);      
      //writeln("$$$$$$$$$$$$  $$$$$$$$$$$$$$$$$$$$$$$");
      //writeln("$$$$$$$$$$$$  $$$$$$$$$$$$$$$$$$$$$$$");
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);      
      return new MsgTuple(repMsg, MsgType.NORMAL);
  }





  // visit a graph using BFS method
  proc segGraphQueMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var repMsg: string;
      var (graphEntryName, queID)
          = payload.splitMsgToTuple(2);
      var timer:Timer;

      timer.start();
      var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
      var ag = gEntry.graph;
      var Ne=ag.n_edges;
      var Nv=ag.n_vertices;

      var attrName = st.nextName();
      var attrMsg:string;
       
      select queID {
           when "src" {
              var retE=toSymEntry(ag.getSRC(), int).a;
              var attrEntry = new shared SymEntry(retE);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "dst" {
              var retE=toSymEntry(ag.getDST(), int).a;
              var attrEntry = new shared SymEntry(retE);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "start_i" {
              var retV=toSymEntry(ag.getSTART_IDX(), int).a;
              var attrEntry = new shared SymEntry(retV);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "neighbour" {
              var retV=toSymEntry(ag.getNEIGHBOR(), int).a;
              var attrEntry = new shared SymEntry(retV);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "srcR" {
              var retE=toSymEntry(ag.getSRC_R(), int).a;
              var attrEntry = new shared SymEntry(retE);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "dstR" {
              var retE=toSymEntry(ag.getDST_R(), int).a;
              var attrEntry = new shared SymEntry(retE);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "start_iR" {
              var retV=toSymEntry(ag.getSTART_IDX_R(), int).a;
              var attrEntry = new shared SymEntry(retV);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "neighbourR" {
              var retV=toSymEntry(ag.getNEIGHBOR_R(), int).a;
              var attrEntry = new shared SymEntry(retV);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "v_weight" {
              var retV=toSymEntry(ag.getVERTEX_WEIGHT(), int).a;
              var attrEntry = new shared SymEntry(retV);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
           when "e_weight" {
              var retE=toSymEntry(ag.getEDGE_WEIGHT(), int).a;
              var attrEntry = new shared SymEntry(retE);
              st.addEntry(attrName, attrEntry);
              attrMsg =  'created ' + st.attrib(attrName);
           }
      }

      timer.stop();
      outMsg= "graph query takes "+timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),attrMsg);
      return new MsgTuple(attrMsg, MsgType.NORMAL);
    }

    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedGraphFile", segGraphFileMsg);
        registerFunction("segmentedGraphPreProcessing", segGraphPreProcessingMsg);
        registerFunction("segmentedGraphFileMtx", segGraphFileMtxMsg);
        registerFunction("segmentedRMAT", segrmatgenMsg);
        registerFunction("segmentedGraphQue", segGraphQueMsg);
        registerFunction("segmentedGraphToNDE", segGraphNDEMsg);

    }
 }


