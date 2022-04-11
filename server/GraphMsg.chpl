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


  private config const logLevel = ServerConfig.logLevel;
  const smLogger = new Logger(logLevel);
  



  config const start_min_degree = 1000000;
  //var tmpmindegree=start_min_degree;

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

  private proc vertex_remap( lsrc:[?D1] int, ldst:[?D2] int, orimin: int, orimax:int, numV:int) {
          var numE=lsrc.size;
          var tmpe:[D1] int;

          var VertexSet= new set(int,parSafe = true);
          tmpe=0;
          var startV=0;
          var endV=numV-1;
          forall i in lsrc with (ref VertexSet) {
                VertexSet.add(i);
          }
          forall i in ldst with (ref VertexSet) {
                VertexSet.add(i);
          }
          var vertexAry=VertexSet.toArray();
          sort(vertexAry);
          forall i in 0..numE-1 {
               lsrc[i]=binSearchV(vertexAry,0,numV-1,lsrc[i]);
               ldst[i]=binSearchV(vertexAry,0,numV-1,ldst[i]);
          }
  }
      /* 
       * we sort the combined array [src dst] here
       */
  private proc combine_sort( lsrc:[?D1] int, ldst:[?D2] int, le_weight:[?D3] int,  lWeightedFlag: bool, sortw=false: bool )  {
             param bitsPerDigit = RSLSD_bitsPerDigit;
             var bitWidths: [0..1] int;
             var negs: [0..1] bool;
             var totalDigits: int;
             var size=D1.size;
             var iv:[D1] int;

             //sort the merged array
             proc mergedArgsort() throws {
                    var merged = makeDistArray(size, 2*uint(bitsPerDigit));
                    forall (m,s,d) in zip (merged,lsrc,ldst){
                          m=(s:uint(bitsPerDigit),d:uint(bitsPerDigit));
                    }
                    var tmpiv:[D1] int;
                    try {
                    
                         tmpiv =  argsortDefault(merged);
                    } catch {
                        try! smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),"error");
                    }    
                    return tmpiv;
             }

             try {
                      iv = mergedArgsort(); 
             } catch {
                  try! smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),
                      "error" );
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
          var indexary:[0..Nv-1] int;
          var iv:[D1] int;
          ldepth=-1;
          proc smallVertex() :int {
                var minindex:int;
                var tmpmindegree:int;
                for i in 0..Nv-1 {
                   if (lneighbour[i]<tmpmindegree) && (lneighbour[i]>0) {
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
                    var tmpary:[0..numCurF-1] int;
                    var sortary:[0..numCurF-1] int;
                    var numary:[0..numCurF-1] int;
                    var tmpa=0:int;
                    forall (a,b)  in zip (tmpary,SetNextF.toArray()) {
                        a=b;
                    }
                    forall i in 0..numCurF-1 {
                         numary[i]=lneighbour[tmpary[i]];
                    }
                    var tmpiv:[D1]int;
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

          combine_sort( lsrc, ldst,le_weight,lWeightedFlag, false);
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
                    var tmpmindegree:int;
                    for i in 0..Nv-1 {
                       if (lneighbour[i]<tmpmindegree) && (lneighbour[i]>0) {
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
                             numary[i]=lneighbour[tmpary[i]];
                        }
                        var tmpiv:[D1] int;
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
 
              //neighbour=0;
              //start_i=-1;
        
              combine_sort( lsrc, ldst,le_weight,lWeightedFlag, true);
              set_neighbour(lsrc,lstart_i,lneighbour);
              coforall loc in Locales  {
                  on loc {
                      forall i in lsrcR.localSubdomain(){
                            lsrcR[i]=ldst[i];
                            ldstR[i]=lsrc[i];
                       }
                  }
               }
               //lneighbourR=0;
               //lstart_iR=-1;
               combine_sort( lsrcR, ldstR,le_weight,lWeightedFlag, false);
               set_neighbour(lsrcR,lstart_iR,lneighbourR);
               //return true;
  }//end RCM_u



  //sorting the vertices based on their degrees.
  private proc degree_sort(lsrc:[?D1] int, ldst:[?D2] int, lstart_i:[?D3] int, lneighbour:[?D4] int,le_weight:[?D5] int,lneighbourR:[?D6] int,lWeightedFlag:bool) {
             var DegreeArray, VertexArray: [D4] int;
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
             } catch {
                  try! smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),"error");
             }
             forall i in 0..Nv-1 {
                 VertexArray[tmpiv[i]]=i;
             }
             coforall loc in Locales  {
                on loc {
                  forall i in lsrc.localSubdomain(){
                        tmpedge[i]=VertexArray[lsrc[i]];
                  }
                }
             }
             lsrc=tmpedge;
             coforall loc in Locales  {
                on loc {
                  forall i in ldst.localSubdomain(){
                        tmpedge[i]=VertexArray[ldst[i]];
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

             combine_sort( lsrc, ldst,le_weight,lWeightedFlag, true);
             //neighbour=0;
             //start_i=-1;
             set_neighbour(lsrc,lstart_i,lneighbour);

  }

  //degree sort for an undirected graph.
  private  proc degree_sort_u(lsrc:[?D1] int, ldst:[?D2] int, lstart_i:[?D3] int, lneighbour:[?D4] int,
                      lsrcR:[?D5] int, ldstR:[?D6] int, lstart_iR:[?D7] int, lneighbourR:[?D8] int,le_weight:[?D9] int,lWeightedFlag:bool) {

             degree_sort(lsrc, ldst, lstart_i, lneighbour,le_weight,lneighbourR,lWeightedFlag);
             coforall loc in Locales  {
               on loc {
                  forall i in lsrcR.localSubdomain(){
                        lsrcR[i]=ldst[i];
                        ldstR[i]=lsrc[i];
                   }
               }
             }
             combine_sort( lsrcR, ldstR,le_weight,lWeightedFlag, false);
             set_neighbour(lsrcR,lstart_iR,lneighbourR);

  }

  // directly read a graph from given file and build the SegGraph class in memory
  proc segGraphFileMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS, FileName,RCMs,DegreeSortS,RemapVertex) = payload.splitMsgToTuple(8);

      var Ne:int =(NeS:int);
      var Nv:int =(NvS:int);
      var NumCol=ColS:int;
      var DirectedFlag:bool=false;
      var WeightedFlag:bool=false;
      var timer: Timer;
      var RCMFlag:bool=false;
      var DegreeSortFlag:bool=false;
      var RemapVertexFlag:bool=false;

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
      if (RCMs:int)==1 {
          RCMFlag=true;
      }
      if (RemapVertex:int)==1 {
          RemapVertexFlag=true;
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

                  while r.readline(line) {
                      if NumCol==2 {
                           (a,b)=  line.splitMsgToTuple(2);
                      } else {
                           (a,b,c)=  line.splitMsgToTuple(3);
                            //if ewlocal.contains(curline){
                            //    e_weight[curline]=c:int;
                            //}
                      }
                      if (RemapVertexFlag) {
                          if srclocal.contains(curline) {
                               src[curline]=(a:int);
                               dst[curline]=(b:int);
                               if a:int > VmaxID[here.id] {
                                   VmaxID[here.id]=a:int;
                               }
                               if b:int > VmaxID[here.id] {
                                   VmaxID[here.id]=b:int;
                               }
                               if a:int < VminID[here.id] {
                                   VminID[here.id]=a:int;
                               }
                               if b:int < VminID[here.id] {
                                   VminID[here.id]=b:int;
                               }
                          
                          }
                      } else {
                          if srclocal.contains(curline) {
                              src[curline]=(a:int)%Nv;
                              dst[curline]=(b:int)%Nv;
                          }
                      }
                      curline+=1;
                      curline+=1;
                      if curline>srclocal.high {
                          break;
                      }
                  } 
                  if (curline<=srclocal.high) {
                     var outMsg="The input file " + FileName + " does not give enough edges for locale " + here.id:string +" current line="+curline:string;
                     smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
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
          var tmpmax:int =-1;
          var tmpmin:int=9999999;
          for i in VmaxID {
               if i>tmpmax {
                   tmpmax=i;
               }
          }
          for i in VminID {
               if i<tmpmin {
                   tmpmin=i;
               }
          }
          vertex_remap(src,dst,tmpmin,tmpmax,Nv);
      }
      timer.stop();
      

      var outMsg="Reading File takes " + timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);


      timer.clear();
      timer.start();
      combine_sort(src, dst,e_weight,WeightedFlag, false);
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
          combine_sort( srcR, dstR,e_weight,WeightedFlag, false);
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
        //if (DegreeSortFlag) {
             //degree_sort(src, dst, start_i, neighbour,e_weight);
        //}
        if (RCMFlag) {
             RCM(src, dst, start_i, neighbour, depth,e_weight,WeightedFlag);
        }

      }
      //if (WeightedFlag) {
      //     graph.withEDGE_WEIGHT(new shared SymEntry(e_weight):GenSymEntry)
      //          .withVERTEX_WEIGHT(new shared SymEntry(v_weight):GenSymEntry);
      //}
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
  proc segReadMtxMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var (NeS,NvS,ColS,DirectedS, FileName,RCMs,DegreeSortS,RemapVertex) = payload.splitMsgToTuple(8);

      var Ne:int =(NeS:int);
      var Nv:int =(NvS:int);
      var NumCol=ColS:int;
      var DirectedFlag:bool=false;
      var WeightedFlag:bool=false;
      var timer: Timer;
      var RCMFlag:bool=false;
      var DegreeSortFlag:bool=false;
      var RemapVertexFlag:bool=false;

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
      if (RCMs:int)==1 {
          RCMFlag=true;
      }
      if (RemapVertex:int)==1 {
          RemapVertexFlag=true;
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
                      if (RemapVertexFlag) {
                          if srclocal.contains(curline) {
                               src[curline]=(a:int);
                               dst[curline]=(b:int);
                               if a:int > VmaxID[here.id] {
                                   VmaxID[here.id]=a:int;
                               }
                               if b:int > VmaxID[here.id] {
                                   VmaxID[here.id]=b:int;
                               }
                               if a:int < VminID[here.id] {
                                   VminID[here.id]=a:int;
                               }
                               if b:int < VminID[here.id] {
                                   VminID[here.id]=b:int;
                               }
                          
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
                     var outMsg="The input file " + FileName + " does not give enough edges for locale " + here.id:string;
                     smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
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
          var tmpmax:int =-1;
          var tmpmin:int=9999999;
          for i in VmaxID {
               if i>tmpmax {
                   tmpmax=i;
               }
          }
          for i in VminID {
               if i<tmpmin {
                   tmpmin=i;
               }
          }
          vertex_remap(src,dst,tmpmin,tmpmax,Nv);
      }
      timer.stop();
      

      var outMsg="Reading File takes " + timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);


      timer.clear();
      timer.start();
      combine_sort(src, dst,e_weight,WeightedFlag, false);
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
          combine_sort( srcR, dstR,e_weight,WeightedFlag, false);
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
        //if (DegreeSortFlag) {
             //degree_sort(src, dst, start_i, neighbour,e_weight);
        //}
        if (RCMFlag) {
             RCM(src, dst, start_i, neighbour, depth,e_weight,WeightedFlag);
        }

      }
      //if (WeightedFlag) {
      //     graph.withEDGE_WEIGHT(new shared SymEntry(e_weight):GenSymEntry)
      //          .withVERTEX_WEIGHT(new shared SymEntry(v_weight):GenSymEntry);
      //}
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
      var outMsg="RMAT generate the graph takes "+timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      timer.clear();
      timer.start();


 
      combine_sort( src, dst,e_weight,WeightedFlag, false);
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
              combine_sort(srcR,dstR,e_weight, WeightedFlag, false);
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
      var outMsg= "graph query takes "+timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),attrMsg);
      return new MsgTuple(attrMsg, MsgType.NORMAL);
    }

    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedGraphFile", segGraphFileMsg);
        registerFunction("segmentedGraphMtxFile", segReadMtxMsg);
        registerFunction("segmentedRMAT", segrmatgenMsg);
        registerFunction("segmentedGraphQue", segGraphQueMsg);
    }
 }


