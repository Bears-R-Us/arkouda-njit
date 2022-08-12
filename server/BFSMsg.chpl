module BFSMsg {


  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  use SegmentedString;
  use ServerErrorStrings;
  use ServerConfig;
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  //use RandArray;
  use IO;


  use SymArrayDmap;
  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use ArgSortMsg;
  use Time;
  use CommAggregation;
  //use Sort;
  use Map;
  use DistributedDeque;


  use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;


  //private config const logLevel = ServerConfig.logLevel;
  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  
  config const start_min_degree = 1000000;
  var tmpmindegree=start_min_degree;

  private proc xlocal(x :int, low:int, high:int):bool {
      return low<=x && x<=high;
  }

  private proc xremote(x :int, low:int, high:int):bool {
      return !xlocal(x, low, high);
  }


  // visit a graph using BFS method
  proc segBFSMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var repMsg: string;
      var (RCMs, n_verticesN, n_edgesN, directedN, weightedN, graphEntryName, restpart )
          = payload.splitMsgToTuple(7);
      var Nv=n_verticesN:int;
      var Ne=n_edgesN:int;
      var Directed=directedN:int;
      var Weighted=weightedN:int;
      var depthName:string;
      var RCMFlag=RCMs:int;
      var timer:Timer;



      timer.start();
      var depth=makeDistArray(Nv,int);
      coforall loc in Locales  {
                  on loc {
                           forall i in depth.localSubdomain() {
                                 depth[i]=-1; }       
                  }
      }
      var root:int;
      var srcN, dstN, startN, neighbourN,vweightN,eweightN, rootN :string;
      var srcRN, dstRN, startRN, neighbourRN:string;
      var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
      var ag = gEntry.graph;
 
      proc _d1_bfs_kernel(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int):string throws{
          var cur_level=0;
          var numCurF=1:int;//flag for stopping loop


          var edgeBeginG=makeDistArray(numLocales,int);//each locale's starting edge ID
          var edgeEndG=makeDistArray(numLocales,int);//each locales'ending edge ID

          var vertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var vertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src
          var HvertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var HvertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src
          var TvertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var TvertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src


          var localNum=makeDistArray(numLocales,int);// current locales's local access times
          var remoteNum=makeDistArray(numLocales,int);// current locales's remote access times
          localNum=0;
          remoteNum=0;

          var MaxBufSize=makeDistArray(numLocales,int);//temp array to calculate global max
          coforall loc in Locales   {
              on loc {
                 edgeBeginG[here.id]=src.localSubdomain().low;
                 edgeEndG[here.id]=src.localSubdomain().high;

                 vertexBeginG[here.id]=src[edgeBeginG[here.id]];
                 vertexEndG[here.id]=src[edgeEndG[here.id]];

                 if (here.id>0) {
                   HvertexBeginG[here.id]=vertexEndG[here.id-1];
                 } else {
                   HvertexBeginG[here.id]=-1;
                 }
                 if (here.id<numLocales-1) {
                   TvertexEndG[here.id]=vertexBeginG[here.id+1];
                 } else {
                   TvertexEndG[here.id]=nei.size;
                 }

                 MaxBufSize[here.id]=vertexEndG[here.id]-vertexBeginG[here.id]+1;
              }
          }
          var CMaxSize=1: int;
          for i in 0..numLocales-1 {
              if   MaxBufSize[i]> CMaxSize {
                   CMaxSize=MaxBufSize[i];
              }
          }
          var localArrayG=makeDistArray(numLocales*CMaxSize,int);//current frontier elements
          var recvArrayG=makeDistArray(numLocales*numLocales*CMaxSize,int);//hold the current frontier elements
          var LPG=makeDistArray(numLocales,int);// frontier pointer to current position
          var RPG=makeDistArray(numLocales*numLocales,int);//pointer to the current position can receive element
          LPG=0;
          RPG=0;

          coforall loc in Locales   {
              on loc {
                 if (xlocal(root,vertexBeginG[here.id],vertexEndG[here.id]) ) {
                   localArrayG[CMaxSize*here.id]=root;
                   LPG[here.id]=1;
                   //writeln("1 Add root=",root," into locale ",here.id);
                 }
              }
          }

          while numCurF >0 {
              coforall loc in Locales   {
                  on loc {
                   ref srcf=src;
                   ref df=dst;
                   ref nf=nei;
                   ref sf=start_i;

                   //var aggdst= newDstAggregator(int);
                   //var aggsrc= newSrcAggregator(int);
                   var LocalSet= new set(int,parSafe = true);//use set to keep the next local frontier, 
                                                             //vertex in src or srcR
                   var RemoteSet=new set(int,parSafe = true);//use set to keep the next remote frontier

                   var mystart=here.id*CMaxSize;//start index 
                   //writeln("1-1 my locale=",here.id, ",has ", LPG[here.id], " elements=",localArrayG[mystart..mystart+LPG[here.id]-1],",startposition=",mystart);
                   coforall i in localArrayG[mystart..mystart+LPG[here.id]-1] with (ref LocalSet, ref RemoteSet)  {
                            // each locale just processes its local vertices
                              if xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) {
                                  // i in src, current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               if (xlocal(j,vertexBeginG[here.id],vertexEndG[here.id])) {
                                                    LocalSet.add(j);
                                               } 
                                               if (xremote(j,HvertexBeginG[here.id],TvertexEndG[here.id])) {
                                                    RemoteSet.add(j);
                                               }
                                         }
                                  }
                              } 
                       
                              if (RemoteSet.size>0) {//there is vertex to be sent
                                  remoteNum[here.id]+=RemoteSet.size;
                                  coforall localeNum in 0..numLocales-1  { 
                                         var ind=0:int;
                                         var agg= newDstAggregator(int); 
                                         for k in RemoteSet {
                                                if (xlocal(k,vertexBeginG[localeNum],vertexEndG[localeNum])){
                                                     agg.copy(recvArrayG[localeNum*numLocales*CMaxSize+
                                                                         here.id*CMaxSize+ind] ,k);
                                                     ind+=1;
                                                     
                                                }
                                         }
                                         RPG[localeNum*numLocales+here.id]=ind;
                                         ind=0;
                                  }
                              }//end if
                   }//end coforall
                   LPG[here.id]=0;
                   if LocalSet.size>0 {
                       LPG[here.id]=LocalSet.size;
                       localNum[here.id]+=LocalSet.size;
                       var mystart=here.id*CMaxSize;
                       forall (a,b)  in zip (localArrayG[mystart..mystart+LocalSet.size-1],LocalSet.toArray()) {
                              a=b;
                       }
                       var tmp=0;
                       for i in LocalSet {
                              tmp+=1;
                       }
                   }
                   LocalSet.clear();
                   RemoteSet.clear();
                  }//end on loc
              }//end coforall loc
              coforall loc in Locales {
                  on loc {
                   var mystart=here.id*CMaxSize;
                   for i in 0..numLocales-1 {
                       if (RPG[numLocales*i+here.id]>0) {
                           localArrayG[mystart+LPG[here.id]-1..mystart+LPG[here.id]+RPG[numLocales*i+here.id]-2]=
                               recvArrayG[CMaxSize*numLocales*i+here.id*CMaxSize..
                                          CMaxSize*numLocales*i+here.id*CMaxSize+RPG[numLocales*i+here.id]-1];
                           LPG[here.id]=LPG[here.id]+RPG[numLocales*i+here.id];
                       }
                         
                   }
                  }//end on loc
              }//end coforall loc
              numCurF=0;
              for iL in 0..(numLocales-1)  {
                   if LPG[iL] >0 {
                       numCurF=1;
                       break;
                   }
              }
              RPG=0;
              cur_level+=1;
          }//end while  
          var TotalLocal=0:int;
          var TotalRemote=0:int;
          for i in 0..numLocales-1 {
            TotalLocal+=localNum[i];
            TotalRemote+=remoteNum[i];
          }
          //writeln("Local Ratio=", (TotalLocal):real/(TotalLocal+TotalRemote):real,"Total Local Access=",TotalLocal," , Total Remote Access=",TotalRemote);
          return "success";
      }//end of_d1_bfs_kernel


      proc _d1_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{
          var cur_level=0;
          var numCurF=1:int;//flag for stopping loop


          var edgeBeginG=makeDistArray(numLocales,int);//each locale's starting edge ID
          var edgeEndG=makeDistArray(numLocales,int);//each locales'ending edge ID

          var vertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var vertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src
          var HvertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var HvertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src
          var TvertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var TvertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src

          var vertexBeginRG=makeDistArray(numLocales,int);// each locales' beginning vertex ID in srcR
          var vertexEndRG=makeDistArray(numLocales,int);// each locales's ending vertex ID in srcR
          var HvertexBeginRG=makeDistArray(numLocales,int);// each locales' beginning vertex ID in srcR
          var HvertexEndRG=makeDistArray(numLocales,int);// each locales's ending vertex ID in srcR
          var TvertexBeginRG=makeDistArray(numLocales,int);// each locales' beginning vertex ID in srcR
          var TvertexEndRG=makeDistArray(numLocales,int);// each locales's ending vertex ID in srcR

          var localNum=makeDistArray(numLocales,int);// current locales's local access times
          var remoteNum=makeDistArray(numLocales,int);// current locales's remote access times
          localNum=0;
          remoteNum=0;

          var MaxBufSize=makeDistArray(numLocales,int);//temp array to calculate global max
          coforall loc in Locales   {
              on loc {
                 edgeBeginG[here.id]=src.localSubdomain().low;
                 edgeEndG[here.id]=src.localSubdomain().high;

                 vertexBeginG[here.id]=src[edgeBeginG[here.id]];
                 vertexEndG[here.id]=src[edgeEndG[here.id]];

                 vertexBeginRG[here.id]=srcR[edgeBeginG[here.id]];
                 vertexEndRG[here.id]=srcR[edgeEndG[here.id]];
                 if (here.id>0) {
                   HvertexBeginG[here.id]=vertexEndG[here.id-1];
                   HvertexBeginRG[here.id]=vertexEndRG[here.id-1];
                 } else {
                   HvertexBeginG[here.id]=-1;
                   HvertexBeginRG[here.id]=-1;
                 }
                 if (here.id<numLocales-1) {
                   TvertexEndG[here.id]=vertexBeginG[here.id+1];
                   TvertexEndRG[here.id]=vertexBeginRG[here.id+1];
                 } else {
                   TvertexEndG[here.id]=nei.size;
                   TvertexEndRG[here.id]=nei.size;
                 }

                 MaxBufSize[here.id]=vertexEndG[here.id]-vertexBeginG[here.id]+
                                     vertexEndRG[here.id]-vertexBeginRG[here.id]+2;
              }
          }
          var CMaxSize=1: int;
          for i in 0..numLocales-1 {
              if   MaxBufSize[i]> CMaxSize {
                   CMaxSize=MaxBufSize[i];
              }
          }
          var localArrayG=makeDistArray(numLocales*CMaxSize,int);//current frontier elements
          var recvArrayG=makeDistArray(numLocales*numLocales*CMaxSize,int);//hold the current frontier elements
          var LPG=makeDistArray(numLocales,int);// frontier pointer to current position
          var RPG=makeDistArray(numLocales*numLocales,int);//pointer to the current position can receive element
          LPG=0;
          RPG=0;

          coforall loc in Locales   {
              on loc {
                 if (xlocal(root,vertexBeginG[here.id],vertexEndG[here.id]) || 
                                 xlocal(root,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                   localArrayG[CMaxSize*here.id]=root;
                   LPG[here.id]=1;
                 }
              }
          }

          while numCurF >0 {
              coforall loc in Locales   {
                  on loc {
                   ref srcf=src;
                   ref df=dst;
                   ref nf=nei;
                   ref sf=start_i;

                   ref srcfR=srcR;
                   ref dfR=dstR;
                   ref nfR=neiR;
                   ref sfR=start_iR;


                   //var aggdst= newDstAggregator(int);
                   //var aggsrc= newSrcAggregator(int);
                   var LocalSet= new set(int,parSafe = true);//use set to keep the next local frontier, 
                                                             //vertex in src or srcR
                   var RemoteSet=new set(int,parSafe = true);//use set to keep the next remote frontier

                   var mystart=here.id*CMaxSize;//start index 
                   coforall i in localArrayG[mystart..mystart+LPG[here.id]-1] with (ref LocalSet, ref RemoteSet)  {
                              if xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) {
                                  // i in src, current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               if (xlocal(j,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(j,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(j);
                                               } 
                                               if (xremote(j,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(j,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(j);
                                               }
                                         }
                                  }
                              } 
                              if xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               if (xlocal(j,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(j,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(j);
                                               } 
                                               if (xremote(j,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(j,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(j);
                                               }
                                         }
                                  }
                              }
                       
                              if (RemoteSet.size>0) {//there is vertex to be sent
                                  remoteNum[here.id]+=RemoteSet.size;
                                  coforall localeNum in 0..numLocales-1  { 
                                         var ind=0:int;
                                         var agg= newDstAggregator(int); 
                                         for k in RemoteSet {
                                                if (xlocal(k,vertexBeginG[localeNum],vertexEndG[localeNum])||
                                                    xlocal(k,vertexBeginRG[localeNum],vertexEndRG[localeNum])){
                                                     agg.copy(recvArrayG[localeNum*numLocales*CMaxSize+
                                                                         here.id*CMaxSize+ind] ,k);
                                                     ind+=1;
                                                     
                                                }
                                         }
                                         RPG[localeNum*numLocales+here.id]=ind;
                                         ind=0;
                                  }
                              }//end if
                   }//end coforall
                   LPG[here.id]=0;
                   if LocalSet.size>0 {
                       LPG[here.id]=LocalSet.size;
                       localNum[here.id]+=LocalSet.size;
                       var mystart=here.id*CMaxSize;
                       forall (a,b)  in zip (localArrayG[mystart..mystart+LocalSet.size-1],LocalSet.toArray()) {
                              a=b;
                       }
                       var tmp=0;
                       for i in LocalSet {
                              tmp+=1;
                       }
                   }
                   LocalSet.clear();
                   RemoteSet.clear();
                  }//end on loc
              }//end coforall loc
              coforall loc in Locales {
                  on loc {
                   var mystart=here.id*CMaxSize;
                   for i in 0..numLocales-1 {
                       if (RPG[numLocales*i+here.id]>0) {
                           localArrayG[mystart+LPG[here.id]-1..mystart+LPG[here.id]+RPG[numLocales*i+here.id]-2]=
                               recvArrayG[CMaxSize*numLocales*i+here.id*CMaxSize..
                                          CMaxSize*numLocales*i+here.id*CMaxSize+RPG[numLocales*i+here.id]-1];
                           LPG[here.id]=LPG[here.id]+RPG[numLocales*i+here.id];
                       }
                         
                   }
                  }//end on loc
              }//end coforall loc
              numCurF=0;
              for iL in 0..(numLocales-1)  {
                   if LPG[iL] >0 {
                       numCurF=1;
                       break;
                   }
              }
              RPG=0;
              cur_level+=1;
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          var TotalLocal=0:int;
          var TotalRemote=0:int;
          for i in 0..numLocales-1 {
            TotalLocal+=localNum[i];
            TotalRemote+=remoteNum[i];
          }
          outMsg="Local Ratio="+ ((TotalLocal):real/(TotalLocal+TotalRemote):real):string+"Total Local Access="+TotalLocal:string+ " , Total Remote Access="+ TotalRemote:string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of _d1_bfs_kernel_u

      proc fo_bag_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                        LF:int,GivenRatio:real):string throws{
          var cur_level=0;
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;
          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       var switchratio=(numCurF:real)/nf.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) || (LF==0)) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR)) || (LF==0))  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              }
                           }//end coforall
                       }else {// bottom up
                           bottomup+=1;
                           forall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                              }
                           }
                           forall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF)  {
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }
                              }
                           }
                       }
                   }//end on loc
                }//end coforall loc
                cur_level+=1;
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+" number of bottom up="+(bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of fo_bag_bfs_kernel_u




      proc aligned_fo_bag_bfs_kernel_u(a_nei:[?D1] DomArray, a_start_i:[?D2] DomArray,src:[?D3] int, dst:[?D4] int,
                        a_neiR:[?D11] DomArray, a_start_iR:[?D12] DomArray,a_srcR:[?D13] DomArray, a_dstR:[?D14] DomArray, 
                        LF:int,GivenRatio:real):string throws{
          var cur_level=0;
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;
          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                   on loc {

                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=a_nei[here.id].DO.low;
                       var vertexEnd=a_nei[here.id].DO.high;
                       //var vertexBeginR=a_srcR[here.id].A[a_start_iR[here.id].A[vertexBegin]];
                       //var vertexEndR=a_srcR[here.id].A[a_start_iR[here.id].A[vertexEnd]];

                       var switchratio=(numCurF:real)/src.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) || (LF==0)) {// current edge has the vertex
                                  var    numNF=a_nei[here.id].A[i];
                                  var    edgeId=a_start_i[here.id].A[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dst[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                                  numNF=a_neiR[here.id].A[i];
                                  edgeId=a_start_iR[here.id].A[i];
                                  nextStart=edgeId;
                                  nextEnd=edgeId+numNF-1;
                                  NF=a_dstR[here.id].A[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              }
                           }//end coforall
                       }else {// bottom up
                           bottomup+=1;
                           forall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=a_nei[here.id].A[i];
                                  var    edgeId=a_start_i[here.id].A[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dst[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                                  numNF=a_neiR[here.id].A[i];
                                  edgeId=a_start_iR[here.id].A[i];
                                  nextStart=edgeId;
                                  nextEnd=edgeId+numNF-1;
                                  NF=a_dstR[here.id].A[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF)  {
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }
                              }
                           }
                       }
                   }//end on loc
                }//end coforall loc
                cur_level+=1;
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+" number of bottom up="+(bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of aligned_fo_bag_bfs_kernel_u



      proc fo_bag_bfs_kernel(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        LF:int,GivenRatio:real):string throws{
          var cur_level=0;
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;

          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;


                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];

                       var switchratio=(numCurF:real)/nf.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) || (LF==0)) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              } 
                           }//end coforall
                       }else {// bottom up
                           bottomup+=1;
                           forall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                              }
                           }
                       }
                   }//end on loc
                }//end coforall loc
                cur_level+=1;
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of fo_bag_bfs_kernel


      proc fo_set_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                        LF:int,GivenRatio:real):string throws{
          var cur_level=0;
          var SetCurF= new set(int,parSafe = true);//use set to keep the current frontier
          var SetNextF=new set(int,parSafe = true);//use set to keep the next fromtier
          SetCurF.add(root);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;

          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       var switchratio=(numCurF:real)/nf.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) ||( LF==0)) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR)) ||(LF==0))  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              }
                           }//end coforall
                       }else {//bottom up
                           bottomup+=1;
                           forall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                              }
                           }
                           forall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF)  {
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
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
                SetCurF=SetNextF;
                SetNextF.clear();
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

          return "success";
      }//end of fo_set_bfs_kernel_u

      proc fo_domain_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                        LF:int,GivenRatio:real):string throws{
          var cur_level=0;
          var SetCurF: domain(int);//use domain to keep the current frontier
          var SetNextF:domain(int);//use domain to keep the next frontier
          SetCurF.add(root);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;

          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       var switchratio=(numCurF:real)/nf.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) ||( LF==0)) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR)) || (LF==0))  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              }
                           }//end coforall
                       } else {//bottom up
                           bottomup+=1;
                           forall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                              }
                           }
                           forall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF)  {
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
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
                SetCurF=SetNextF;
                SetNextF.clear();
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of fo_domain_bfs_kernel_u

      proc fo_d1_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,GivenRatio:real):string throws{
          var cur_level=0;
          var numCurF:int=1;
          var topdown=0:int;
          var bottomup=0:int;


          var edgeBeginG=makeDistArray(numLocales,int);//each locale's starting edge ID
          var edgeEndG=makeDistArray(numLocales,int);//each locales'ending edge ID

          var vertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var vertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src
          var HvertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var TvertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src
          var BoundBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var BoundEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src

          var vertexBeginRG=makeDistArray(numLocales,int);// each locales' beginning vertex ID in srcR
          var vertexEndRG=makeDistArray(numLocales,int);// each locales's ending vertex ID in srcR
          var HvertexBeginRG=makeDistArray(numLocales,int);// each locales' beginning vertex ID in srcR
          var TvertexEndRG=makeDistArray(numLocales,int);// each locales's ending vertex ID in srcR

          var localNum=makeDistArray(numLocales,int);// current locales's local access times
          var remoteNum=makeDistArray(numLocales,int);// current locales's remote access times
          localNum=0;
          remoteNum=0;

          var MaxBufSize=makeDistArray(numLocales,int);//temp array to calculate global max
          coforall loc in Locales with (+ reduce topdown, + reduce bottomup)  {
              on loc {
                 edgeBeginG[here.id]=src.localSubdomain().low;
                 edgeEndG[here.id]=src.localSubdomain().high;

                 vertexBeginG[here.id]=src[edgeBeginG[here.id]];
                 vertexEndG[here.id]=src[edgeEndG[here.id]];

                 vertexBeginRG[here.id]=srcR[edgeBeginG[here.id]];
                 vertexEndRG[here.id]=srcR[edgeEndG[here.id]];

                 BoundBeginG[here.id]=vertexBeginG[here.id];
                 BoundEndG[here.id]=vertexEndG[here.id];

                 if (here.id>0) {
                   HvertexBeginG[here.id]=vertexEndG[here.id-1];
                   HvertexBeginRG[here.id]=vertexEndRG[here.id-1];
                   BoundBeginG[here.id]=min(vertexEndG[here.id-1]+1,nei.size-1);
              
                 } else {
                   HvertexBeginG[here.id]=-1;
                   HvertexBeginRG[here.id]=-1;
                   BoundBeginG[here.id]=0;
                 }
                 if (here.id<numLocales-1) {
                   TvertexEndG[here.id]=vertexBeginG[here.id+1];
                   TvertexEndRG[here.id]=vertexBeginRG[here.id+1];
                   BoundEndG[here.id]=max(BoundBeginG[here.id+1]-1,0);
                 } else {
                   TvertexEndG[here.id]=nei.size;
                   TvertexEndRG[here.id]=nei.size;
                   BoundEndG[here.id]=nei.size-1;
                 }

                 MaxBufSize[here.id]=vertexEndG[here.id]-vertexBeginG[here.id]+
                                     vertexEndRG[here.id]-vertexBeginRG[here.id]+2;
              }
          }
          var CMaxSize=1: int;
          for i in 0..numLocales-1 {
              if   MaxBufSize[i]> CMaxSize {
                   CMaxSize=MaxBufSize[i];
              }
          }
          var localArrayG=makeDistArray(numLocales*CMaxSize,int);//current frontier elements
          var recvArrayG=makeDistArray(numLocales*numLocales*CMaxSize,int);//hold the current frontier elements
          var LPG=makeDistArray(numLocales,int);// frontier pointer to current position
          var RPG=makeDistArray(numLocales*numLocales,int);//pointer to the current position can receive element
          LPG=0;
          RPG=0;

          coforall loc in Locales   {
              on loc {
                 if (xlocal(root,vertexBeginG[here.id],vertexEndG[here.id]) || 
                                 xlocal(root,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                   localArrayG[CMaxSize*here.id]=root;
                   LPG[here.id]=1;
                 }
              }
          }

          while numCurF >0 {
              coforall loc in Locales with (+ reduce bottomup, + reduce topdown)   {
                  on loc {
                   ref srcf=src;
                   ref df=dst;
                   ref nf=nei;
                   ref sf=start_i;

                   ref srcfR=srcR;
                   ref dfR=dstR;
                   ref nfR=neiR;
                   ref sfR=start_iR;


                   var LocalSet= new set(int,parSafe = true);//use set to keep the next local frontier, 
                                                             //vertex in src or srcR
                   var RemoteSet=new set(int,parSafe = true);//use set to keep the next remote frontier

                   var mystart=here.id*CMaxSize;//start index 



                   var   switchratio=(numCurF:real)/nf.size:real;
                   if (switchratio<GivenRatio) {//top down
                       topdown+=1;
                       forall i in localArrayG[mystart..mystart+LPG[here.id]-1] 
                                                   with (ref LocalSet, ref RemoteSet)  {
                            // each locale just processes its local vertices
                              if xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) {
                                  // i in src, current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               if (xlocal(j,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(j,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(j);
                                               } 
                                               if (xremote(j,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(j,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(j);
                                               }
                                         }
                                  }
                              } 
                              if xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               if (xlocal(j,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(j,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(j);
                                               } 
                                               if (xremote(j,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(j,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(j);
                                               }
                                         }
                                  }
                              }
                       }//end coforall
                       
                       if (RemoteSet.size>0) {//there is vertex to be sent
                                  remoteNum[here.id]+=RemoteSet.size;
                                  coforall localeNum in 0..numLocales-1  { 
                                       if localeNum != here.id{
                                         var ind=0:int;
                                         var agg= newDstAggregator(int); 
                                         for k in RemoteSet {
                                                if (xlocal(k,vertexBeginG[localeNum],vertexEndG[localeNum])||
                                                    xlocal(k,vertexBeginRG[localeNum],vertexEndRG[localeNum])){
                                                     agg.copy(recvArrayG[localeNum*numLocales*CMaxSize+
                                                                         here.id*CMaxSize+ind] ,k);
                                                     ind+=1;
                                                     
                                                }
                                         }
                                         agg.flush();
                                         RPG[localeNum*numLocales+here.id]=ind;
                                         ind=0;
                                       }
                                  }
                              }//end if
                   }// end of top down
                   else {  //bottom up
                       bottomup+=1;
                       proc FrontierHas(x:int):bool{
                            var returnval=false;
                            coforall i in 0..numLocales-1 with (ref returnval) {
                                if (xlocal(x,vertexBeginG[i],vertexEndG[i]) ||
                                    xlocal(x,vertexBeginRG[i],vertexEndRG[i])) {
                                    var mystart=i*CMaxSize;
                                    forall j in localArrayG[mystart..mystart+LPG[i]-1] with (ref returnval){
                                         if j==x {
                                            returnval=true;
                                         }
                                    }
                                }
                            }
                            return returnval;
                       }

                       forall i in BoundBeginG[here.id]..BoundEndG[here.id]
                                                   with (ref LocalSet, ref RemoteSet)  {
                          if (depth[i]==-1) {
                              if xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if FrontierHas(j) {
                                               depth[i]=cur_level+1;
                                               if (xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(i);
                                               } 
                                               if (xremote(i,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(i,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(i);
                                               }
                                         }
                                  }
                              } 
                              if xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if FrontierHas(j) {
                                               depth[i]=cur_level+1;
                                               if (xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(i);
                                               } 
                                               if (xremote(i,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(i,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(i);
                                               }
                                         }
                                  }
                              }
                          } //end if (depth[i]==-1)
                       
                       }//end coforall
                   }//end bottom up
                   if (RemoteSet.size>0) {//there is vertex to be sent
                                  remoteNum[here.id]+=RemoteSet.size;
                                  coforall localeNum in 0..numLocales-1  { 
                                       if localeNum != here.id{
                                         var ind=0:int;
                                         var agg= newDstAggregator(int); 
                                         for k in RemoteSet {
                                                if (xlocal(k,vertexBeginG[localeNum],vertexEndG[localeNum])||
                                                    xlocal(k,vertexBeginRG[localeNum],vertexEndRG[localeNum])){
                                                     agg.copy(recvArrayG[localeNum*numLocales*CMaxSize+
                                                                         here.id*CMaxSize+ind] ,k);
                                                     ind+=1;
                                                     
                                                }
                                         }
                                         agg.flush();
                                         RPG[localeNum*numLocales+here.id]=ind;
                                         ind=0;
                                       }
                                  }
                   }//end if

                   localNum[here.id]+=LPG[here.id];
                   LPG[here.id]=0;
                   if LocalSet.size>0 {
                       LPG[here.id]=LocalSet.size;
                       localNum[here.id]+=LocalSet.size;
                       var mystart=here.id*CMaxSize;
                       forall (a,b)  in zip (localArrayG[mystart..mystart+LocalSet.size-1],LocalSet.toArray()) {
                              a=b;
                       }
                   }
                   LocalSet.clear();
                   RemoteSet.clear();
                  }//end on loc
              }//end coforall loc
              coforall loc in Locales {
                  on loc {
                   var mystart=here.id*CMaxSize;
                   for i in 0..numLocales-1 {
                     if i != here.id {
                       if (RPG[here.id*numLocales+i]>0) {
                           localArrayG[mystart+LPG[here.id]..mystart+LPG[here.id]+RPG[numLocales*here.id+i]-1]=
                           recvArrayG[CMaxSize*numLocales*here.id+i*CMaxSize..
                                      CMaxSize*numLocales*here.id+i*CMaxSize+RPG[numLocales*here.id+i]-1];
                           LPG[here.id]=LPG[here.id]+RPG[numLocales*here.id+i];
                       }
                     }
                         
                   }
                  }//end on loc
              }//end coforall loc
              numCurF=0;
              for iL in 0..(numLocales-1)  {
                   if LPG[iL] >0 {
                       numCurF+=LPG[iL];
                   }
              }
              RPG=0;
              cur_level+=1;
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          var TotalLocal=0:int;
          var TotalRemote=0:int;
          for i in 0..numLocales-1 {
            TotalLocal+=localNum[i];
            TotalRemote+=remoteNum[i];
          }
          outMsg="Local Ratio="+ ((TotalLocal):real/(TotalLocal+TotalRemote):real):string +"Total Local Access="+ (TotalLocal:string) +" , Total Remote Access="+ (TotalRemote:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of fo_d1_bfs_kernel_u

      proc co_bag_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                        LF:int,GivenRatio:real):string throws{
          var cur_level=0;
          var SetCurF=  new DistBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new DistBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root);
          var numCurF=1:int;
          var bottomup=0:int;
          var topdown=0:int;

          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       var switchratio=(numCurF:real)/nf.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           coforall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) || (LF==0)) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR)) || (LF==0))  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              }
                           }//end coforall
                       }else {// bottom up
                           bottomup+=1;

                           coforall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                              }
                           }
                           coforall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF)  {
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }
                              }
                           }
                       }
                   }//end on loc
                }//end coforall loc
                cur_level+=1;
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of co_bag_bfs_kernel_u


      proc co_set_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                        LF:int,GivenRatio:real):string throws{
          var cur_level=0;
          var SetCurF= new set(int,parSafe = true);//use set to keep the current frontier
          var SetNextF=new set(int,parSafe = true);//use set to keep the next fromtier
          SetCurF.add(root);
          var numCurF=1:int;

          var bottomup=0:int;
          var topdown=0:int;

          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       var switchratio=(numCurF:real)/nf.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           coforall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) ||( LF==0)) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR)) ||(LF==0))  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              }
                           }//end coforall
                       }else {//bottom up
                           bottomup+=1;
                           coforall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                              }
                           }
                           coforall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF)  {
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
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
                SetCurF=SetNextF;
                SetNextF.clear();
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of co_set_bfs_kernel_u

      proc co_domain_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                        LF:int,GivenRatio:real):string throws{
          var cur_level=0;
          var SetCurF: domain(int);//use domain to keep the current frontier
          var SetNextF:domain(int);//use domain to keep the next frontier
          SetCurF.add(root);
          var numCurF=1:int;
          var bottomup=0:int;
          var topdown=0:int;

          while (numCurF>0) {
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       var switchratio=(numCurF:real)/nf.size:real;
                       if (switchratio<GivenRatio) {//top down
                           topdown+=1;
                           coforall i in SetCurF with (ref SetNextF) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) ||( LF==0)) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR)) || (LF==0))  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               SetNextF.add(j);
                                         }
                                  }
                              }
                           }//end coforall
                       } else {//bottom up
                           bottomup+=1;
                           coforall i in vertexBegin..vertexEnd  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF){
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
                                               SetNextF.add(i);
                                         }
                                  }

                              }
                           }
                           coforall i in vertexBeginR..vertexEndR  with (ref SetNextF) {
                              if depth[i]==-1 {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref SetNextF)  {
                                         if (SetCurF.contains(j)) {
                                               depth[i]=cur_level+1;
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
                SetCurF=SetNextF;
                SetNextF.clear();
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of co_domain_bfs_kernel_u

      proc co_d1_bfs_kernel_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,GivenRatio:real):string throws{
          var cur_level=0;
          var numCurF=1:int;//flag for stopping loop
          var topdown=0:int;
          var bottomup=0:int;


          var edgeBeginG=makeDistArray(numLocales,int);//each locale's starting edge ID
          var edgeEndG=makeDistArray(numLocales,int);//each locales'ending edge ID

          var vertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var vertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src
          var HvertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var TvertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src
          var BoundBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var BoundEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src

          var vertexBeginRG=makeDistArray(numLocales,int);// each locales' beginning vertex ID in srcR
          var vertexEndRG=makeDistArray(numLocales,int);// each locales's ending vertex ID in srcR
          var HvertexBeginRG=makeDistArray(numLocales,int);// each locales' beginning vertex ID in srcR
          var TvertexEndRG=makeDistArray(numLocales,int);// each locales's ending vertex ID in srcR

          var localNum=makeDistArray(numLocales,int);// current locales's local access times
          var remoteNum=makeDistArray(numLocales,int);// current locales's remote access times
          localNum=0;
          remoteNum=0;

          var MaxBufSize=makeDistArray(numLocales,int);//temp array to calculate global max
          coforall loc in Locales   {
              on loc {
                 edgeBeginG[here.id]=src.localSubdomain().low;
                 edgeEndG[here.id]=src.localSubdomain().high;

                 vertexBeginG[here.id]=src[edgeBeginG[here.id]];
                 vertexEndG[here.id]=src[edgeEndG[here.id]];

                 vertexBeginRG[here.id]=srcR[edgeBeginG[here.id]];
                 vertexEndRG[here.id]=srcR[edgeEndG[here.id]];

                 BoundBeginG[here.id]=vertexBeginG[here.id];
                 BoundEndG[here.id]=vertexEndG[here.id];

                 if (here.id>0) {
                   HvertexBeginG[here.id]=vertexEndG[here.id-1];
                   HvertexBeginRG[here.id]=vertexEndRG[here.id-1];
                   BoundBeginG[here.id]=min(vertexEndG[here.id-1]+1,nei.size-1);
              
                 } else {
                   HvertexBeginG[here.id]=-1;
                   HvertexBeginRG[here.id]=-1;
                   BoundBeginG[here.id]=0;
                 }
                 if (here.id<numLocales-1) {
                   TvertexEndG[here.id]=vertexBeginG[here.id+1];
                   TvertexEndRG[here.id]=vertexBeginRG[here.id+1];
                   BoundEndG[here.id]=max(BoundBeginG[here.id+1]-1,0);
                 } else {
                   TvertexEndG[here.id]=nei.size;
                   TvertexEndRG[here.id]=nei.size;
                   BoundEndG[here.id]=nei.size-1;
                 }

                 MaxBufSize[here.id]=vertexEndG[here.id]-vertexBeginG[here.id]+
                                     vertexEndRG[here.id]-vertexBeginRG[here.id]+2;
              }
          }
          var CMaxSize=1: int;
          for i in 0..numLocales-1 {
              if   MaxBufSize[i]> CMaxSize {
                   CMaxSize=MaxBufSize[i];
              }
          }
          var localArrayG=makeDistArray(numLocales*CMaxSize,int);//current frontier elements
          var recvArrayG=makeDistArray(numLocales*numLocales*CMaxSize,int);//hold the current frontier elements
          var LPG=makeDistArray(numLocales,int);// frontier pointer to current position
          var RPG=makeDistArray(numLocales*numLocales,int);//pointer to the current position can receive element
          LPG=0;
          RPG=0;

          coforall loc in Locales   {
              on loc {
                 if (xlocal(root,vertexBeginG[here.id],vertexEndG[here.id]) || 
                                 xlocal(root,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                   localArrayG[CMaxSize*here.id]=root;
                   LPG[here.id]=1;
                 }
              }
          }

          while numCurF >0 {
              coforall loc in Locales with (+ reduce topdown, + reduce bottomup)  {
                  on loc {
                   ref srcf=src;
                   ref df=dst;
                   ref nf=nei;
                   ref sf=start_i;

                   ref srcfR=srcR;
                   ref dfR=dstR;
                   ref nfR=neiR;
                   ref sfR=start_iR;


                   var LocalSet= new set(int,parSafe = true);//use set to keep the next local frontier, 
                                                             //vertex in src or srcR
                   var RemoteSet=new set(int,parSafe = true);//use set to keep the next remote frontier

                   var mystart=here.id*CMaxSize;//start index 



                   var   switchratio=(numCurF:real)/nf.size:real;
                   if (switchratio<GivenRatio) {//top down
                       topdown+=1;
                       coforall i in localArrayG[mystart..mystart+LPG[here.id]-1] 
                                                   with (ref LocalSet, ref RemoteSet)  {
                              if xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               if (xlocal(j,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(j,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(j);
                                               } 
                                               if (xremote(j,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(j,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(j);
                                               }
                                         }
                                  }
                              } 
                              if xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               if (xlocal(j,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(j,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(j);
                                               } 
                                               if (xremote(j,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(j,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(j);
                                               }
                                         }
                                  }
                              }
                       
                       }//end coforall
                       if (RemoteSet.size>0) {//there is vertex to be sent
                                  remoteNum[here.id]+=RemoteSet.size;
                                  coforall localeNum in 0..numLocales-1  { 
                                       if localeNum != here.id{
                                         var ind=0:int;
                                         var agg= newDstAggregator(int); 
                                         for k in RemoteSet {
                                                if (xlocal(k,vertexBeginG[localeNum],vertexEndG[localeNum])||
                                                    xlocal(k,vertexBeginRG[localeNum],vertexEndRG[localeNum])){
                                                     agg.copy(recvArrayG[localeNum*numLocales*CMaxSize+
                                                                         here.id*CMaxSize+ind] ,k);
                                                     ind+=1;
                                                     
                                                }
                                         }
                                         agg.flush();
                                         RPG[localeNum*numLocales+here.id]=ind;
                                         ind=0;
                                       }
                                  }
                       }//end if
                   }// end of top down
                   else {  //bottom up
                       bottomup+=1;
                       proc FrontierHas(x:int):bool{
                            var returnval=false;
                            coforall i in 0..numLocales-1 with (ref returnval) {
                                if (xlocal(x,vertexBeginG[i],vertexEndG[i]) ||
                                    xlocal(x,vertexBeginRG[i],vertexEndRG[i])) {
                                    var mystart=i*CMaxSize;
                                    for j in localArrayG[mystart..mystart+LPG[i]-1] {
                                         if j==x {
                                            returnval=true;
                                            break;
                                         }
                                    }
                                }
                            }
                            return returnval;
                       }

                       coforall i in BoundBeginG[here.id]..BoundEndG[here.id]
                                                   with (ref LocalSet, ref RemoteSet)  {
                          if (depth[i]==-1) {
                              if xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) {
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if FrontierHas(j) {
                                               depth[i]=cur_level+1;
                                               if (xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(i);
                                               } 
                                               if (xremote(i,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(i,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(i);
                                               }
                                         }
                                  }
                              } 
                              if xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBeginG[here.id]);
                                  var nextEnd=min(edgeEndG[here.id],edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  coforall j in NF with (ref LocalSet, ref RemoteSet) {
                                         if FrontierHas(j) {
                                               depth[i]=cur_level+1;
                                               if (xlocal(i,vertexBeginG[here.id],vertexEndG[here.id]) ||
                                                   xlocal(i,vertexBeginRG[here.id],vertexEndRG[here.id])) {
                                                    LocalSet.add(i);
                                               } 
                                               if (xremote(i,HvertexBeginG[here.id],TvertexEndG[here.id]) ||
                                                   xremote(i,HvertexBeginRG[here.id],TvertexEndRG[here.id])) {
                                                    RemoteSet.add(i);
                                               }
                                         }
                                  }
                              }
                          } //end if (depth[i]==-1)
                       }//end coforall
                   }// end bottom up
                       
                   if (RemoteSet.size>0) {//there is vertex to be sent
                                  remoteNum[here.id]+=RemoteSet.size;
                                  coforall localeNum in 0..numLocales-1  { 
                                       if localeNum != here.id{
                                         var ind=0:int;
                                         var agg= newDstAggregator(int); 
                                         for k in RemoteSet {
                                                if (xlocal(k,vertexBeginG[localeNum],vertexEndG[localeNum])||
                                                    xlocal(k,vertexBeginRG[localeNum],vertexEndRG[localeNum])){
                                                     agg.copy(recvArrayG[localeNum*numLocales*CMaxSize+
                                                                         here.id*CMaxSize+ind] ,k);
                                                     ind+=1;
                                                     
                                                }
                                         }
                                         agg.flush();
                                         RPG[localeNum*numLocales+here.id]=ind;
                                         ind=0;
                                       }
                                  }
                   }//end if

                   localNum[here.id]+=LPG[here.id];
                   LPG[here.id]=0;
                   if LocalSet.size>0 {
                       LPG[here.id]=LocalSet.size;
                       localNum[here.id]+=LocalSet.size;
                       var mystart=here.id*CMaxSize;
                       forall (a,b)  in zip (localArrayG[mystart..mystart+LocalSet.size-1],LocalSet.toArray()) {
                              a=b;
                       }
                   }
                   LocalSet.clear();
                   RemoteSet.clear();
                  }//end on loc
              }//end coforall loc
              coforall loc in Locales {
                  on loc {
                   var mystart=here.id*CMaxSize;
                   for i in 0..numLocales-1 {
                     if i != here.id {
                       if (RPG[here.id*numLocales+i]>0) {
                           localArrayG[mystart+LPG[here.id]..mystart+LPG[here.id]+RPG[numLocales*here.id+i]-1]=
                           recvArrayG[CMaxSize*numLocales*here.id+i*CMaxSize..
                                      CMaxSize*numLocales*here.id+i*CMaxSize+RPG[numLocales*here.id+i]-1];
                           LPG[here.id]=LPG[here.id]+RPG[numLocales*here.id+i];
                       }
                     }
                         
                   }
                  }//end on loc
              }//end coforall loc
              numCurF=0;
              for iL in 0..(numLocales-1)  {
                   if LPG[iL] >0 {
                       numCurF+=LPG[iL];
                       //break;
                   }
              }
              RPG=0;
              cur_level+=1;
          }//end while  
          var outMsg="Search Radius = "+ (cur_level+1):string;
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          outMsg="number of top down = "+(topdown:string)+ " number of bottom up="+ (bottomup:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          var TotalLocal=0:int;
          var TotalRemote=0:int;
          for i in 0..numLocales-1 {
            TotalLocal+=localNum[i];
            TotalRemote+=remoteNum[i];
          }
          outMsg="Local Ratio="+ ((TotalLocal):real/(TotalLocal+TotalRemote):real):string + "Total Local Access=" + (TotalLocal:string) +" Total Remote Access=" + (TotalRemote:string);
          smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          return "success";
      }//end of co_d1_bfs_kernel_u

      proc return_depth(): string throws{
          var depthName = st.nextName();
          var depthEntry = new shared SymEntry(depth);
          st.addEntry(depthName, depthEntry);
          //try! st.addEntry(vertexName, vertexEntry);

          var depMsg =  'created ' + st.attrib(depthName);
          //var lrepMsg =  'created ' + st.attrib(levelName) + '+created ' + st.attrib(vertexName) ;
          return depMsg;

      }

      if (Directed!=0) {
              var ratios:string;
               (rootN,ratios)=
                   restpart.splitMsgToTuple(2);
              root=rootN:int;
              var GivenRatio=ratios:real;
              if (RCMFlag>0) {
                  root=0;
              }
              depth[root]=0;


            //   var ag = new owned SegGraphDW(Nv,Ne,Directed,Weighted,srcN,dstN,
            //                      startN,neighbourN,vweightN,eweightN, st);
            //   fo_bag_bfs_kernel(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,1,GivenRatio);
              fo_bag_bfs_kernel(
                  toSymEntry(ag.getNEIGHBOR(), int).a,
                  toSymEntry(ag.getSTART_IDX(), int).a,
                  toSymEntry(ag.getSRC(), int).a,
                  toSymEntry(ag.getDST(), int).a,
                  1, GivenRatio);

               repMsg=return_depth();

      }
      else {
              var ratios:string;
              (rootN, ratios)=
                   restpart.splitMsgToTuple(2);
              root=rootN:int;
              if (RCMFlag>0) {
                  root=0;
              }
              depth=-1;
              depth[root]=0;
              var Flag=0:int;
              var GivenRatio=ratios:real;
              if (GivenRatio <0  ) {//do default call
                  GivenRatio=-1.0* GivenRatio;
                  fo_bag_bfs_kernel_u(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,
                      1, GivenRatio
                  );
                  
                  timer.stop();
                  var outMsg= "graph BFS takes "+timer.elapsed():string+" for fo_bag version";
                  smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  aligned_fo_bag_bfs_kernel_u(
                      toDomArraySymEntry(ag.getA_NEIGHBOR()).domary,
                      toDomArraySymEntry(ag.getA_START_IDX()).domary,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toDomArraySymEntry(ag.getA_NEIGHBOR_R()).domary,
                      toDomArraySymEntry(ag.getA_START_IDX_R()).domary,
                      toDomArraySymEntry(ag.getA_SRC_R()).domary,
                      toDomArraySymEntry(ag.getA_DST_R()).domary,
                      1, GivenRatio
                  );
                  outMsg= "graph BFS takes "+timer.elapsed():string+" for aligned_fo_bag version";
                  smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
                  repMsg=return_depth();
 
              } else {// do batch test
                  depth=-1;
                  depth[root]=0;
                  timer.stop();
                  timer.clear();
                  timer.start();
 
                  co_d1_bfs_kernel_u(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a,
                      GivenRatio
                  );
                  timer.stop();
                  var outMsg= "graph BFS takes "+timer.elapsed():string+ " for Co D Hybrid version";
                  smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

                  /*
                  depth=-1;
                  depth[root]=0;
                  Flag=1;
                  timer.clear();
                  timer.start();
                  co_d1_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,2.0);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Co D TopDown version $$$$$$$$$$$$$$$$$$");


                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=1;
                  co_bag_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Co Bag L version $$$$$$$$$$$$$$$$$$");

                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=0;
                  co_bag_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Co Bag G version $$$$$$$$$$$$$$$$$$");


                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=1;
                  co_set_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Co Set L version $$$$$$$$$$$$$$$$$$");

                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=0;
                  co_set_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Co Set G version $$$$$$$$$$$$$$$$$$");


                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=1;
                  co_domain_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Co Domain L version $$$$$$$$$$$$$$$$$$");

                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=0;
                  co_domain_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Co Domain G version $$$$$$$$$$$$$$$$$$");


                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  fo_d1_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for D Hybrid version $$$$$$$$$$$$$$$$$$");

                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  fo_d1_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,2.0);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for D TopDown version $$$$$$$$$$$$$$$$$$");


                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=1;
                  fo_bag_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Bag L version $$$$$$$$$$$$$$$$$$");

                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=0;
                  fo_bag_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Bag G version $$$$$$$$$$$$$$$$$$");


                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=1;
                  fo_set_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Set L version $$$$$$$$$$$$$$$$$$");

                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=0;
                  fo_set_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Set G version $$$$$$$$$$$$$$$$$$");


                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=1;
                  fo_domain_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Domain L version $$$$$$$$$$$$$$$$$$");

                  depth=-1;
                  depth[root]=0;
                  timer.clear();
                  timer.start();
                  Flag=0;
                  fo_domain_bfs_kernel_u(ag.neighbour.a, ag.start_i.a,ag.src.a,ag.dst.a,
                           ag.neighbourR.a, ag.start_iR.a,ag.srcR.a,ag.dstR.a,Flag,GivenRatio);
                  timer.stop();
                  writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), " for Domain G version $$$$$$$$$$$$$$$$$$");
                  */

                  repMsg=return_depth();
              }//end of batch test

      }
      timer.stop();
      //writeln("$$$$$$$$$$$$$$$$$ graph BFS takes ",timer.elapsed(), "$$$$$$$$$$$$$$$$$$");
      var outMsg= "graph BFS takes "+timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    use CommandMap;
    registerFunction("segmentedGraphBFS", segBFSMsg);
 }


