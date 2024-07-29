module DiameterMsg {
  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  use ServerErrorStrings;
  use ServerConfig;
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use RandArray;
  use IO;
  use LinearAlgebra;

  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use ArgSortMsg;
  use Time;
  use CommAggregation;
  use Sort;
  use Map;
  use DistributedDeque;

  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;

  use Set;

  use MemDiagnostics;

  // private config const logLevel = ServerConfig.logLevel;
  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  
  config const start_min_degree = 1000000;
  var tmpmindegree=start_min_degree;

  const JumpSteps=6;
  const FirstOrderIters=4;
  const SecondOrderIters=6;
  var  ORDERH:int=512;
  const LargeScale=1000000;
  const LargeEdgeEfficiency=100;
  const MultiLocale=1;

  private proc xlocal(x :int, low:int, high:int):bool {
    return low<=x && x<=high;
  }

  private proc xremote(x :int, low:int, high:int):bool {
    return !xlocal(x, low, high);
  }

  proc segDiameterMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
    // Get the values passeed to Python and now, Chapel. 
    //var (n_verticesN, n_edgesN, directedN, weightedN, graphEntryName, restpart) = payload.splitMsgToTuple(6);
    //var msgArgs = parseMessageArgs(payload, argSize);

    var n_verticesN=msgArgs.getValueOf("NumOfVertices");
    var n_edgesN=msgArgs.getValueOf("NumOfEdges");
    var directedN=msgArgs.getValueOf("Directed");
    var weightedN=msgArgs.getValueOf("Weighted");
    var graphEntryName=msgArgs.getValueOf("GraphName");


    // Initialize the variables with graph data. 
    var Nv = n_verticesN:int; 
    var Ne = n_edgesN:int; 
    var Directed = directedN:int; 
    var Weighted = weightedN:int; 
    
    // Declare the other variables to be used. 
    var CCName:string; 
    var srcN, dstN, startN, neighbourN, vweightN, eweightN, rootN:string;
    var srcRN, dstRN, startRN, neighbourRN:string;
    
    // Initialize the distributed visited array. 
    var visited = makeDistArray(Nv, int); 
    
    // Initialize the timer to track the execution of the implementation. 
    // var timer:stopwatch;

    // Get our graph information. 
    var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
    var ag = gEntry.graph;


/*
      proc bfs (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                       root:int):int throws{
          var cur_level=0;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;
          var update=false:bool;
          var depth:[D1] int;
          depth=-1;
          depth[root]=0;
          while (numCurF>0) {
                update=false;
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup, ref depth,ref update) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF, ref update) {
                              var branchnum=0:int;
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update ){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               update=true;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               update=true;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              }
                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if ( update) {
                    cur_level+=1;
                }
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
                //writeln("BFS tree level=",cur_level);
          }//end while  


          return cur_level;
      }//end of bfs



      proc tree_bfs (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                       root:int, father:[?D15] int):int throws{
          var cur_level=0;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;
          var update=false:bool;
          var depth:[D1] int;
          depth=-1;
          depth[root]=0;
          while (numCurF>0) {
                update=false;
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup, ref depth,ref update) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF, ref update) {
                              var branchnum=0:int;
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update ){
                                         if (depth[j]==-1 && (father[i]==j ||father[j]==i)) {
                                               depth[j]=cur_level+1;
                                               update=true;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update)  {
                                         if (depth[j]==-1 && (father[i]==j ||father[j]==i)) {
                                               depth[j]=cur_level+1;
                                               update=true;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              }
                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if ( update) {
                    cur_level+=1;
                }
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
                //writeln("BFS tree level=",cur_level);
          }//end while  

          return cur_level;
      }//end of bfs


 
*/

      proc Stree_bfs (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int, srcR:[?D13] int, dstR:[?D14] int, 
                       root:int,removed:[?D15] bool, father:[?D16] int,printflag=false:bool):(int,int) throws {
          var cur_level=0;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          var SetRemoved=  new distBag(int,Locales); //use bag to keep the removed vertices
          var SetNextRemoved=  new distBag(int,Locales); //use bag to keep the next removed vertices
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var update=false:bool;
          var depth:[D1] int;
          depth=-1;
          depth[root]=0;
          var maxv:int=-1;
          writeln("The tree root=",root);
          if removed[root] {
              writeln("Vertex ", root, " has been removed, WRONG!!!");
          }
          while (numCurF>0) {
                update=false;
                coforall loc in Locales  with (ref SetNextF, ref depth,ref update,ref maxv,
                             ref SetRemoved, ref SetNextRemoved) {
                   on loc {

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//
                           forall i in SetCurF with (ref SetNextF,ref depth, ref update, ref maxv,
                              ref SetRemoved, ref SetNextRemoved ) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nei[i];
                                  var    edgeId=start_i[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dst[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref depth, ref update,ref maxv ){
                                         if (depth[j]==-1 ) {
                                               if removed[j] {
                                                   SetRemoved.add(j,here.id); 
                                                   depth[j]=cur_level+1;
                                               } else {
                                                   if (father[j]==i ||father[i]==j) {
                                                       update=true;
                                                       SetNextF.add(j,here.id);
                                                       maxv=j;
                                                       if (printflag) {
                                                            write("current level is ",cur_level+1,"," );
                                                            if father[j]==i {
                                                                writeln(j,"->",i);
                                                            } else {
                                                                writeln(i,"->",j);
                                                            }
                                                       }
                                                       depth[j]=cur_level+1;
                                                   }
                                               }
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=neiR[i];
                                  var    edgeId=start_iR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dstR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref depth,ref update,ref maxv)  {
                                         if (depth[j]==-1) {
                                               if removed[j] {
                                                   SetRemoved.add(j,here.id); 
                                                   depth[j]=cur_level+1;
                                               } else {
                                                   if (father[j]==i ||father[i]==j) {
                                                       update=true;
                                                       SetNextF.add(j,here.id);
                                                       maxv=j;
                                                       if (printflag) {
                                                            write("current level is ",cur_level+1,"," );
                                                            if father[j]==i {
                                                                writeln(j,"->",i);
                                                            } else {
                                                                writeln(i,"->",j);
                                                            }
                                                       }
                                                       depth[j]=cur_level+1;
                                                   }
                                               }
                                         }
                                  }
                              }

                              //handle the removed vertices
                              while SetRemoved.getSize()>0 {
                                   forall k in SetRemoved  with (ref SetNextF, ref depth, ref update, 
                                                                 ref maxv, ref SetNextRemoved) {
                                      if ((xlocal(k,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                          var    numNF=nei[k];
                                          var    edgeId=start_i[k];
                                          var nextStart=max(edgeId,edgeBegin);
                                          var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                          ref NF=dst[nextStart..nextEnd];
                                          forall j in NF with (ref SetNextF,ref depth, ref update, 
                                                               ref maxv, ref SetNextRemoved){
                                                 if (depth[j]==-1 ) {
                                                       if removed[j] {
                                                            SetNextRemoved.add(j,here.id); 
                                                       } else {
                                                           if (//father[j]==k ||father[k]==j ||
                                                               father[j]==i ||father[i]==j ) {
                                                               update=true;
                                                               SetNextF.add(j,here.id);
                                                               maxv=j;
                                                               if (printflag) {
                                                                   write("current level is ",cur_level+1,"," );
                                                                   if father[j]==i {
                                                                       writeln(j,"->",i);
                                                                   } else {
                                                                       writeln(i,"->",j);
                                                                   }
                                                               }
                                                               depth[j]=cur_level+1;
                                                           }
                                                       }
                                                 }
                                          }
                                      } 
                                      if ((xlocal(k,vertexBeginR,vertexEndR))  )  {
                                          var    numNF=neiR[k];
                                          var    edgeId=start_iR[k];
                                          var nextStart=max(edgeId,edgeBegin);
                                          var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                          ref NF=dstR[nextStart..nextEnd];
                                          forall j in NF with (ref SetNextF,ref depth, ref update,
                                                               ref maxv, ref SetNextRemoved)  {
                                                 if (depth[j]==-1 ) {
                                                       if removed[j] {
                                                            SetRemoved.add(j,here.id);
                                                       } else {
                                                           if (//father[j]==k ||father[k]==j ||
                                                               father[j]==i ||father[i]==j ) {
                                                               update=true;
                                                               SetNextF.add(j,here.id);
                                                               maxv=j;
                                                               if (printflag) {
                                                                   write("current level is ",cur_level+1,"," );
                                                                   if father[j]==i {
                                                                       writeln(j,"->",i);
                                                                   } else {
                                                                       writeln(i,"->",j);
                                                                   }
                                                               }
                                                               depth[j]=cur_level+1;
                                                           }
                                                       }
                                                 }
                                          }
                                      }
                                 }//end forall
                                 SetRemoved<=>SetNextRemoved;
                                 SetNextRemoved.clear();
                              }// end while


                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if (update) {
                    cur_level+=1;
                    //writeln("Tree BFS, current level =",cur_level);
                }
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
          }//end while  


          return (cur_level,maxv);
      }//end of bfs


/*

      proc bfs_maxv (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                       root:int):(int,int) throws{
          var cur_level=0;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;
          var update=false:bool;
          var depth:[D1] int;
          depth=-1;
          depth[root]=0;
          var maxv:int=-1;
          while (numCurF>0) {
                update=false;
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup, ref root, ref src, ref depth,ref update,ref maxv) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF, ref update,ref maxv) {
                              var branchnum=0:int;
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update,ref maxv ){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               update=true;
                                               SetNextF.add(j,here.id);
                                               maxv=j;
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update,ref maxv)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               update=true;
                                               SetNextF.add(j,here.id);
                                               maxv=j;
                                         }
                                  }
                              }
                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if ( update) {
                    cur_level+=1;
                }
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
                //writeln("BFS tree level=",cur_level);
          }//end while  

          return (cur_level,maxv);
      }//end of bfs


*/


      proc Sbfs_maxv (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                      neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int,
                      root:int,removed:[?D15] bool, ref father:[?D16] int, setfather:bool):(int,int) throws{
          var cur_level=0;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          var SetRemoved=  new distBag(int,Locales); //use bag to keep the removed vertices
          var SetNextRemoved=  new distBag(int,Locales); //use bag to keep the next removed vertices
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var update=false:bool;
          var depth:[D1] int;
          depth=-1;
          depth[root]=0;
          var maxv:int=-1;
          if removed[root] {
             writeln("Vertex ", root, " has been removed, WRONG!!!");
          }
          while (numCurF>0) {
                update=false;
                coforall loc in Locales  with (ref SetNextF, ref depth,ref update,ref maxv,
                             ref SetRemoved, ref SetNextRemoved,ref father) {
                   on loc {
                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//
                           forall i in SetCurF with (ref SetNextF, ref update, ref maxv,
                              ref SetRemoved, ref SetNextRemoved, ref father) {
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nei[i];
                                  var    edgeId=start_i[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dst[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update,ref maxv,ref father ){
                                         if (depth[j]==-1) {
                                               if removed[j] {
                                                   SetRemoved.add(j,here.id); 
                                                   //writeln("Found removed vertex ", j);
                                               } else {
                                                   update=true;
                                                   SetNextF.add(j,here.id);
                                                   maxv=j;
                                                   if setfather {
                                                       father[j]=i;
                                                   }
                                               }
                                               depth[j]=cur_level+1;
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=neiR[i];
                                  var    edgeId=start_iR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dstR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update,ref maxv, ref father)  {
                                         if (depth[j]==-1) {
                                               if removed[j] {
                                                   SetRemoved.add(j,here.id); 
                                                   //writeln("Found removed vertex ", j);
                                               } else {
                                                   update=true;
                                                   SetNextF.add(j,here.id);
                                                   maxv=j;
                                                   if setfather {
                                                       father[j]=i;
                                                   }
                                               }
                                               depth[j]=cur_level+1;
                                         }
                                  }
                              }



                              //handle the removed vertices
                              while (SetRemoved.getSize()>0) {
                                   forall k in SetRemoved with (ref SetNextF, ref update, ref maxv, ref SetNextRemoved) {
                                      if ((xlocal(k,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                          var    numNF=nei[k];
                                          var    edgeId=start_i[k];
                                          var nextStart=max(edgeId,edgeBegin);
                                          var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                          ref NF=dst[nextStart..nextEnd];
                                          forall j in NF with (ref SetNextF,ref update, ref maxv, 
                                                               ref SetNextRemoved,ref father){
                                                 if (depth[j]==-1) {
                                                       if removed[j] {
                                                           SetNextRemoved.add(j,here.id); 
                                                       } else {
                                                           update=true;
                                                           SetNextF.add(j,here.id);
                                                           maxv=j;
                                                           if setfather {
                                                               father[j]=i;
                                                           }
                                                       }
                                                       depth[j]=cur_level+1;
                                                 }
                                          }
                                      } 
                                      if ((xlocal(k,vertexBeginR,vertexEndR))  )  {
                                          var    numNF=neiR[k];
                                          var    edgeId=start_iR[k];
                                          var nextStart=max(edgeId,edgeBegin);
                                          var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                          ref NF=dstR[nextStart..nextEnd];
                                          forall j in NF with (ref SetNextF,ref update,ref maxv,
                                                               ref SetNextRemoved,ref father)  {
                                                 if (depth[j]==-1) {
                                                       if removed[j] {
                                                           SetRemoved.add(j,here.id);
                                                           //writeln("Found removed vertex ", j);
                                                       } else {
                                                           update=true;
                                                           SetNextF.add(j,here.id);
                                                           maxv=j;
                                                           if setfather {
                                                               father[j]=i;
                                                           }
                                                       }
                                                       depth[j]=cur_level+1;
                                                 }
                                          }
                                      }
                                   }//end forall
                                   SetRemoved<=>SetNextRemoved;
                                   SetNextRemoved.clear();
                              }//end while




                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if ( update) {
                    cur_level+=1;
                }
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
          }//end while  


          return (cur_level,maxv);
      }//end of bfs



/*
      proc c_diameter (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                       root:int,gdiameter:int):int throws{
          var cur_level=0;
          var diameter=gdiameter;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;
          var update=false:bool;
          var depth:[D1] int;
          depth=-1;
          var father=depth;
          father[root]=-1;
          depth[root]=0;
          var leaf:[D1] bool;
          leaf=true;
          var branch:[D1] bool;
          branch=false;
          var maxdist: atomic int;
          maxdist.write(0);
          var maxvertex: int=-1;
          var maxvx=-1:int;
          var maxvy=-1:int;
          record Mergedist {
                var vx: atomic int;
                var vxvertex:int;
                var vy:atomic int;
                var vyvertex:int;
          }
          var length:[D1] Mergedist;
          forall i in D1 {
                length[i].vx.write(0);
                length[i].vy.write(0);
                length[i].vxvertex=-1;
                length[i].vyvertex=-1;
          }
          while (numCurF>0) {
                update=false;
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup, ref root, ref src, ref depth,ref update) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF, ref update) {
                              var branchnum=0:int;
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update, ref branchnum){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               father[j]=i;
                                               leaf[i]=false;
                                               update=true;
                                               branchnum+=1;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update,ref branchnum)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               leaf[i]=false;
                                               father[j]=i;
                                               update=true;
                                               branchnum+=1;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              }
                              if branchnum>1 {
                                  branch[i]=true;
                              }
                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if ( update) {
                    cur_level+=1;
                }
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
                //writeln("BFS tree level=",cur_level);
          }//end while  
          //writeln("After BFS");
          diameter=max(diameter,cur_level);
          //unmark some branch vertex

          var LeafSet=new set(int,parSafe = true);
          forall i in D1 with (ref maxdist, ref maxvertex,ref maxvx,ref maxvy,ref diameter,ref LeafSet) {
              if leaf[i]==true  {
                   if depth[i] <diameter/2 {
                       leaf[i]=false;
                   } else {
                      LeafSet.add(i);
                   }
          }

          for i in LeafSet {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update ){
                                         if (leaf[j]==true) && depth[j]==depth[i] {
                                               leaf[j]=false;
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update)  {
                                         if (depth[j]==depth[i] && leaf[j]==true) {
                                               leaf[j]=false;
                                         }
                                  }
                              }
          }
          for i in D1 {
                   if ( leaf[i]==true) && depth[i] >diameter/2  {
                            var xx=bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, i);
                            writeln("Search from ",i," and the height is ",xx," current diamter is ",diameter);
                            diameter=max(diameter, xx);
                   }
              }//end if
          }


          return diameter;
          //return max(cur_level,xx);
      }//end of component diameter






      proc c_farthest (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                       root:int,gdiameter:int,numfarv:int):int throws{
          var cur_level=0;
          var diameter=gdiameter;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;
          var update=false:bool;
          var depth:[D1] int;
          depth=-1;
          var father=depth;
          father[root]=-1;
          depth[root]=0;
          var leaf:[D1] bool;
          leaf=true;
          var branch:[D1] bool;
          branch=false;
          var maxdist: atomic int;
          maxdist.write(0);
          var maxvertex: int=-1;
          var maxvx=-1:int;
          var maxvy=-1:int;
          record Mergedist {
                var vx: atomic int;
                var vxvertex:int;
                var vy:atomic int;
                var vyvertex:int;
          }
          var length:[D1] Mergedist;
          forall i in D1 {
                length[i].vx.write(0);
                length[i].vy.write(0);
                length[i].vxvertex=-1;
                length[i].vyvertex=-1;
          }
          while (numCurF>0) {
                update=false;
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup, ref root, ref src, ref depth,ref update) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF, ref update) {
                              var branchnum=0:int;
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update, ref branchnum){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               father[j]=i;
                                               leaf[i]=false;
                                               update=true;
                                               branchnum+=1;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update,ref branchnum)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               leaf[i]=false;
                                               father[j]=i;
                                               update=true;
                                               branchnum+=1;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              }
                              if branchnum>1 {
                                  branch[i]=true;
                              }
                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if ( update) {
                    cur_level+=1;
                }
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
                //writeln("BFS tree level=",cur_level);
          }//end while  
          //writeln("After BFS");
          diameter=max(diameter,cur_level);
          writeln("The height from root ", root, " is ", cur_level);
          var numiter:int=1;
          for i in D1  {
              if depth[i] ==cur_level {
                            var xx=bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, i);
                  writeln("search from vertex ",i,", its leaf flag is ", leaf[i], ", the tree height is ",xx, ", the current diameter is ", diameter,", it is the ",numiter," farthest vertex");
                            diameter=max(diameter, xx);
                  numiter+=1;
                  if numiter>numfarv {
                       break;
                  }
              }//end if
          }
          return diameter;
          //return max(cur_level,xx);
      }//end of component diameter

*/
/*
      proc c_lu (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                 neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                 root:int,plbound:int,pubound:int,iternum:int,varray:[?D15] int, f:[?D16]int):(int,int) throws{
          var i=0:int;
          var dindex:int=0;
          var maxv:int;
          var tmpr=root;
          var lbound=0;
          var ubound=999999;

          var diameter=lbound;
          var removed:[D1] bool;
          removed=false;
          var father:[D1] int;
          father=-1;

          var graphheight0,graphheight1,graphheight2:int;
          var graphvertex0,graphvertex1,graphvertex2:int;
          var treeheight0,treeheight1,treeheight2:int;
          var treevertex0,treevertex1,treevertex2:int;

          while i<iternum {
          (graphheight0,graphvertex0)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, varray[i],removed,father,true );
          writeln("iteration ",i,","," From vertex ", varray[i]," Step 0, Graph BFS height =",graphheight0, ", farest vertex is ", graphvertex0);

          (treeheight0,treevertex0)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, varray[i],removed,father,true);
          writeln("iteration ",i,","," From vertex ", varray[i]," Step 0, Tree BFS height =",treeheight0, ", farest vertex is ", treevertex0);
          if treeheight0!=graphheight0 {
               writeln("iteration ",i,","," Step 0 height is not equal, WRONG!!!");
          }

          (treeheight1,treevertex1)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, treevertex0,removed,father,true);
          writeln("iteration ",i,",","From vertex ", treevertex0," Step 0-1, Tree BFS height =",treeheight1, ", farest vertex is ", treevertex1);

          (treeheight2,treevertex2)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, treevertex1,removed,father,true);
          writeln("iteration ",i,",","From vertex ", treevertex1," Step 0-2, Tree BFS height =",treeheight2, ", farest vertex is ", treevertex2);

          writeln("iteration ",i,",","GraphHeight0=",graphheight0,"Tree height0=",treeheight0," Tree height1=",treeheight1," Tree height2=",treeheight2);
          if graphheight0>min(treeheight2,treeheight1) {
              writeln("WRONG!!!, graph height is larger than tree height");
          }


          father=-1;
          (graphheight1,graphvertex1)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex0,removed,father,true );
          writeln("iteration ",i,",","From vertex ", varray[i]," Step 1, Graph BFS height =",graphheight1, ", root is ",graphvertex0, ", farest vertex is ", graphvertex1);


          (treeheight0,treevertex0)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex0,removed,father,true);
          writeln("iteration ",i,",","From vertex ", varray[i]," Step 1, Tree BFS height =",treeheight0, ", root is ",graphvertex0,", farest vertex is ", treevertex0);
          if treeheight0!=graphheight1 {
               writeln("Step 1 height is not equal, WRONG!!!");
          }

          (treeheight1,treevertex1)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, treevertex0,removed,father,true);
          writeln("iteration ",i,",","From vertex ", varray[i]," Step 1-1, Tree BFS height =",treeheight1, ", root is ",treevertex0,", farest vertex is ", treevertex1);

          (treeheight2,treevertex2)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, treevertex1,removed,father,true);
          writeln("iteration ",i,",","From vertex ", varray[i]," Step 1-2, Tree BFS height =",treeheight2, ", root is ",treevertex1,", farest vertex is ", treevertex2);

          writeln("iteration ",i,",","GraphHeight1=",graphheight1,"Tree height0=",treeheight0," Tree height1=",treeheight1," Tree height2=",treeheight2);
          if graphheight1>min(treeheight2,treeheight1) {
              writeln("WRONG!!!, graph height is larger than tree height");
          }



          father=-1;
          (graphheight2,graphvertex2)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex1,removed,father,true );
          writeln("iteration ",i,",","From vertex ", varray[i]," Step 2, Graph BFS height =",graphheight2, ", root is ",graphvertex1, ", farest vertex is ", graphvertex2);


          (treeheight0,treevertex0)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex1,removed,father,true);
          writeln("iteration ",i,",","From vertex ", varray[i]," Step 2, Tree BFS height =",treeheight0, ", root is ",graphvertex1,", farest vertex is ", treevertex0);
          if treeheight0!=graphheight2 {
               writeln("Step 1 height is not equal, WRONG!!!");
          }

          (treeheight1,treevertex1)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, treevertex0,removed,father,true);
          writeln("iteration ",i,",","From vertex ", varray[i]," Step 2-1, Tree BFS height =",treeheight1, ", root is ",treevertex0,", farest vertex is ", treevertex1);

          (treeheight2,treevertex2)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, treevertex1,removed,father,true);
          writeln("iteration ",i,",","From vertex ", varray[i]," Step 2-2, Tree BFS height =",treeheight2, ", root is ",treevertex1,", farest vertex is ", treevertex2);

          writeln("iteration ",i,",","GraphHeight2=",graphheight2,", Tree height0=",treeheight0,", Tree height1=",treeheight1,", Tree height2=",treeheight2);
          if graphheight2>min(treeheight2,treeheight1) {
              writeln("WRONG!!!, graph height is larger than tree height");
          }
          i=i+1;
          father=-1;
          }
          return (0,0);
      }


*/


      proc c_lu (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                 neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                 root:int,plbound:int,pubound:int,iternum:int,varray:[?D15] int, f:[?D16]int):(int,int) throws{
          var i=0:int;
          var dindex:int=0;
          var maxv:int;
          var tmpr=root;
          var lbound=0;
          var ubound=999999;

          var diameter=lbound;
          var removed:[D1] bool;
          removed=false;
          var visited=removed;
          var father,oldfather:[D1] int;
          var keep:[D1] atomic int;
          forall i in D1 {
             keep[i].write(-1);
          }
          forall i in D1 with (ref keep, ref removed) {
             if nei[i]+neiR[i]==1 {
                 if nei[i]==1 {
                     var c=dst[start_i[i]];
                     var old=keep[c].read();
                     if (old!=-1) {
                        removed[i]=true;
                     } else {
                          while old==-1 {
                               keep[c].compareAndSwap(-1,i);
                               old=keep[c].read();                   
                          }
                          if old !=i {
                             removed[i]=true;
                          }
                     }
                 } else {
                     if neiR[i]==1 {
                         var c=dstR[start_iR[i]];
                         var old=keep[c].read();
                         if (old!=-1) {
                            removed[i]=true;
                         } else {
                              while old==-1 {
                                  keep[c].compareAndSwap(-1,i);
                                  old=keep[c].read();                   
                              }
                              if old !=i {
                                 removed[i]=true;
                              }
                         }
                     }
                 } 

             }//end if 
          }// end forall

          var graphheight0,graphheight1,graphheight2:int;
          var graphvertex0,graphvertex1,graphvertex2:int;
          var treeheight0,treeheight1,treeheight2:int;
          var treevertex0,treevertex1,treevertex2:int;

          var tmproot,tmpgraphheight0,tmpgraphheight1,tmpgraphheight2:int;
          var tmpgraphvertex0,tmpgraphvertex1,tmpgraphvertex2:int;
          var tmptreeheight0,tmptreeheight1,tmptreeheight2:int;
          var tmptreevertex0,tmptreevertex1,tmptreevertex2:int;

          tmpr=-1;
          while (i<iternum){
               while (varray.size>dindex) {
                   if (removed[varray[dindex]] || visited[varray[dindex]] ) {
                       dindex=dindex+1;
                   } else {
                       break;
                   }
               }
               if dindex+1>=varray.size {
                        break;
               }

               if tmpr==-1 {
                    tmpr=varray[dindex];
               }
               father=-1;
               //initial the two steps in one complete iteration
               (graphheight0,graphvertex0)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, tmpr,removed,father,true );
               visited[tmpr]=true;
               tmpr=-1;
               if (visited[graphvertex0]) {
                    dindex=dindex+1;
                    i=i+1;
                    continue;
               }
               writeln("Iteration ",i,", Step 0, Graph BFS height =",graphheight0, ", farest vertex is ", graphvertex0);

               (treeheight1,treevertex1)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex0,removed,father,false);

               oldfather=father;
               father=-1;
               (graphheight1,graphvertex1)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex0,removed,father,true);
               visited[graphvertex0]=true;
               writeln("Iteration ",i,", Step 1, Tree BFS height =",treeheight1,", Graph BFS height =", graphheight1, 
                  ",  Farest tree and graph vertices ",treevertex1,", ",graphvertex1);

               if (visited[graphvertex1]) {
                    dindex=dindex+1;
                    i=i+1;
                    continue;
               }
               if (treeheight1 == graphheight1) {
                  lbound=max(lbound,graphheight1);
                  ubound=lbound;
                  i=iternum;
                  break;
               } else {
                   if (treeheight1 < graphheight1) {
                       writeln("Tree height ", treeheight1, " is less than the graph height ",graphheight1, " WRONG!!!");
                       writeln("The Tree looks like this");
                       (tmptreeheight1,tmptreevertex1)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex0,removed,oldfather,true);

                       writeln("Tree height ", tmptreeheight1, " The farest vertex is ", tmptreevertex1);
                       writeln("The BFS Tree looks like this");
                       (tmptreeheight1,tmptreevertex1)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex0,removed,father,true);
                       writeln("Tree height ", tmptreeheight1, " The farest vertex is ", tmptreevertex1);

                   }
                  lbound=max(lbound,graphheight1);
                  ubound=min(ubound,treeheight1,2*graphheight0,2*graphheight1);
               }

              //check the second BFS step in one complete iteration
              (treeheight2,treevertex2)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex1,removed,father,false);

              oldfather=father;
              father=-1;
              (graphheight2,graphvertex2)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex1,removed,father,true);
              visited[graphvertex1]=true;

              if (treeheight2 < graphheight2) {
                   writeln("Tree height ", treeheight2, " is less than the graph height ",graphheight2, " WRONG!!!");
              }

              writeln("Iteration ",i,", Step 2, Tree BFS height =",treeheight2,", Graph BFS height =", graphheight2, 
                      ", Farest tree are graph vertices ",treevertex2,", ",graphvertex2);
              if (treeheight2 == graphheight2) {
                  lbound=max(lbound,graphheight2);
                  ubound=lbound;
                  break;
              } else {
                  lbound=max(lbound,graphheight2);
                  ubound=min(ubound, treeheight2,2*graphheight2);
              }
              writeln("Iteration ",i," lbound=",lbound," ubound=",ubound);
              if lbound>=ubound {
                            i=iternum;
                            break;
              }
              //if graphheight2 > graphheight1  {
              //    removed[graphvertex0]=true;
              //    writeln("Iteration ",i,", Removed the No. 0 farest vertex ",graphvertex0);
              //} 
              if visited[graphvertex2]==false {
                  tmpr=graphvertex2;
              }
              /*
              //while (graphheight2 == graphheight1) && (i<iternum)   {
              if (graphheight2 == graphheight1) && (i<iternum)   {
                  var tmpremoved=removed;
                  tmpremoved[graphvertex1]=true;
                  tmproot=oldfather[graphvertex1];
                  while (tmproot!=-1) {
                       if  visited[tmproot] || removed[tmproot] {
                           tmproot=oldfather[tmproot];
                       } else {
                           break;
                       }
                  }
                  if (tmproot==-1){
                      writeln("No available father vertex, WRONG!!!");
                      break;
                  }
             
                  writeln("Iteration ",i,", Remove vertex ",graphvertex1,
                          " to break the repeat pattern, select new root  vertex is  ", tmproot);
                  father=-1;
                  (tmpgraphheight0,tmpgraphvertex0)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, tmproot,tmpremoved,father,true );
                  writeln("Iteration ",i,", Tmp Step 0, Graph BFS height =",tmpgraphheight0, 
                          ", farest vertex is ",tmpgraphvertex0);
                  //if visited[tmpgraphvertex0] {
                  //     break;
                  //}

                  (tmptreeheight1,tmptreevertex1)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, tmpgraphvertex0,tmpremoved,father);
                  father=-1;
                  (tmpgraphheight1,tmpgraphvertex1)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, tmpgraphvertex0,tmpremoved,father,true);
                  writeln("Iteration ",i,", Tmp Step 1, Tree BFS height =",tmptreeheight1,
                          ", Graph BFS height =",tmpgraphheight1, ", Farest tree are graph vertices ",tmptreevertex1,
                          ", ",tmpgraphvertex1);
                  //if visited[tmpgraphvertex1] {
                  //     break;
                  //}

                  if (tmpgraphheight1>=graphheight1) {
                     writeln("confirmed the removed vertex ",graphvertex1," is feasible because the new graph height ", tmpgraphheight1," is not less than the old graph height ",graphheight1);
                     visited[tmproot]=true;
                     visited[tmpgraphvertex0]=true;
                     graphheight1=tmpgraphheight1;
                     graphheight0=tmpgraphheight0;
                     graphvertex1=tmpgraphvertex1;
                     graphvertex0=tmpgraphvertex0;
                     treeheight1=tmptreeheight1;
                     treevertex1=tmptreevertex1;
                     removed=tmpremoved;

                     //check the last step in one complete iteration
                     (treeheight2,treevertex2)=Stree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex1,removed,father,false);

                     oldfather=father;
                     father=-1;
                     (graphheight2,graphvertex2)= Sbfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, graphvertex1,removed,father,true);
                     visited[graphvertex1]=true;
                     //if visited[graphvertex2] {
                     //     break;
                     //}

                     if (treeheight2 < graphheight2) {
                           writeln("Tree height ", treeheight2, " is less than the graph height ",graphheight2, " WRONG!!!");
                     }

                     writeln("Iteration ",i,", Step 2, Tree BFS height =",treeheight2,
                             ", Graph BFS height =", graphheight2, 
                             ", Farest tree and graph vertices ",treevertex2,", ",graphvertex2);
                     if (treeheight1 == graphheight1) {
                             lbound=max(lbound,graphheight1);
                             ubound=lbound;
                             i=iternum;
                             break;
                     } 
                     if (treeheight2 == graphheight2) {
                             lbound=max(lbound,graphheight2);
                             ubound=lbound;
                             i=iternum;
                             break;
                      } else {
                          lbound=max(lbound,graphheight0,graphheight1,graphheight2);
                          ubound=min(ubound, treeheight1, treeheight2,2*graphheight0,2*graphheight1,2*graphheight2);
                      }
                      writeln("Iteration ",i," lbound=",lbound," ubound=",ubound);
                      if lbound>=ubound {
                            i=iternum;
                            break;
                      }
                      i=i+1;
                  } else {
                      //break;
                  } 

              }
              */
              //if graphheight2 < graphheight1  {
              //    removed[graphvertex1]=true;
              //    writeln("Iteration ",i,", Removed the No. 1 farest vertex ",graphvertex1);
              //} 
              writeln("lbound=",lbound," ubound=",ubound," after iteration ",i);
              if lbound==ubound {
                   break;
              }

              i=i+1;
              dindex=dindex+1;
          }
          lbound=max(lbound,plbound);
          ubound=min(ubound,pubound);
          diameter=lbound;
          return (diameter,ubound);
      }//end of component diameter


/*
      proc bak_c_lu (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                       root:int,plbound:int,pubound:int,iternum:int):(int,int) throws{
          var i:int=0;
          var maxv:int;
          var tmpr=root;
          var lbound=plbound;
          var ubound=pubound;

          var cur_level=0;
          var diameter=lbound;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          var SetRemoved=  new distBag(int,Locales); //use bag to keep the removed vertices
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var topdown=0:int;
          var bottomup=0:int;
          var update=false:bool;
          var depth:[D1] int;
          depth=-1;
          var removed=update;
          var father=depth;
          father[root]=-1;
          depth[root]=0;
          var leaf:[D1] bool;
          leaf=true;
          var branch:[D1] bool;
          branch=false;
          var visited=branch;
          var maxdist: atomic int;
          maxdist.write(0);
          var maxvertex: int=-1;
          var maxvx=-1:int;
          var maxvy=-1:int;
          record Mergedist {
                var vx: atomic int;
                var vxvertex:int;
                var vy:atomic int;
                var vyvertex:int;
          }
          var length:[D1] Mergedist;
          forall i in D1 {
                length[i].vx.write(0);
                length[i].vy.write(0);
                length[i].vxvertex=-1;
                length[i].vyvertex=-1;
          }

          while (i<iternum){

          while (numCurF>0) {
                update=false;
                SetRemoved.clear();
          forall i in D1 {
                length[i].vx.write(0);
                length[i].vy.write(0);
                length[i].vxvertex=-1;
                length[i].vyvertex=-1;
          }

          while (i<iternum){

          while (numCurF>0) {
                update=false;
                SetRemoved.clear();
          }
          var length:[D1] Mergedist;
          forall i in D1 {
                length[i].vx.write(0);
                length[i].vy.write(0);
                length[i].vxvertex=-1;
                length[i].vyvertex=-1;
          }

          while (i<iternum){

          while (numCurF>0) {
                update=false;
                SetRemoved.clear();
                coforall loc in Locales  with (ref SetNextF,+ reduce topdown, + reduce bottomup, ref root, ref src, ref depth,ref update, ref SetRemoved) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//top down
                           topdown+=1;
                           forall i in SetCurF with (ref SetNextF, ref update) {
                              var branchnum=0:int;
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update, ref branchnum){
                                         if (depth[j]==-1) {
                                                   depth[j]=cur_level+1;
                                                   father[j]=i;
                                                   leaf[i]=false;
                                                   update=true;
                                                   branchnum+=1;
                                                   SetNextF.add(j,here.id);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update,ref branchnum,ref SetRemoved)  {
                                         if (depth[j]==-1) {
                                                   depth[j]=cur_level+1;
                                                   leaf[i]=false;
                                                   father[j]=i;
                                                   update=true;
                                                   branchnum+=1;
                                                   SetNextF.add(j,here.id);
                                         }
                                  }
                              }

                              if branchnum>1 {
                                  branch[i]=true;
                              }
                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if ( update) {
                    cur_level+=1;
                }
                numCurF=SetNextF.getSize();
                SetCurF<=>SetNextF;
                SetNextF.clear();
                //writeln("BFS tree level=",cur_level);
          }//end while  
          //writeln("After BFS");
          lbound=max(lbound,cur_level);
          writeln("The height from root ", root, " is ", cur_level);

          var mylevel:int;
          var mymaxv:int;
          var oldheight:int;
          oldheight=cur_level;
          for i in D1  {
              if depth[i] ==cur_level {
                            var xx=tree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, i,father);
                            writeln("Tree BFS height=",xx);
                            (mylevel,mymaxv)= bfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, i);
                            if mylevel>oldheight {
                                removed[i]=true;
                            }
                            oldheight=mylevel;
                            writeln("Graph BFS height=",mylevel);
                            lbound=max(lbound,mylevel);
                            ubound=min(ubound, xx,2*lbound);
                            writeln("lbound=",lbound," ubound=",ubound);
                            diameter=lbound;
                            break;
              }//end if
          }



          if lbound==ubound {
               break;
          }

          i=i+1;
          if father[mymaxv]!=-1 {
             mymaxv=father[mymaxv];
          }
          SetCurF.add(mymaxv,here.id);
          numCurF=1;
          update=false;
          depth=-1;
          father=depth;
          father[mymaxv]=-1;
          depth[mymaxv]=0;
          cur_level=0;
          }
          return (diameter,ubound);
          //return max(cur_level,xx);
      }//end of component diameter


      proc c_supernode (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                       root:int,gdiameter:int,numfarv:int):int throws{
          var cur_level=0;
          var diameter=gdiameter;
          var SetCurF=  new distBag(int,Locales);//use bag to keep the current frontier
          var SetNextF=  new distBag(int,Locales); //use bag to keep the next frontier
          //startVerboseMem();
          //{
          var depth:[D1] int;
          //}
          SetCurF.add(root,here.id);
          var numCurF=1:int;
          var update=false:bool;
          depth=-1;
          depth[root]=0;
          while (numCurF>0) {
                update=false;
                coforall loc in Locales  with (ref SetNextF, ref root,  ref depth,ref update) {
                   on loc {
                       ref srcf=src;
                       ref df=dst;
                       ref nf=nei;
                       ref sf=start_i;

                       ref srcfR=srcR;
                       ref dfR=dstR;
                       ref nfR=neiR;
                       ref sfR=start_iR;

                       var edgeBegin=src.localSubdomain().lowBound;
                       var edgeEnd=src.localSubdomain().highBound;
                       var vertexBegin=src[edgeBegin];
                       var vertexEnd=src[edgeEnd];
                       var vertexBeginR=srcR[edgeBegin];
                       var vertexEndR=srcR[edgeEnd];

                       {//top down
                           forall i in SetCurF with (ref SetNextF, ref update) {
                              var branchnum=0:int;
                              if ((xlocal(i,vertexBegin,vertexEnd)) ) {// current edge has the vertex
                                  var    numNF=nf[i];
                                  var    edgeId=sf[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=df[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update){
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               update=true;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              } 
                              if ((xlocal(i,vertexBeginR,vertexEndR))  )  {
                                  var    numNF=nfR[i];
                                  var    edgeId=sfR[i];
                                  var nextStart=max(edgeId,edgeBegin);
                                  var nextEnd=min(edgeEnd,edgeId+numNF-1);
                                  ref NF=dfR[nextStart..nextEnd];
                                  forall j in NF with (ref SetNextF,ref update)  {
                                         if (depth[j]==-1) {
                                               depth[j]=cur_level+1;
                                               update=true;
                                               SetNextF.add(j,here.id);
                                         }
                                  }
                              }
                           }//end coforall
                       }
                   }//end on loc
                }//end coforall loc
                if ( update) {
                    cur_level+=1;
                }
                numCurF=SetNextF.getSize();
                if numCurF>0 {
                    SetCurF<=>SetNextF;
                    SetNextF.clear();
                } else {
                    if cur_level>diameter {
                         numCurF=SetCurF.getSize();
                         forall i in depth {
                              if i==cur_level {
                                  i=0;
                              } else {
                                  i=-1;
                              }
                         }
                         cur_level=0;
                    } else {
                       break;
                    }
                }

                //writeln("BFS tree level=",cur_level);
          }//end while  
          diameter=max(diameter,cur_level);
          return diameter;
          //return max(cur_level,xx);
      }//end of component diameter


*/


/*
      proc c_iter (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                       neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int, 
                       root:int,gdiameter:int, iternum:int):int throws{
          var cur_level=0;
          var diameter=gdiameter;
          var i:int=0;
          var maxv:int;
          var tmpr=root;
          while i<iternum {
            (cur_level,maxv)= bfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, tmpr);
            writeln("The height of the ",i,"th iteration is ",cur_level," and the current diameter is ",diameter);
            if cur_level<=diameter {
                 break;
            }
            diameter=max(diameter,cur_level);
            tmpr=maxv;
            i+=1;
          }
          return diameter;
      }//end of component diameter

*/
    inline proc find_split(u:int,  ref parents:[?D1] int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                parents[i]= w;
                i = v;
          }
      }
      return v;
    }

    inline proc find_naive(u:int,  parents:[?D1] int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                //parents[i]= w;
                i = v;
          }
      }
      return v;
    }

    inline proc find_naive_atomic(u:int,  ref parents:[?D1] atomic int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                //parents[i]= w;
                i = v;
          }
      }
      return v;
    }



    inline proc find_split_atomic(u:int,  ref parents:[?D1] atomic int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                parents[i].write(w);
                i = v;
          }
      }
      return v;
    }


    inline proc find_split_h(u:int, ref  parents:[?D1] int, h:int):int {
       var  t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i];
          w = parents[v];
          if (v <= w) {
                break;
          } else {
                //gbbs::atomic_compare_and_swap(&parents[i], v, w);
                parents[i]= w;
                i = v;
          }
          t=t+1;
      }
      return v;
    }
    inline proc find_split_atomic_h(u:int, ref  parents:[?D1] atomic int, h:int):int {
       var t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                parents[i].compareAndSwap(v, w);
                i = v;
          }
          t=t+1;
      }
      return v;
    }

    proc find_half(u:int,  ref parents:[?D1] int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                parents[i]= w;
                i = parents[i];
          }
       }
       return v;
    }
    proc find_half_h(u:int,  ref parents:[?D1] int,h:int):int {
       var t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
                break;
          } else {
                parents[i]= w;
                i = parents[i];
          }
          t=t+1;
       }
       return v;
    }

    proc find_half_atomic_h(u:int,  ref parents:[?D1] atomic int,h:int):int {
       var t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                parents[i].compareAndSwap(v, w);
                i = parents[i].read();
          }
          t=t+1;
       }
       return v;
    }


    proc find_half_atomic(u:int,  ref parents:[?D1] atomic int):int {
       var i=u;
       var v,w:int;
       while (1) {
          v = parents[i].read();
          w = parents[v].read();
          if (v == w) {
                break;
          } else {
                parents[i].compareAndSwap(v, w);
                i = parents[i].read();
          }
       }
       return v;
    }



    proc unite(u:int, v:int,  ref parents:[?D1] int):int {
       var rx=u;
       var ry=v;
       var p_ry = parents[ry];
       var p_rx = parents[rx];
       while (p_ry!=p_rx){
          if (p_rx > p_ry) {
               rx<=>ry;
               p_rx<=> p_ry;
          }
          if (ry == p_ry ) {
                 parents[ry]= p_rx;
                 while (parents[parents[u]]<parents[u]) {
                      parents[u]=parents[parents[u]];
                 }
                 while (parents[parents[v]]<parents[v]) {
                      parents[v]=parents[parents[v]];
                 }
                 //compress(x, parents);
                 //compress(y, parents);
                 return rx;
          } else {
                    //rx = splice(rx, ry, parents);
                    parents[ry]= p_ry;
          }
          p_ry = parents[ry];
          p_rx = parents[rx];
       }
       return rx;
    }



    proc unite_atomic(u:int, v:int,  ref parents:[?D1] atomic int):int {
       var ru=u;
       var rv=v;
       var p_rv = parents[rv].read() ;
       var p_ru = parents[ru].read();
       while (p_rv!=p_ru) {
          if (p_ru < p_rv) {
               ru<=>rv;
               p_ru<=> p_rv;
          }

          if ( (ru == p_ru) && (parents[ru].compareAndSwap(p_ru,p_rv) ) ) {
                 return ru;
          } else {
                    var g_u=parents[p_ru].read();
                    while (p_ru>g_u) {
                         parents[ru].compareAndSwap(p_ru,g_u);
                         p_ru=parents[ru].read();
                    }
                    ru=g_u;
                    p_ru = parents[ru].read();
          }
       }
       return ru;
    }







    // Contour variant: a  mapping based connected components algorithm
    proc cc_mm_diameter(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int): int throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
              on loc {
                forall i in f.localSubdomain()  with (ref af){
                  af[i].write(i);
                }
              }
           }

           if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
           }else {
                ORDERH=1024;
           }  
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count , ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {

                                forall x in src.localSubdomain() with ( + reduce lcount)  {
                                    var u = src[x];
                                    var v = dst[x];
                                    var TmpMin:int;

                                    var fu=find_split_atomic_h(u,localf,ORDERH);
                                    var fv=find_split_atomic_h(v,localf,ORDERH);
                                    TmpMin=min(fu,fv);
                                    var oldx=localf[u].read();
                                    while (oldx>TmpMin) {
                                              if (localf[u].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[u].read();
                                              lcount+=1;
                                    }
                                    oldx=localf[v].read();
                                    while (oldx>TmpMin) {
                                              if (localf[v].compareAndSwap(oldx,TmpMin)) {
                                                  u=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                    }
                   
                                }//end of forall
                                if( (lcount==0) ) {
                                    lconverged = true;
                                    writeln("Loale ", here.id, " inner iteration=", litera," lcount=",lcount);
                                }
                                else {
                                    lconverged = false;
                                    lcount=0;
                                }
                                litera+=1;
                             }// while
                             writeln("Converge local ------------------------------------------");
                             forall i in 0..Nv-1 with (+ reduce count) {
                                 var old=af[i].read();
                                 var newval=localf[i].read();
                                 while old>newval {
                                     af[i].compareAndSwap(old,newval);
                                     old=af[i].read();
                                     count+=1;
                                 }
                             }

                     }// end of on loc 
                 }// end of coforall loc 

                 if( (count==0) ) {
                      converged = true;
                 }
                 else {
                     converged = false;
                     count=0;
                 }
                 itera += 1;
                 writeln(" -----------------------------------------------------------------");
                 writeln(" outter iteration=", itera);


           }//while

           forall i in 0..Nv-1 with (+ reduce count) {
                    f[i]=af[i].read();
           }
      } else {


          coforall loc in Locales with (ref f)  {
            on loc {
              forall i in f.localSubdomain() {
                f[i] = i;
                if (nei[i] >0) {
                    var tmpv=dst[start_i[i]];
                    if ( tmpv <i ) {
                         f[i]=tmpv;
                    }
                }
                if (neiR[i] >0) {
                    var tmpv=dstR[start_iR[i]];
                    if ( tmpv <f[i] ) {
                         f[i]=tmpv;
                    }
                }
              }
            }
          }
    
    

          if (Ne/here.numPUs() < LargeScale) {
               ORDERH=2;
          }else {
               ORDERH=1024;
          }  
          //we first check with order=1 mapping method
          while( (!converged) ) {
            // In the second step, we employ high order mapping
            localtimer.clear();
            localtimer.start(); 




            if (ORDERH==2) {
                coforall loc in Locales with ( + reduce count, ref f ) {
                  on loc {
                    var edgeBegin = src.localSubdomain().lowBound;
                    var edgeEnd = src.localSubdomain().highBound;

                    forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
                      var u = src[x];
                      var v = dst[x];

                      var TmpMin:int;

                      TmpMin=min(f[f[u]],f[f[v]]);
                      if(TmpMin < f[f[u]]) {
                         f[f[u]] = TmpMin;
                      }
                      if(TmpMin < f[f[v]]) {
                         f[f[v]] = TmpMin;
                      }
                      if(TmpMin < f[u]) {
                        f[u] = TmpMin;
                      }
                      if(TmpMin < f[v]) {
                        f[v] = TmpMin;
                      }
                    }//end of forall
                    forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
                      var u = src[x];
                      var v = dst[x];
                      if (count==0) {
                            if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                                count=1;
                            } 
                      }
                    }
                  }// end of on loc 
                }// end of coforall loc 
            } else {
                coforall loc in Locales with ( + reduce count, ref f) {
                  on loc {
                    var edgeBegin = src.localSubdomain().lowBound;
                    var edgeEnd = src.localSubdomain().highBound;
    
                    forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
                      var u = src[x];
                      var v = dst[x];
    
                      var TmpMin:int;
                      if (itera==1) {
                          TmpMin=min(u,v);
                      } else{
                          TmpMin=min(find_split_h(u,f,ORDERH),find_split_h(v,f,ORDERH));
                      }
                      if ( (f[u]!=TmpMin) || (f[v]!=TmpMin)) {
                          var myx=u;
                          var lastx=u;
                          while (f[myx] >TmpMin ) {
                              lastx=f[myx];
                              f[myx]=TmpMin;
                              myx=lastx;
                          }
                          myx=v;
                          while (f[myx] >TmpMin ) {
                              lastx=f[myx];
                              f[myx]=TmpMin;
                              myx=lastx;
                          }
                      }
                  
                    }//end of forall

                    forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
                      var u = src[x];
                      var v = dst[x];
                      if (count==0) {
                        if (f[u]!=f[f[u]] || f[v]!=f[f[v]] || f[f[u]]!=f[f[v]]) {
                            count=1;
                        }     
                      }
                    }
                  }// end of on loc 
                }// end of coforall loc 

            }


            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
              count=0;
            }
            itera += 1;
            //writeln("My Order is ",ORDERH); 
            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
          }

      }
      writeln("Number of iterations = ", itera-1);


      var CompSet=new set(int,parSafe = true);
      for i in f  {
         CompSet.add(i);
      }
      writeln("Size of the Components=",CompSet.size);
      writeln("The components are as follows");
      writeln(CompSet);
      writeln("Size of the Components=",CompSet.size);
      // handle all components
      var largestD=0:int;
      var diameter=0:int ;
      var Ubound=0:int;
      var ubound:int;
      for i in CompSet  {
          writeln("Handle component ",i);
          var numV=f.count(i);
          if numV<=max(2,largestD) {
              writeln("no more than  two or ", largestD, " vertices, contiune");
              continue;
          }
          if numV>2500 {
              var vset= new set(int, parSafe = true); 
              for k in D1 {
                  if f[k]==i {
                     vset.add(k);
                  }
              }
              var vertexarray=vset.toArray();
              writeln("Enter BFS method");
              writeln("*************************************");
              //diameter=c_diameter(nei, start_i,src, dst,
              //          neiR, start_iR,srcR, dstR, i,largestD);
              //diameter=c_supernode(nei, start_i,src, dst,
              //          neiR, start_iR,srcR, dstR, i,largestD,10);
              (diameter,ubound)=c_lu(nei, start_i,src, dst,
                        neiR, start_iR,srcR, dstR, vertexarray[0],largestD,99999,10,vertexarray,f);
              if largestD<diameter {
                 Ubound=ubound;
              }
              writeln("Pass 1  The diameter of component ",i,"=",diameter );
              largestD=max(largestD,diameter);
          } else {


              writeln("----------------------------------------");
              writeln("Allocate ",numV,"X",numV," matrix");
              var AdjMatrix=Matrix(numV,numV,eltType=int);
              AdjMatrix=0;
              //writeln("Assign diagnal");
              forall j in 0..numV-1 with (ref AdjMatrix) {
                   AdjMatrix[j,j]=1;
              }
              var mapary=f;
              var tmpmap=0:int;
              //writeln("mapping vertices to matrix");
              for k in 0..f.size-1 {
                  if f[k]==i {
                      mapary[k]=tmpmap;
                      tmpmap+=1;
                  
                  }
              }
              //writeln("assign edge to matrix");
              forall j in 0..f.size-1 with (ref AdjMatrix, ref diameter) {
                 if f[j]==i  && nei[j] >=1 {
                     for k in start_i[j]..start_i[j]+nei[j]-1 {
                         if f[src[k]]!=i || f[dst[k]]!=i {
                             writeln("src[",k,"]=",src[k]," component=",i," dst[",k,"]=",dst[k]," f[src[",k,"]]=",f[src[k]]," f[dst[",k,"]]=",f[dst[k]]);
                             writeln("There is something wrong in the component ",i, " because they mapped to different vertices");
                             exit(0);
                         }
                         AdjMatrix[mapary[j],mapary[dst[k]]]=1;
                         AdjMatrix[mapary[dst[k]],mapary[j]]=1;
                         if j!=dst[k]  {
                            diameter=1;
                         }
 
                     }      
                 }

              }
              if (numV<20) {
                  writeln("The adjacency matrix ",numV,"X",numV," is as follows");
                  writeln(AdjMatrix);
              } else {

                  writeln("It is a ",numV,"X",numV," AdjMatrix");
              }



              // Here, we have built the adjacencent matrix based on component i
              var Mk=AdjMatrix;
              var k=0:int;
              var x,y:int;
              var havezero=false:bool;
      
              forall x in Mk with (ref havezero) {
                   if x==0 {
                       havezero=true;
                   }
              }
              writeln("size of the matrix=",Mk.size);
              //writeln("calculate matrix power");
              while havezero && Mk.size>1 {
                  var MM= matPow(Mk, 2);
                  k=k+1;
                  Mk=MM;
                  havezero=false;
                  forall x in Mk with (ref havezero) {
                       if x==0 {
                           havezero=true;
                       }
                  }
                  writeln("k=",k);
              }
              if k<=1 {
                   writeln("The diameter of component ",i,"=1");
                   continue;
              }
              diameter=max(2**(k-1),diameter):int ;
              var left=matPow(AdjMatrix, 2**(k-1));
              var B=left;
              for l in 0..k-2 {
                  var Ml = matPow(AdjMatrix,2**(k-2-l));

                  var Bnew = dot(B, Ml);

                  havezero=false;
                  forall x in Bnew with (ref havezero) {
                       if x==0 {
                           havezero=true;
                       }
                  }
                  if havezero {
                      B = Bnew;
                      //dot(left, Ml);
                      diameter  += 2**(k-2-l);
                      writeln("Increase diameter to ", diameter);
                  } else {
                      
                      writeln("2^",k-2-l," do not have zero entry");
                  }
              }
              largestD=max(largestD,diameter);
              writeln("The diameter of component ",i,"=",diameter );
          }

      }


      writeln("Size of the Components=",CompSet.size);
      writeln("The largest diameter =",largestD);
      if Ubound<largestD {
          Ubound=largestD;
      }
      writeln("The Ubound =",Ubound);
      return largestD;
    }




    var timer:stopwatch;
    var retDiameter:int;
    if (Directed == 0) {

        timer.clear();
        timer.start();
        retDiameter  = cc_mm_diameter( toSymEntry(ag.getNEIGHBOR(), int).a, 
                            toSymEntry(ag.getSTART_IDX(), int).a, 
                            toSymEntry(ag.getSRC(), int).a, 
                            toSymEntry(ag.getDST(), int).a, 
                            toSymEntry(ag.getNEIGHBOR_R(), int).a, 
                            toSymEntry(ag.getSTART_IDX_R(), int).a, 
                            toSymEntry(ag.getSRC_R(), int).a, 
                            toSymEntry(ag.getDST_R(), int).a);
        timer.stop(); 
        outMsg = "Time elapsed for fs mm diameter: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);


    }
   

    var repMsg = retDiameter:string;
    return new MsgTuple(repMsg, MsgType.NORMAL);
  }

  use CommandMap;
  registerFunction("segmentedGraphDiameter", segDiameterMsg,getModuleName());
}
