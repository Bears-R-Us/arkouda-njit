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
          /*
          forall e in D3 {
               var s=src[e];
               var d=dst[e];
               if (depth[s]>depth[d] && d!=father[s] ) {
                     s=father[s];
                     while s!=-1 && depth[s]>depth[d] {
                         s=father[s];
                     }
               } else if (depth[s]<depth[d] && s!=father[d] ) {
                     d=father[d];
                     while d!=-1 && depth[s]<depth[d] {
                         d=father[d];
                     }
               } 
               if depth[s]==depth[d] && depth[s]!=-1 {
                     if s==d {
                         branch[s]=false;
                     } else {
                         var fs=father[s];
                         var fd=father[d];
                         while fs!=-1 && fd!=-1 && fs!=fd {
                             fs=father[fs];
                             fd=father[fd];
                         } 
                         if fs==fd {
                             branch[fs]=false;
                         }
                     }
               }
          }


          forall i in D1 with (ref maxdist, ref maxvertex,ref maxvx,ref maxvy,ref diameter) {
          //for i in D1 {
              if leaf[i]==true  {
              //if leaf[i]==true && depth[i] >=diameter/2 {
                   leaf[i]=false;
                   var f=father[i];
                   var height=1;
                   var old:int;
                   var newval:int;
                   //while (f!=-1) && (leaf[f] ==false) {
                   while (f!=-1)  && depth[i] >=diameter/2  {
                        //writeln("Leaf ",i," search to vertex ",f, " with height ", height);
                        if length[f].vx.read()<height && branch[f]==true {
                             old=length[f].vx.read();
                             while (old<height) {
                                length[f].vx.compareAndSwap(old,height);
                                old=length[f].vx.read();
                             }
                             if (old==height && length[f].vxvertex!=i) {
                                length[f].vxvertex=i;
                             } 
                        } else {
                            if length[f].vy.read()<height && branch[f]==true {
                                 old=length[f].vy.read();
                                 while (old<height) {
                                    length[f].vy.compareAndSwap(old,height);
                                    old=length[f].vy.read();
                                 }
                                 if (old==height && length[f].vyvertex!=i) {
                                    length[f].vyvertex=i;
                                 } 
                         
                            } else { 
                                          break;
                            }
                        }
                            
                        f=father[f];
                        height+=1;
                   }//end while
              }//end if
          }


          */

          var LeafSet=new set(int,parSafe = true);
          forall i in D1 with (ref maxdist, ref maxvertex,ref maxvx,ref maxvy,ref diameter,ref LeafSet) {
              if leaf[i]==true  {
                   if depth[i] <diameter/2 {
                       leaf[i]=false;
                   } else {
                      LeafSet.add(i);
                   }
                   /*
                   else {
                       var f=father[i];
                       var height=1;
                       var old:int;
                       var newval:int;
                       while (f!=-1) && (branch[f] ==false) {
                           f=father[f];
                       }
                       if f!=-1 && branch[f]==true {
                           if height<length[f].vx.read(){
                                leaf[i]=false;
                           } else {
                              if length[f].vxvertex!=i {
                                leaf[i]=false;
                              }
                           }

                       }
                  }//end if
                  */
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






      proc c_lu (nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
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
          lbound=max(lbound,cur_level);
          writeln("The height from root ", root, " is ", cur_level);

          var mylevel:int;
          var mymaxv:int;
          for i in D1  {
              if depth[i] ==cur_level {
                            var xx=tree_bfs( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, i,father);
                            writeln("Tree BFS height=",xx);
                            (mylevel,mymaxv)= bfs_maxv( nei, start_i,src, dst,
                                    neiR, start_iR,srcR, dstR, i);
                            writeln("Graph BFS height=",mylevel);
                            lbound=max(lbound,mylevel);
                            ubound=min(ubound, xx*2);
                            writeln("lbound=",lbound," ubound=",ubound);
                            diameter=lbound;
                            break;
              }//end if
          }



          if lbound==ubound {
               break;
          }

          i=i+1;
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



    // Contour: a minimum mapping based connected components algorithm, a mixed method
    proc cc_contour(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;


      localtimer.clear();
      localtimer.start(); 
      coforall loc in Locales with (ref f) {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd with (ref f) {
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


      localtimer.stop(); 
      executime=localtimer.elapsed();
      myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;

      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      //we vx check with order=1 mapping method
      while( (!converged) && (itera<FirstOrderIters) && 
               ( (Ne/here.numPUs() < LargeScale) )) {
        localtimer.clear();
        localtimer.start(); 
        coforall loc in Locales with ( + reduce count, ref f) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
              var u = src[x];
              var v = dst[x];

                         var TmpMin:int;
                         TmpMin=min(f[u],f[v]);
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count=count+1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count=count+1;
                         }
                  
            }//end of forall
          }
        }


        if( (count==0) ) {
          converged = true;
        }
        else {
          converged = false;
          count=0;
        }
        itera += 1;
        writeln("My Order is 1"); 
        localtimer.stop(); 
        executime=localtimer.elapsed();
        //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
      }




      if (Ne/here.numPUs() < LargeScale) {
           ORDERH=2;
      }else {
           ORDERH=1024;
      }  
      // then we use 1m1m method
      while( (!converged) ) {
        localtimer.clear();
        localtimer.start(); 
        coforall loc in Locales with ( + reduce count, ref f) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
              var u = src[x];
              var v = dst[x];

                         var TmpMin:int;
                         TmpMin=min(f[u],f[v]);
                         if(TmpMin < f[u]) {
                             f[u] = TmpMin;
                             count=count+1;
                         }
                         if(TmpMin < f[v]) {
                             f[v] = TmpMin;
                             count=count+1;
                         }
                  
            }//end of forall
          }
        }


        itera += 1;
        //writeln("My Order is 1"); 
        localtimer.stop(); 
        executime=localtimer.elapsed();
        //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
        if( (count==0) ) {
          converged = true;
          continue;
        }
        else {
          converged = false;
          count=0;
        }

        // In the second step, we employ high order mapping
        localtimer.clear();
        localtimer.start(); 
        if (ORDERH==2) {
            coforall loc in Locales with ( + reduce count, ref f ) {
              on loc {
                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;

                forall x in edgeBegin..edgeEnd  with ( + reduce count, ref f)  {
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
            coforall loc in Locales with ( + reduce count , ref f) {
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

                forall x in edgeBegin..edgeEnd  with ( + reduce count )  {
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
        writeln("My Order is ",ORDERH); 
        localtimer.stop(); 
        executime=localtimer.elapsed();
        //myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        //writeln("Efficiency is ", myefficiency, " time is ",executime);
      }



      writeln("Number of iterations = ", itera-1);

      return f;
    }














    // union-find
    proc cc_unionfind(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 

      // Initialize f and f_low in distributed memory.

      coforall loc in Locales with (ref f) {
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd with (ref f) {
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



      var converged:bool = false;
      var itera = 1;
      {
        var count:int=0;
        var count1:int=0;
        coforall loc in Locales with ( + reduce count, + reduce count1, ref f) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd  with (ref f)   {
              var u = src[x];
              var v = dst[x];
              unite(u,v,f);
            }//end of forall
            forall x in edgeBegin..edgeEnd  with (ref f)  {
              var u = src[x];
              var v = dst[x];
              var l=find_half(u,f);
              var t=u;
              var ft=f[t];
              while (f[t]>l) {
                  ft=f[t];
                  f[t]=l;
                  t=ft;
              }
              l=find_half(v,f);
              t=v;
              while (f[t]>l) {
                  ft=f[t];
                  f[t]=l;
                  t=ft;
              }
            }//end of forall
          }
        }
      }
      writeln("Number of iterations = ", itera);

      return f;
    }







    // distance=2;
    proc cc_2(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var converged:bool = false;
      var count:int=0;
      var itera = 1;
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;
      if (numLocales>1 && MultiLocale==1) {

           coforall loc in Locales with (ref af) {
                on loc {
                    forall i in f.localSubdomain() with (ref af)  {
                         af[i].write(i);
                    }
                }
           }
           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                             var localf:[0..Nv-1] atomic int;
                             var lconverged:bool = false;
                             var litera = 1;
                             var lcount:int=0;
                             forall i in 0..Nv-1 with (ref af)  {
                                 localf[i].write(af[i].read());
                             }
                             while (!lconverged) {
                                forall x in src.localSubdomain()  with ( + reduce lcount)  {
                                        var u = src[x];
                                        var v = dst[x];
                                        var TmpMin:int;
                                        var fu=localf[u].read();
                                        var fv=localf[v].read();
                                        TmpMin=min(localf[fu].read(),localf[fv].read());
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
                                                  v=oldx;
                                              }
                                              oldx=localf[v].read();
                                              lcount+=1;
                                        }
                                        oldx=localf[fu].read();
                                        while (oldx>TmpMin) {
                                              if (localf[fu].compareAndSwap(oldx,TmpMin)) {
                                                  fu=oldx;
                                              }
                                              oldx=localf[fu].read();
                                              lcount+=1;
                                        }


                                        oldx=localf[fv].read();
                                        while (oldx>TmpMin) {
                                              if (localf[fv].compareAndSwap(oldx,TmpMin)) {
                                                  fv=oldx;
                                              }
                                              oldx=localf[fv].read();
                                              lcount+=1;
                                        }


                                }// forall
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

      // Initialize f and f_low in distributed memory.

          coforall loc in Locales with (ref f){
            on loc {
              var vertexBegin = f.localSubdomain().lowBound;
              var vertexEnd = f.localSubdomain().highBound;
              forall i in vertexBegin..vertexEnd {
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


          while(!converged) {
            var count:int=0;
            localtimer.clear();
            localtimer.start(); 
            coforall loc in Locales with ( + reduce count,ref f ) {
              on loc {
                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;

                forall x in edgeBegin..edgeEnd  with ( + reduce count )  {
                  var u = src[x];
                  var v = dst[x];

                  var TmpMin:int;
                  if (itera==1) {
                         TmpMin=min(u,v);
                  } else {
                    TmpMin=min(f[f[u]],f[f[v]]);
                  }
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
              }
            }



            localtimer.stop(); 
            executime=localtimer.elapsed();
            myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
            //writeln("Efficiency is ", myefficiency, " time is ",executime);
            if( (count==0) ) {
              converged = true;
            }
            else {
              converged = false;
            }
            itera += 1;
          }
      }
      writeln("Number of iterations = ", itera-1);

      return f;
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
          //if true {
          if numV>2500 {
              writeln("Enter BFS method");
              writeln("*************************************");
              //diameter=c_diameter(nei, start_i,src, dst,
              //          neiR, start_iR,srcR, dstR, i,largestD);
              //diameter=c_supernode(nei, start_i,src, dst,
              //          neiR, start_iR,srcR, dstR, i,largestD,10);
              (diameter,ubound)=c_lu(nei, start_i,src, dst,
                        neiR, start_iR,srcR, dstR, i,largestD,99999,10);
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
      /*
      largestD=0;
      diameter=0;
      var diameter1=0:int;
      var diameter2=0:int;
      var largestD1=0:int;
      var largestD2:int=0;
      for i in CompSet  {
          writeln("Handle component ",i);
          var numV=f.count(i);
          if numV<=max(2,largestD) {
              writeln("no more than  two or ", largestD, " vertices, contiune");
              continue;
          }
          {
              //writeln("Enter BFS method");
              //writeln("*************************************");
              var localtimer:stopwatch;
              var executime:real;
              localtimer.start();
              diameter1=c_iter(nei, start_i,src, dst,
                        neiR, start_iR,srcR, dstR, i,largestD,10);
              
              executime=localtimer.elapsed();
              writeln("Pass 1  The diameter of component ",i,"=",diameter1," execution time is ",executime );
              localtimer.stop();

              localtimer.clear();
              localtimer.start();
              diameter2=c_farthest(nei, start_i,src, dst,
                        neiR, start_iR,srcR, dstR, i,largestD,10);
              writeln("Difference=",executime-localtimer.elapsed(),", Pass 1 needs ", executime, " Pass 2 needs ", localtimer.elapsed());
              if diameter1!=diameter2 {
                  writeln("not equal, diameter 1=",diameter1,", diameter 2=",diameter2);
              } else  {
                  writeln("equal, diameter =",diameter1);
              }
              largestD1=max(largestD1,diameter1);
              largestD2=max(largestD2,diameter2);
              largestD=max(largestD1,largestD2);
          } 
      }
      writeln("Size of the Components=",CompSet.size);
      writeln("The largest diameter =",largestD);

      */
      return largestD;
    }




    // the atomic method for union find implementation
    proc cc_connectit(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int, neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(Nv, int); 
      var af = makeDistArray(Nv, atomic int); 
      var f_low = makeDistArray(Nv, atomic int); 
      var localtimer:stopwatch;
      var myefficiency:real;
      var executime:real;

      // Initialize f and f_low in distributed memory.
      coforall loc in Locales  with (ref af, ref f, ref f_low){
        on loc {
          var vertexBegin = f.localSubdomain().lowBound;
          var vertexEnd = f.localSubdomain().highBound;
          forall i in vertexBegin..vertexEnd with (ref af, ref f, ref f_low) {
            f_low[i].write(i);
            f[i]=i;
            af[i].write(i);
          }
        }
      }


      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      var count1:int=0;


      if (numLocales>1 && MultiLocale==1) {

           while( (!converged) ) {
             // In the second step, we employ high order mapping
             localtimer.clear();
             localtimer.start(); 

             
             coforall loc in Locales with ( + reduce count, ref af ) {
                     on loc {
                                var localf_low:[0..Nv-1] atomic int;
                                var lconverged:bool = false;
                                var litera = 1;
                                var lcount:int=0;
                                forall i in 0..Nv-1 {
                                    localf_low[i].write(af[i].read());
                                }

                                forall x in src.localSubdomain()    {
                                    var u = src[x];
                                    var v = dst[x];
                                    unite_atomic(u,v,localf_low);
                                }
                                forall x in src.localSubdomain()    {
                                     var u = src[x];
                                     var v = dst[x];
                                     var l=find_naive_atomic(u,localf_low);
                                     var oldx=localf_low[u].read();
                                     while (oldx>l) {
                                           if (localf_low[u].compareAndSwap(oldx,l)) {
                                               u=oldx;
                                           }
                                           oldx=localf_low[u].read();
                                     }
                                     //l=find_naive_atomic(v,localf_low);
                                     oldx=localf_low[v].read();
                                     while (oldx>l) {
                                           if (localf_low[v].compareAndSwap(oldx,l)) {
                                               v=oldx;
                                           }
                                           oldx=localf_low[v].read();
                                     }

                                }//end of forall

                                writeln("Converge local ------------------------------------------");
                                forall i in 0..Nv-1 with (+ reduce count) {
                                    var old=af[i].read();
                                    var newval=localf_low[i].read();
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

      {
        coforall loc in Locales with ( + reduce count, + reduce count1, ref f_low) {
          on loc {
            var edgeBegin = src.localSubdomain().lowBound;
            var edgeEnd = src.localSubdomain().highBound;

            forall x in edgeBegin..edgeEnd    {
              var u = src[x];
              var v = dst[x];

              unite_atomic(u,v,f_low);
            }
            forall x in edgeBegin..edgeEnd    {
              var u = src[x];
              var v = dst[x];
              var l=find_naive_atomic(u,f_low);
              var oldx=f_low[u].read();
              while (oldx>l) {
                    if (f_low[u].compareAndSwap(oldx,l)) {
                        u=oldx;
                    }
                    oldx=f_low[u].read();
              }
              //l=find_naive_atomic(v,f_low);
              oldx=f_low[v].read();
              while (oldx>l) {
                    if (f_low[v].compareAndSwap(oldx,l)) {
                        v=oldx;
                    }
                    oldx=f_low[v].read();
              }

            }//end of forall
          }
        }
        
      }


      itera+=1;
      coforall loc in Locales with (ref f) {
        on loc {
          forall i in f.localSubdomain() {
            f[i] = f_low[i].read();
          }
        }
      }
      }

      writeln("Number of iterations = ", itera-1);
      return f;
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








      /*
      diameter=largestD;
      for i in CompSet  {
          writeln("Handle component ",i);
          var numV=f.count(i);
          if numV<diameter {
              writeln("no more than ",diameter,"  vertices, contiune");
              continue;
          }
          {
              var depth=f;
              depth=-1;
              depth[i]=0; 
              var leaf=depth;
              leaf[i]=-1;//means it is a leaf vertex
              var level=bfs(nei, start_i,src, dst,
                        neiR, start_iR,srcR, dstR, 
                        depth,i,leaf,diameter);
              diameter =max(diameter,level);
              var longestvertexSet=new set(int,parSafe = true);
              forall s in 0..depth.size-1 with (ref longestvertexSet) {
                   if (depth[s] >= diameter/2 ) && (leaf[s]==-1) {
                        longestvertexSet.add(s);
                   }
              }
              for s in longestvertexSet {
                  depth=-1;
                  depth[s]=0;
                  leaf=depth;
                  leaf[i]=-1;//means it is a leaf vertex
                  level=bfs(nei, start_i,src, dst,
                        neiR, start_iR,srcR, dstR, 
                        depth,s,leaf,diameter);
                  diameter =max(diameter,level);

              }
              writeln("The diameter of component ",i,"=",diameter );
              largestD=max(largestD,diameter);
          } 
      }
      */



