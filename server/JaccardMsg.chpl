module JaccardMsg {


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
  

  // calculate Jaccard coefficient
  proc segJaccardMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
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
      var jaccard=makeDistArray(Nv*Nv,int);//we only need to save half results and we will optimize it later.
      coforall loc in Locales  {
                  on loc {
                           forall i in jaccard.localSubdomain() {
                                 jaccard[i]=0;
                           }       
                  }
      }
      var root:int;
      var srcN, dstN, startN, neighbourN,vweightN,eweightN, rootN :string;
      var srcRN, dstRN, startRN, neighbourRN:string;
      var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
      // the graph must be relabeled based on degree of each vertex
      var ag = gEntry.graph;
 

      proc jaccard_coefficient__u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
                        neiR:[?D11] int, start_iR:[?D12] int,srcR:[?D13] int, dstR:[?D14] int):string throws{

          var edgeBeginG=makeDistArray(numLocales,int);//each locale's starting edge ID
          var edgeEndG=makeDistArray(numLocales,int);//each locales'ending edge ID

          var vertexBeginG=makeDistArray(numLocales,int);//each locale's beginning vertex ID in src
          var vertexEndG=makeDistArray(numLocales,int);// each locales' ending vertex ID in src


          coforall loc in Locales   {
              on loc {
                 edgeBeginG[here.id]=src.localSubdomain().low;
                 edgeEndG[here.id]=src.localSubdomain().high;

                 vertexBeginG[here.id]=src[edgeBeginG[here.id]];
                 vertexEndG[here.id]=src[edgeEndG[here.id]];

              }
          }
          coforall loc in Locales   {
              on loc {
                 if (here.id>0) {
                   vertexBeginG[here.id]=vertexEndG[here.id-1]+1;
                 } else {
                   vertexBeginG[here.id]=0;
                 }

              }
          }
          coforall loc in Locales   {
              on loc {

                 if (here.id<numLocales-1) {
                   vertexEndG[here.id]=vertexBeginG[here.id+1]-1;
                 } else {
                   vertexEndG[here.id]=nei.size;
                 }

              }
          }
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

                       var edgeBegin=src.localSubdomain().low;
                       var edgeEnd=src.localSubdomain().high;
                       var vertexBegin=vertexBeginG[here.id];
                       var vertexEnd=vertexEndG[here.id];

                       forall  i in vertexBegin..vertexEnd {
                              var    numNF=nf[i];
                              var    edgeId=sf[i];
                              var nextStart=edgeId;
                              var nextEnd=edgeId+numNF-1;
                              ref NF1=df[nextStart..nextEnd];
                              ref NF2=df[nextStart+1..nextEnd];
                              forall e1 in nextStart..nextEnd {
                                   var u=df[e1];
                                   forall e2 in e1+1..nextEnd {
                                       var v=df[e2];
                                       jaccard(u*Nv+v)+=1;
                                   }
                              } 
                       }
              }
          }//end coforall loc

          return "success";
      }//end of fo_bag_bfs_kernel_u



      if (!Directed) {
                  jaccard_coefficient__u(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a
                  );
                  
                  repMsg=return_jaccard();
 
              }
          }
      }
      timer.stop();
      var outMsg= "graph Jaccard takes "+timer.elapsed():string;
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    proc registerMe() {
        use CommandMap;
        registerFunction("segmentedGraphJaccard", segJaccardMsg);
    }
 }


