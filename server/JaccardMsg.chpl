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
  use IO;


  use SymArrayDmap;
  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use ArgSortMsg;
  use Time;
  use CommAggregation;
  use Map;
  use DistributedDeque;


  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;


  private config const logLevel = ServerConfig.logLevel;
  const smLogger = new Logger(logLevel);
  

  // calculate Jaccard coefficient
  proc segJaccardMsg(cmd: string, payload: string, st: borrowed SymTab): MsgTuple throws {
      var repMsg: string;
      var (n_verticesN, n_edgesN, directedN, weightedN, graphEntryName, restpart )
          = payload.splitMsgToTuple(6);
      var Nv=n_verticesN:int;
      var Ne=n_edgesN:int;
      var Directed=directedN:int;
      var Weighted=weightedN:int;
      var timer:Timer;



      var JaccGamma=makeDistArray(Nv*Nv,atomic int);//we only need to save half results and we will optimize it later.
      var JaccCoeff=makeDistArray(Nv*Nv, real);//we only need to save half results and we will optimize it later.
      coforall loc in Locales  {
                  on loc {
                           forall i in JaccGamma.localSubdomain() {
                                 JaccGamma[i].write(0);
                           }       
                  }
      }
      var root:int;
      var srcN, dstN, startN, neighbourN,vweightN,eweightN, rootN :string;
      var srcRN, dstRN, startRN, neighbourRN:string;
      var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
      // the graph must be relabeled based on degree of each vertex
      var ag = gEntry.graph;
 

      timer.start();
      proc jaccard_coefficient_u(nei:[?D1] int, start_i:[?D2] int,src:[?D3] int, dst:[?D4] int,
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
                   vertexEndG[here.id]=nei.size-1;
                 }

              }
          }
          coforall loc in Locales   {
              on loc {

                       var vertexBegin=vertexBeginG[here.id];
                       var vertexEnd=vertexEndG[here.id];

                       forall  i in vertexBegin..vertexEnd {
                              var    numNF=nei[i];
                              var    edgeId=start_i[i];
                              var nextStart=edgeId;
                              var nextEnd=edgeId+numNF-1;
                              forall e1 in nextStart..nextEnd-1 {
                                   var u=dst[e1];
                                   forall e2 in e1+1..nextEnd {
                                       var v=dst[e2];
                                       if u<v {
                                           JaccGamma[u*Nv+v].add(1);
                                       }
                                   }
                              } 
                              numNF=neiR[i];
                              edgeId=start_iR[i];
                              nextStart=edgeId;
                              nextEnd=edgeId+numNF-1;
                              forall e1 in nextStart..nextEnd-1 {
                                   var u=dstR[e1];
                                   forall e2 in e1+1..nextEnd {
                                       var v=dstR[e2];
                                       if u<v {
                                           JaccGamma[u*Nv+v].add(1);
                                       }
                                   }
                              }



                              forall e1 in nextStart..nextEnd {
                                   var u=dstR[e1];

                                   var    numNF2=nei[i];
                                   var    edgeId2=start_i[i];
                                   var nextStart2=edgeId2;
                                   var nextEnd2=edgeId2+numNF2-1;
                                   forall e2 in nextStart2..nextEnd2 {
                                       var v=dst[e2];
                                       if u<v {
                                           JaccGamma[u*Nv+v].add(1);
                                       } else {
                                          if u>v {
                                              JaccGamma[v*Nv+u].add(1);
                                          }
                                       }
                                   }
                              }


                       }
              }
          }//end coforall loc

          forall u in 0..Nv-2 {
             forall v in u+1..Nv-1 {
                  var tmpjac:real =JaccGamma[u*Nv+v].read();
                  if ((u<v) && (tmpjac>0.0)) {
                      JaccCoeff[u*Nv+v]=tmpjac/(nei[u]+nei[v]+neiR[u]+neiR[v]-tmpjac);
                      JaccCoeff[v*Nv+u]=JaccCoeff[u*Nv+v];
                      //writeln("d(",u,")=",nei[u]+neiR[u]," d(",v,")=", nei[v]+neiR[v], " Garmma[",u,",",v,"]=",tmpjac, " JaccCoeff[",u,",",v,"]=",JaccCoeff[u*Nv+v]);
                  }
             }
          }
          var JaccName = st.nextName();
          var JaccEntry = new shared SymEntry(JaccCoeff);
          st.addEntry(JaccName, JaccEntry);

          var jacMsg =  'created ' + st.attrib(JaccName);
          return jacMsg;

      }//end of 


      if (!Directed) {
                  repMsg=jaccard_coefficient_u(
                      toSymEntry(ag.getNEIGHBOR(), int).a,
                      toSymEntry(ag.getSTART_IDX(), int).a,
                      toSymEntry(ag.getSRC(), int).a,
                      toSymEntry(ag.getDST(), int).a,
                      toSymEntry(ag.getNEIGHBOR_R(), int).a,
                      toSymEntry(ag.getSTART_IDX_R(), int).a,
                      toSymEntry(ag.getSRC_R(), int).a,
                      toSymEntry(ag.getDST_R(), int).a
                  );
                  
 
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
