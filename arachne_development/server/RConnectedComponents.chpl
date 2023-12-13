module RConnectedComponents {
    // Chapel modules.
    use Reflection;
    use Set;
    use List;

    // Package modules.
    use CopyAggregation;

    // Arachne modules.
    use GraphArray;
    use Utils;
    use Aggregators;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use AryUtil;

    inline proc find_split_h(u:int, ref parents:[?D1] int, h:int):int {
       var  t=0;
       var i=u;
       var v,w:int;
       while (t<h) {
          v = parents[i];
          w = parents[v];
          if (v == w) {
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

    // Contour connected components a mapping based connected components algorithm
    proc cc_mm(graph: SegGraph) throws {
      // Initialize the parent vectors f that will form stars. 
      var f = makeDistArray(graph.n_vertices, int); 
    //   var localtimer:Timer;
      var myefficiency:real;
      var executime:real;
      var ORDERH:int = 512;
      const LargeScale=1000000;
      var src = toSymEntry(graph.getComp("SRC"),int).a;
      var dst = toSymEntry(graph.getComp("DST"),int).a;
      var srcR = toSymEntry(graph.getComp("SRC_R"),int).a;
      var dstR = toSymEntry(graph.getComp("DST_R"),int).a;
      var start_i = toSymEntry(graph.getComp("START_IDX"),int).a;
      var start_iR = toSymEntry(graph.getComp("START_IDX_R"),int).a;
      var nei = toSymEntry(graph.getComp("NEIGHBOR"),int).a;
      var neiR = toSymEntry(graph.getComp("NEIGHBOR_R"),int).a;
      var Ne = graph.n_edges;

      coforall loc in Locales with (ref f) {
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

      var converged:bool = false;
      var itera = 1;
      var count:int=0;
      if (Ne/here.numPUs() < LargeScale) {
           ORDERH=2;
      }else {
           ORDERH=1024;
      }  
      //we first check with order=1 mapping method
      while( (!converged) ) {
        // In the second step, we employ high order mapping
        // localtimer.clear();
        // localtimer.start(); 

        if (ORDERH==2) {
            coforall loc in Locales with ( + reduce count , ref f) {
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
        } else {
            coforall loc in Locales with ( + reduce count, ref f ) {
              on loc {
                var edgeBegin = src.localSubdomain().lowBound;
                var edgeEnd = src.localSubdomain().highBound;

                forall x in edgeBegin..edgeEnd  with ( + reduce count)  {
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
        // writeln("My Order is ",ORDERH); 
        // localtimer.stop(); 
        // executime=localtimer.elapsed();
        // myefficiency=(Ne:real/executime/1024.0/1024.0/here.numPUs():real):real;
        // writeln("Efficiency is ", myefficiency, " time is ",executime);
      }

    //   writeln("Number of iterations = ", itera-1);

      return f;
    }

    
}// end of ConnectedComponents module
