module ConnectedComponents {
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

  /* Given a `SegGraph` object, compute the connected components of the graph. */
  proc connectedComponents(graph: SegGraph) throws {
    var src = if graph.isReversed() then toSymEntry(graph.getComp("SRC_RDI"),int).a
              else toSymEntry(graph.getComp("SRC_SDI"),int).a;
    var dst = if graph.isReversed() then toSymEntry(graph.getComp("DST_RDI"),int).a
              else toSymEntry(graph.getComp("DST_SDI"),int).a;
    var Nv = graph.n_vertices;

    return connectedComponents(src, dst, Nv);
  }
  
  /* Given source and destination arrays, compute the connected components of the graph. */
  proc connectedComponents(src: [?Ds] int, dst: [?Dd] int, Nv: int) throws {
    var f = makeDistArray(Nv, int); 
    var af = makeDistArray(Nv, atomic int); 
    var converged:bool = false;
    var count:int=0;
    var itera = 1;
    var myefficiency:real;
    var executime:real;
    coforall loc in Locales with (ref af) do on loc {
      forall i in f.localSubdomain() with (ref af) do af[i].write(i);
    }
    while(!converged) {
      coforall loc in Locales with ( + reduce count, ref af ) do on loc {
        var localf:[0..Nv-1] atomic int;
        var lconverged:bool = false;
        var litera = 1;
        var lcount:int=0;
        forall i in 0..Nv-1 with (ref af) do localf[i].write(af[i].read());
        while (!lconverged) {
          forall x in src.localSubdomain() with (+ reduce lcount) {
            var u = src[x];
            var v = dst[x];
            var TmpMin:int;
            var fu=localf[u].read();
            var fv=localf[v].read();
            TmpMin=min(localf[fu].read(),localf[fv].read());
            var oldx=localf[u].read();
            while (oldx>TmpMin) {
              if (localf[u].compareAndSwap(oldx,TmpMin)) then u=oldx;
              oldx=localf[u].read();
              lcount+=1;
            }
            oldx=localf[v].read();
            while (oldx>TmpMin) {
              if (localf[v].compareAndSwap(oldx,TmpMin)) then v=oldx;
              oldx=localf[v].read();
              lcount+=1;
            }
            oldx=localf[fu].read();
            while (oldx>TmpMin) {
              if (localf[fu].compareAndSwap(oldx,TmpMin)) then fu=oldx;
              oldx=localf[fu].read();
              lcount+=1;
            }
            oldx=localf[fv].read();
            while (oldx>TmpMin) {
              if (localf[fv].compareAndSwap(oldx,TmpMin)) then fv=oldx;
              oldx=localf[fv].read();
              lcount+=1;
            }
          }
          if(lcount==0) then lconverged = true;
          else { lconverged = false; lcount=0; }
          litera+=1;
        }
        forall i in 0..Nv-1 with (+ reduce count) {
          var old=af[i].read();
          var newval=localf[i].read();
          while old>newval {
            af[i].compareAndSwap(old,newval);
            old=af[i].read();
            count+=1;
          }
        }
      }
      if(count==0) then converged = true;
      else { converged = false; count=0; }
      itera += 1;
    }
    forall i in 0..Nv-1 with (+ reduce count) do f[i]=af[i].read();
    return f;
  }

  proc connectedComponentsLocal(src: [?Ds] int, dst: [?Dd] int, Nv: int) throws {
    var f: [0..<Nv] int; 
    var af: [0..<Nv] atomic int; 
    var converged:bool = false;
    var count:int=0;
    var itera = 1;
    var myefficiency:real;
    var executime:real;
    forall i in af.domain do af[i].write(i);
    while(!converged) {
      var localf:[0..Nv-1] atomic int;
      var lconverged:bool = false;
      var litera = 1;
      var lcount:int=0;
      forall i in 0..Nv-1 with (ref af) do localf[i].write(af[i].read());
      while (!lconverged) {
        forall x in src.domain with (+ reduce lcount) {
          var u = src[x];
          var v = dst[x];
          var TmpMin:int;
          var fu=localf[u].read();
          var fv=localf[v].read();
          TmpMin=min(localf[fu].read(),localf[fv].read());
          var oldx=localf[u].read();
          while (oldx>TmpMin) {
            if (localf[u].compareAndSwap(oldx,TmpMin)) then u=oldx;
            oldx=localf[u].read();
            lcount+=1;
          }
          oldx=localf[v].read();
          while (oldx>TmpMin) {
            if (localf[v].compareAndSwap(oldx,TmpMin)) then v=oldx;
            oldx=localf[v].read();
            lcount+=1;
          }
          oldx=localf[fu].read();
          while (oldx>TmpMin) {
            if (localf[fu].compareAndSwap(oldx,TmpMin)) then fu=oldx;
            oldx=localf[fu].read();
            lcount+=1;
          }
          oldx=localf[fv].read();
          while (oldx>TmpMin) {
            if (localf[fv].compareAndSwap(oldx,TmpMin)) then fv=oldx;
            oldx=localf[fv].read();
            lcount+=1;
          }
        }
        if(lcount==0) then lconverged = true;
        else { lconverged = false; lcount=0; }
        litera+=1;
      }
      forall i in 0..Nv-1 with (+ reduce count) {
        var old=af[i].read();
        var newval=localf[i].read();
        while old>newval {
          af[i].compareAndSwap(old,newval);
          old=af[i].read();
          count+=1;
        }
      }
      if(count==0) then converged = true;
      else { converged = false; count=0; }
      itera += 1;
    }
    forall i in 0..Nv-1 with (+ reduce count) do f[i]=af[i].read();
    return f;
  }
}// end of ConnectedComponents module