module Diameter {
  // Chapel modules.
  use Set;
  use Time;

  // Package modules.
  use LinearAlgebra;

  // Arachne modules.
  use BreadthFirstSearch;
  use GraphArray;

  proc componentIter(g:SegGraph, root:int, gdiameter:int, iternum:int): int throws {
    var cur_level = 0;
    var diameter = gdiameter;
    var i:int = 0;
    var maxv:int;
    var tmpr = root;
    while i < iternum {
      var depth = makeDistArray(g.n_vertices, int);
      depth = -1;
      if numLocales == 1 then maxv = bfs_kernel_und_smem(g, tmpr, depth, returnMax=true);
      else maxv = bfs_kernel_und_dmem_opt(g, tmpr, depth, returnMax=true);

      if cur_level <= diameter then break;
      diameter = max(diameter,cur_level);
      tmpr = maxv;
      i += 1;
    }
    return diameter;
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

  proc connectedComponentDiameter(graph:SegGraph): int throws {
    var src = toSymEntry(graph.getComp("SRC_RDI"),int).a;
    var dst = toSymEntry(graph.getComp("DST_RDI"),int).a;
    var srcR = toSymEntry(graph.getComp("SRC_R_RDI"),int).a;
    var dstR = toSymEntry(graph.getComp("DST_R_RDI"),int).a;
    var start_i = toSymEntry(graph.getComp("START_IDX_RDI"),int).a;
    var start_iR = toSymEntry(graph.getComp("START_IDX_R_RDI"),int).a;
    var nei = toSymEntry(graph.getComp("NEIGHBOR_RDI"),int).a;
    var neiR = toSymEntry(graph.getComp("NEIGHBOR_R_RDI"),int).a;
    var Ne = graph.n_edges;
    var Nv = graph.n_vertices;

    var f = makeDistArray(Nv, int); 
    var af = makeDistArray(Nv, atomic int); 
    var converged:bool = false;
    var itera = 1;
    var count:int=0;
    var localtimer:stopwatch;
    var myefficiency:real;
    var executime:real;
    var ORDERH:int=512;
    const LargeScale=1000000;

    coforall loc in Locales with (ref af) do on loc {
      forall i in f.localSubdomain() with (ref af) do af[i].write(i);
    }

    if (Ne/here.numPUs() < LargeScale) then ORDERH=2;
    else ORDERH=1024;

    while !converged {
      coforall loc in Locales with ( + reduce count , ref af ) do on loc {
        var localf:[0..Nv-1] atomic int;
        var lconverged:bool = false;
        var litera = 1;
        var lcount:int=0;
        forall i in 0..Nv-1 do localf[i].write(af[i].read());

        while (!lconverged) {
          forall x in src.localSubdomain() with ( + reduce lcount) {
            var u = src[x];
            var v = dst[x];
            var TmpMin:int;

            var fu=find_split_atomic_h(u,localf,ORDERH);
            var fv=find_split_atomic_h(v,localf,ORDERH);
            TmpMin=min(fu,fv);
            var oldx=localf[u].read();
            while (oldx>TmpMin) {
              if (localf[u].compareAndSwap(oldx,TmpMin)) then u=oldx;
              oldx=localf[u].read();
              lcount+=1;
            }
            oldx=localf[v].read();
            while (oldx>TmpMin) {
              if (localf[v].compareAndSwap(oldx,TmpMin)) then u=oldx;
              oldx=localf[v].read();
              lcount+=1;
            }
          }
          if( (lcount==0) ) then lconverged = true;
          else { lconverged = false; lcount=0;}
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
      if( (count==0) ) then converged = true;
      else { converged = false; count=0; }
      itera += 1;
    }
    forall i in 0..Nv-1 with (+ reduce count) do f[i]=af[i].read();

    var CompSet = new set(int,parSafe = true);
    for i in f do CompSet.add(i);
    writeln("Size of the Components=",CompSet.size);
    writeln("The components are as follows");
    writeln(CompSet);
    writeln("Size of the Components=",CompSet.size);

    var largestD=0:int;
    var diameter=0:int ;
    for i in CompSet  {
      writeln("Handle component ",i);
      var numV=f.count(i);
      if numV<=max(2,largestD) {
        writeln("no more than  two or ", largestD, " vertices, contiune");
        continue;
      }
      if numV>2500 {
        writeln("Enter BFS method");
        writeln("*************************************");
        diameter=componentIter(graph, i, largestD, 10);
        writeln("Pass 1 The diameter of component ", i, "=", diameter);
        largestD=max(largestD,diameter);
      } else {
        writeln("----------------------------------------");
        writeln("Allocate ",numV,"X",numV," matrix");
        var AdjMatrix=Matrix(numV,numV,eltType=int);
        AdjMatrix=0;
        forall j in 0..numV-1 with (ref AdjMatrix) {
          AdjMatrix[j,j]=1;
        }
        var mapary=f;
        var tmpmap=0:int;
        for k in 0..f.size-1 {
          if f[k]==i {
            mapary[k]=tmpmap;
            tmpmap+=1;
          }
        }
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
              if j!=dst[k] then diameter=1;
            }      
          }
        }
        if (numV<20) {
          writeln("The adjacency matrix ",numV,"X",numV," is as follows");
          writeln(AdjMatrix);
        } else {
          writeln("It is a ",numV,"X",numV," AdjMatrix");
        }

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
        while havezero && Mk.size>1 {
          var MM= matPow(Mk, 2);
          k=k+1;
          Mk=MM;
          havezero=false;
          forall x in Mk with (ref havezero) {
            if x==0 then havezero=true;
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
            if x==0 then havezero=true;
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
    return largestD;
  }
}