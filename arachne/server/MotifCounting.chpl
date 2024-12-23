module MotifCounting {
  // Chapel modules.
  use Reflection;
  use List;
  use Random;
  use List;
  use IO;
  use Time;
  use Set;
  use Map;
  use CommDiagnostics;
  use Collectives;
  use Sort;

  // Arachne modules.
  use GraphArray;
  use Utils;
  use MotifCountingMsg;
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use MultiTypeRegEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;
  use SymArrayDmap;
  use Logging;


class KavoshState {
    var n: int;
    var k: int;
    var maxDeg: int;

    var visited: [0..<n] bool;

    // subgraph[level][0] = count; subgraph[level][1..count] = vertices
    var subgraph: [0..<k, 0..maxDeg] int;

    // childSet[level][0] = count; childSet[level][1..count] = children
    var childSet: [0..<k, 0..maxDeg] int;

    // indexMap[level][i] maps selection order for revolve-door algorithm
    var indexMap: [0..<k, 0..maxDeg] int;

    var subgraphCount: int;

    proc init(n: int, k: int, maxDeg: int) {
      this.n = n;
      this.k = k;
      this.maxDeg = maxDeg;
      this.visited = false;
      this.subgraph = 0;
      this.childSet = 0;
      this.indexMap = 0;
      this.subgraphCount = 0;
    }

    proc reset() {
      this.visited = false;
      this.subgraph = 0;
      this.childSet = 0;
      this.indexMap = 0;
      this.subgraphCount = 0;
    }
  }// End of KavoshState


  proc runMotifCounting(g1: SegGraph, g2: SegGraph, semanticCheckType: string, 
              sizeLimit: string, in timeLimit: int, in printProgressInterval: int,
              algType: string, returnIsosAs:string, st: borrowed SymTab) throws {
    var numIso: int = 0;

    // Extract the g1/G/g information from the SegGraph data structure.
    const ref srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    const ref dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    const ref segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
    const ref dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
    const ref segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;

    // Get the number of vertices and edges for each graph.
    var nG1 = nodeMapGraphG1.size;
    var mG1 = srcNodesG1.size;


    // Returns the map of attribute name to tuple of symbol table identifier and array data type
    // to be used to extract a given attribute array.
    var graphNodeAttributes = g1.getNodeAttributes();
    var graphEdgeAttributes = g1.getEdgeAttributes();


    // Gathers unique valid neighbors for the current level.
    proc initChildSet(ref state: KavoshState, root: int, level: int) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("====== initChildSet called for level ", level, " and root ", root, " ======");
      }

      state.childSet[level,0] = 0;
      const parentsCount = state.subgraph[level-1,0];

      // For each vertex chosen at the previous level, get its neighbors
      for p in 1..parentsCount {
        const parent = state.subgraph[level-1,p];

        // Collect all neighbors (both in and out) in a domain to ensure uniqueness
        var neighbours: domain(int, parSafe=true);

        // Outgoing neighbors
        var outNeighbors = dstNodesG1[segGraphG1[parent]..<segGraphG1[parent+1]];
        neighbours += outNeighbors;

        // Incoming neighbors
        var inNeighbors = dstRG1[segRG1[parent]..<segRG1[parent+1]];
        neighbours += inNeighbors;

        // Add each outNeighbor to childSet if it passes criteria
        for neighbor in neighbours {
          // Must be greater than root and not visited
          if neighbor > root && !state.visited[neighbor] {
            // Check for duplicates in current childSet
            var exists = false;
            for j in 1..state.childSet[level,0] {
              if state.childSet[level,j] == neighbor {
                exists = true;
                break;
              }
            }
            // If new, add it and mark visited
            if !exists {
              state.childSet[level,0] += 1;
              state.childSet[level, state.childSet[level,0]] = neighbor;
              state.visited[neighbor] = true;
            }
          }
        }
      }

      if logLevel == LogLevel.DEBUG {
        writeln("initChildSet: Found ", state.childSet[level,0], " valid children at level ", level);
        write("Children: ");
        for i in 1..state.childSet[level,0] {
          write(state.childSet[level,i], " ");
        }
        writeln();
      }
    }// End of initChildSet

    proc prepareNaugtyArguments(ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("===== prepareNaugtyArguments called =====");
      }

      // Build an array for the chosen vertices in this subgraph
      var chosenVerts: [1..state.k] int;
        // subgraph[i, 1..subgraph[i,0]] are chosen at that level
        // but each level of Kavosh picks a certain number of vertices.
        // Combine them in order. The total number selected = k.
        // The order in subgraph is the order of selection.
        // Each subgraph[i,0] > 0 means we selected some vertices at that level.
        // Flatten them into chosenVerts in ascending order of level.
        var idx = 1;
        for i in 0..<state.k {
          for x in 1..state.subgraph[i,0] {
            chosenVerts[idx] = state.subgraph[i,x];
            idx += 1;
          }
        }
        // Create and initialize adjacency matrix from chosenVerts
        var adjMatrix: [0..#(state.k * state.k)] int;

        for i in 0..#state.k {
            for j in 0..#state.k {
                if i != j {
                    var u = chosenVerts[i+1]; // +1 because chosenVerts is 1-based
                    var w = chosenVerts[j+1];
                    var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                    if eid != -1 {
                      adjMatrix[i * state.k + j] = 1;
                    } else{
                      adjMatrix[i * state.k + j] = 0;
                    }
                }
            }
        }
        if logLevel == LogLevel.DEBUG {
          // Print the mapping
          writeln("Vertex to Index mapping:");
          for i in 1..state.k {
              writeln("Vertex ", chosenVerts[i], " -> Index ", i-1);
          }


          // Print the adjacency matrix as 1D array
          writeln("\nAdjacency Matrix (1D):");
          for i in 0..#(state.k * state.k) {
              write(adjMatrix[i], " ");
          }

          // Print it in 2D format for better visualization
          writeln("\nAdjacency Matrix (2D visualization):");
          for i in 0..#state.k {
              for j in 0..#state.k {
                  write(adjMatrix[i * state.k + j], " ");
              }
              writeln();
          }
          writeln();
        }
      return (adjMatrix, chosenVerts);
    }// End of prepareNaugtyArguments

    // Explores subgraphs containing the root vertex,
    // expanding level by level until remainder = 0 (which means we have chosen k vertices).
    proc Explore(ref state: KavoshState, root: int, level: int, remainder: int) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("===== Explore called =====");
        writeln("Current root: ", root, " level: ", level, " remainder: ", remainder);
        writeln("Visited Array: ", state.visited);
        writeln("Current partial subgraph:");
        for l in 0..<level {
          write("Level ", l, " (count=", state.subgraph[l,0], "): ");
          for x in 1..state.subgraph[l,0] {
            write(state.subgraph[l,x], " ");
          }
          writeln();
        }
        writeln("==========================");
      }

      // Base case: all k vertices chosen
      if remainder == 0 {
        state.subgraphCount += 1;
        if logLevel == LogLevel.DEBUG {
          writeln("Found complete subgraph #", state.subgraphCount);
          for l in 0..<state.k {
            write("Level ", l, ": ");
            for x in 1..state.subgraph[l,0] {
              write(state.subgraph[l,x], " ");
            }
            writeln();
          }
          writeln("Now we make adjMatrix to pass to Naught");
        } 
        var (A, B) = prepareNaugtyArguments(state);
        // This the place that we should call nautyCaller from cpp
        // Then we should Classify based on label that naugty will give.
        writeln("A is: ",A);
        writeln("B is: ",B);
        

        return;
      }

      // Get children for this level
      initChildSet(state, root, level);
      const childCount = state.childSet[level,0];

      // Try all possible selection sizes at this level, from 1 to remainder
      for selSize in 1..remainder {
        if childCount < selSize {
          // Not enough children to form this selection
          if logLevel == LogLevel.DEBUG {
            writeln("Not enough children (", childCount, ") to select ", selSize, " vertices at level ", level);
          }
          // Unmark visited children before returning
          for i in 1..childCount {
            state.visited[state.childSet[level,i]] = false;
          }
          return;
        }

        // Initial selection: pick the first selSize children
        state.subgraph[level,0] = selSize;
        for i in 1..selSize {
          state.subgraph[level,i] = state.childSet[level,i];
          state.indexMap[level,i] = i;
        }

        if logLevel == LogLevel.DEBUG {
          writeln("Exploring with initial selection of size ", selSize, " at level ", level);
          write("Selected vertices: ");
          for i in 1..selSize {
            write(state.subgraph[level,i], " ");
          }
          writeln("we will Recurse with chosen selection");
          writeln();
        }

        // Recurse with chosen selection
        Explore(state, root, level+1, remainder - selSize);

        // Generate other combinations using revolve-door algorithm
        ForwardGenerator(childCount, selSize, root, level, remainder, selSize, state);
      }

      // Cleanup: Unmark visited children before going up
      for i in 1..childCount {
        state.visited[state.childSet[level,i]] = false;
      }
      state.subgraph[level,0] = 0;
    }// End of Explore

    // I read this for implementing revolving door 
    // https://encyclopediaofmath.org/wiki/Gray_code#Combinations.2C_partitions.2C_permutations.2C_and_other_objects.

    // swapping: Used by revolve-door Gray code generation to swap two elements
    // and then immediately Explore with the new combination.
    proc swapping(i: int, j: int, root: int, level: int, remainder: int, m: int, ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("swapping called: swapping indices ", i, " and ", j, " at level ", level);
        writeln("Before swapping: indexMap[level,i] = ", state.indexMap[level,i], 
                " indexMap[level,j] = ", state.indexMap[level,j]);
      }

      state.indexMap[level,i] = state.indexMap[level,j];
      state.subgraph[level, state.indexMap[level,i]] = state.childSet[level,i];

      if logLevel == LogLevel.DEBUG {
        writeln("After swapping: subgraph[level,indexMap[level,i]] = childSet[level,i] = ", state.childSet[level,i]);
        writeln("Now calling Explore after swapping");
      }

      Explore(state, root, level+1, remainder - m);
    }// End of swapping

    // ForwardGenerator(GEN): Part of revolve-door combination Forward Generator 
    proc ForwardGenerator(n: int, k: int, root: int, level: int, remainder: int, m: int, ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("ForwardGenerator called with n=", n, " k=", k, " level=", level, " remainder=", remainder, " m=", m);
      }

      if k > 0 && k < n {
        ForwardGenerator(n-1, k, root, level, remainder, m, state);

        if k == 1 {
          if logLevel == LogLevel.DEBUG {
            writeln("ForwardGenerator: k=1 case, calling swapping(n, n-1) => swapping(", n, ", ", n-1, ")");
          }
          swapping(n, n-1, root, level, remainder, m, state);
        } else {
          if logLevel == LogLevel.DEBUG {
            writeln("GEN: k>1 case, calling swapping(n, k-1) => swapping(", n, ", ", k-1, ")");
          }
          swapping(n, k-1, root, level, remainder, m, state);
        }

        reverseGenerator(n-1, k-1, root, level, remainder, m, state);
      }
    }// End of ForwardGenerator

    // reverseGenerator(NEG): Another part of revolve-door combination generation logic
    proc reverseGenerator(n: int, k: int, root: int, level: int, remainder: int, m: int, ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("reverseGenerator called with n=", n, " k=", k, " level=", level, " remainder=", remainder, " m=", m);
      }

      if k > 0 && k < n {
        ForwardGenerator(n-1, k-1, root, level, remainder, m, state);

        if k == 1 {
          if logLevel == LogLevel.DEBUG {
            writeln("reverseGenerator: k=1 case, calling swapping(n-1, n) => swapping(", n-1, ", ", n, ")");
          }
          swapping(n-1, n, root, level, remainder, m, state);
        } else {
          if logLevel == LogLevel.DEBUG {
            writeln("reverseGenerator: k>1 case, calling swapping(k-1, n) => swapping(", k-1, ", ", n, ")");
          }
          swapping(k-1, n, root, level, remainder, m, state);
        }

        reverseGenerator(n-1, k, root, level, remainder, m, state);
      }
    }// End of reverseGenerator

    // Enumerate: Iterates over all vertices as potential roots
    // and calls Explore to find all subgraphs of size k containing that root.
    proc Enumerate(ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("Enumerate: starting enumeration over all vertices");
      }

      for v in 0..<state.n {
        if logLevel == LogLevel.DEBUG {
          writeln("Root = ", v, " (", v+1, "/", state.n, ")");
        }

        state.subgraph[0,0] = 1;
        state.subgraph[0,1] = v;
        state.visited[v] = true;

        Explore(state, v, 1, state.k - 1);

        state.visited[v] = false;
      }

      if logLevel == LogLevel.DEBUG {
        writeln("Enumerate: finished enumeration over all vertices");
      }
    }// End of Enumerate

    // Encode the pattern of a k-sized subgraph.
    // subgraphVerts: the vertices chosen for the subgraph.
    // We assume subgraphVerts are in `state.subgraph[l,x]` arrays.
    // We'll gather them into a temporary array for convenience.
    proc encodePattern(k: int, subgraphVerts: [1..k] int): uint(64) throws{
      var pattern: uint(64) = 0;
      var pos = 0;

      // We'll consider each pair (i,j) to set pattern bit
      // Flatten row-major: for i in [1..k], j in [1..k], i,j distinct
      // If edge from subgraphVerts[i] -> subgraphVerts[j] exists, set bit.
      for i in 1..k {
        for j in 1..k {
          // Usually self-loops are 0 unless you have them. Let's just check edges if i!=j.
          if i != j {
            var u = subgraphVerts[i];
            var w = subgraphVerts[j];
            var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
            if eid != -1 {
              pattern |= 1:uint(64) << pos;
            }
          }
          pos += 1;
        }
      }
      if logLevel == LogLevel.DEBUG {
        writeln("subgraphVerts= ", subgraphVerts);
        writeln("encodePattern called and pattern= ", pattern);
      }
      return pattern;
    }
////////////////////////////////////////////////////////////////////////////////
    // Setup the problem
    var n = nodeMapGraphG1.size;
    var k = 3; // Looking for motifs of size 3
    var nodeDegree: [0..<n] int;

    forall v in 0..<n with (ref nodeDegree) {
      var Tin = dstRG1[segRG1[v]..<segRG1[v+1]];
      var Tout = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
      nodeDegree[v] = Tin.size + Tout.size;
    }
    var maxDeg = max reduce nodeDegree;

    // Instead of a single Enumerate, we now parallelize over each root
    // Each root runs independently with its own KavoshState.
    var atomicGlobalCount: atomic int; // atomic counter for global subgraph count
    atomicGlobalCount.write(0);
/*
    coforall v in 0..<n with(ref atomicGlobalCount) {
      // Create a local state for this root
      var localState = new KavoshState(n, k, maxDeg);

      // Initialize the root vertex
      localState.subgraph[0,0] = 1;
      localState.subgraph[0,1] = v;
      localState.visited[v] = true;

      // Explore subgraphs starting from this root
      Explore(localState, v, 1, k - 1);

      // Add local count to global
      atomicGlobalCount.add(localState.subgraphCount);
    }

    if logLevel == LogLevel.DEBUG {
      // After all tasks complete, we have the total subgraph count
      writeln("\nTotal subgraphs found: ", atomicGlobalCount.read());
    }
    */

    var state = new KavoshState(n, k, maxDeg);

    if logLevel == LogLevel.DEBUG {
      writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
      writeln("Maximum degree: ", maxDeg);
    }

    // Execute enumeration
    Enumerate(state);

    if logLevel == LogLevel.DEBUG {
      writeln("\nTotal motif found: ", state.subgraphCount);
      writeln();
    }

    var tempArr: [0..0] int;
    var srcPerIso = makeDistArray(2*2, int);
    var dstPerIso = makeDistArray(2*2, int);
    return (srcPerIso, dstPerIso, tempArr, tempArr);
  }// End of runMotifCounting

}// End of MotifCounting Module