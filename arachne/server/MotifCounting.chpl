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
  }


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
 // initChildSet mimics the C++ initChildSet function
  // It gathers the neighbors of all parents in the previous level, filters them,
  // and puts them in childSet[level].
  proc initChildSet(ref state: KavoshState, root: int, level: int) {

    state.childSet[level,0] = 0;

    const parentsCount = state.subgraph[level-1,0];
    for p in 1..parentsCount {
      const parent = state.subgraph[level-1,p];


        // Create a domain to store all unique neighbors
        var neighbours: domain(int, parSafe=true);
        
        // Get outgoing neighbors
        var outNeighbors = dstNodesG1[segGraphG1[parent]..<segGraphG1[parent+1]];
        neighbours += outNeighbors;

        // Get incoming neighbors
        var inNeighbors = dstRG1[segRG1[parent]..<segRG1[parent+1]];
        neighbours += inNeighbors;

      for neighbor in neighbours {
        if neighbor > root && !state.visited[neighbor] {
          // Check if already in childSet
          var exists = false;
          for j in 1..state.childSet[level,0] {
            if state.childSet[level,j] == neighbor {
              exists = true;
              break;
            }
          }
          if !exists {
            state.childSet[level,0] += 1;
            state.childSet[level,state.childSet[level,0]] = neighbor;
            state.visited[neighbor] = true; // Mark visited now
          }
        }
      }
    }
  }


  proc Explore(ref state: KavoshState, root: int, level: int, remainder: int) {
    if remainder == 0 {
      state.subgraphCount += 1;
      // Print the found subgraph if needed
      writeln("Found subgraph #", state.subgraphCount, ": ");
      for l in 0..<state.k {
        write("Level ", l, ": ");
        for x in 1..state.subgraph[l,0] {
          write(state.subgraph[l,x], " ");
        }
        writeln();
      }
      return;
    }

    initChildSet(state, root, level);

    const childCount = state.childSet[level,0];

    for selSize in 1..remainder {
      if childCount < selSize {
        // Not enough children to form this selection
        // Unvisit them before returning
        for i in 1..childCount {
          state.visited[state.childSet[level,i]] = false;
        }
        return;
      }

      // Initial selection
      state.subgraph[level,0] = selSize;
      for i in 1..selSize {
        state.subgraph[level,i] = state.childSet[level,i];
        state.indexMap[level,i] = i;
      }

      // Recurse with this selection
      Explore(state, root, level+1, remainder - selSize);

      // Generate other combinations with revolve-door
      GEN(childCount, selSize, root, level, remainder, selSize, state);
    }

    // Cleanup: unmark visited
    for i in 1..childCount {
      state.visited[state.childSet[level,i]] = false;
    }

    state.subgraph[level,0] = 0;
  }

// I read this for implemnting revolving door 
// https://encyclopediaofmath.org/wiki/Gray_code#Combinations.2C_partitions.2C_permutations.2C_and_other_objects.
 // Explore function: Explores subgraphs containing the root vertex

  // swap function from revolve-door logic
  proc swap(i: int, j: int, root: int, level: int, remainder: int, m: int, ref state: KavoshState) {
    state.indexMap[level,i] = state.indexMap[level,j];
    state.subgraph[level, state.indexMap[level,i]] = state.childSet[level,i];

    Explore(state, root, level+1, remainder - m);
  }

  // GEN function from revolve-door logic
  proc GEN(n: int, k: int, root: int, level: int, remainder: int, m: int, ref state: KavoshState) {
    if k > 0 && k < n {
      GEN(n-1, k, root, level, remainder, m, state);

      if k == 1 {
        swap(n, n-1, root, level, remainder, m, state);
      } else {
        swap(n, k-1, root, level, remainder, m, state);
      }

      NEG(n-1, k-1, root, level, remainder, m, state);
    }
  }

  // NEG function from revolve-door logic
  proc NEG(n: int, k: int, root: int, level: int, remainder: int, m: int, ref state: KavoshState) {
    if k > 0 && k < n {
      GEN(n-1, k-1, root, level, remainder, m, state);

      if k == 1 {
        swap(n-1, n, root, level, remainder, m, state);
      } else {
        swap(k-1, n, root, level, remainder, m, state);
      }

      NEG(n-1, k, root, level, remainder, m, state);
    }
  }

  proc Enumerate(ref state: KavoshState) {
    for v in 0..<state.n {
      state.subgraph[0,0] = 1;
      state.subgraph[0,1] = v;
      state.visited[v] = true;
      Explore(state, v, 1, state.k - 1);
      state.visited[v] = false;
    }
  }

////////////////////////////////////////////////////////////////////////////////
    var n = nodeMapGraphG1.size;
    var k = 4; // for example, as given
    var nodeDegree: [0..<n] int;

    forall v in 0..<n with (ref nodeDegree) {
      var Tin = dstRG1[segRG1[v]..<segRG1[v+1]];
      var Tout = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
      nodeDegree[v] = Tin.size + Tout.size;
    }
    var maxDeg = max reduce nodeDegree;

    var state = new KavoshState(n, k, maxDeg);
    Enumerate(state);

    writeln("Total subgraphs found: ", state.subgraphCount);

    var tempArr: [0..0] int;
    var srcPerIso = makeDistArray(2*2, int);
    var dstPerIso = makeDistArray(2*2, int);
    return (srcPerIso, dstPerIso, tempArr, tempArr);
  }
}