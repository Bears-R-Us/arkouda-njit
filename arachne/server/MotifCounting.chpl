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
//   use SubgraphIsomorphismMsg;
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

  /* Memory-efficient state management for large graphs */
class KavoshState {
    var n: int;              // Number of vertices
    var k: int;              // Motif size
    var visited: [0..<n] bool;
    var pattern: [0..<k] int;  // Fixed-size array instead of list
    var patternSize: int;      // Track current size
    var motifCounts: map(string, atomic int);

    var seenPatterns = new set(string);

    // Track memory usage
    var totalPatterns: atomic int = 0;
    var maxPatternSize: atomic int = 0;

    // Statistics tracking
    var patternStats = new map(string, (int, real, real)); // (frequency, zscore, pvalue)
 
     // Store random distributions:
    // For each motif (identified by label), we store an array of frequencies from random graphs
    var randomDistributions = new map(string, list(int));

    proc init(n: int, k: int) {
        if logLevel == LogLevel.DEBUG {
            writeln("Initializing KavoshState: n=", n, " Looking for motifs of size k=", k);
        }
        this.n = n;
        this.k = k;
        this.visited = false;
        this.pattern = -1;     // Initialize with invalid vertex values
        this.patternSize = 0;
        this.motifCounts = new map(string, atomic int);
    }

    proc reset() {
        if logLevel == LogLevel.DEBUG {
            writeln("Resetting KavoshState");
        }
        this.visited = false;
        this.pattern = -1;
        this.patternSize = 0;
    }

    /* Add vertex to pattern */
    proc addToPattern(v: int) {
        if logLevel == LogLevel.DEBUG {
            writeln("Adding vertex ", v, " to pattern at position ", this.patternSize);
        }
        if this.patternSize < k {
            this.pattern[this.patternSize] = v;
            this.patternSize += 1;
            updateMemoryStats();
        }
    }

    /* Remove last vertex from pattern */
    proc removeFromPattern() {
        if logLevel == LogLevel.DEBUG {
            writeln("Removing last vertex from pattern at position ", this.patternSize-1);
        }
        if this.patternSize > 0 {
            this.pattern[this.patternSize-1] = -1;
            this.patternSize -= 1;
        }
    }

    /* Track memory usage */
    proc updateMemoryStats() {
        totalPatterns.add(1);
        maxPatternSize.write(max(maxPatternSize.read(), pattern.size));
    }

    /* Update statistics */
    proc updateStats(pattern: string, freq: int, zscore: real, pvalue: real) {
        patternStats[pattern] = (freq, zscore, pvalue);
    }

    /* Print statistics */
    proc printStats() {
        if logLevel == LogLevel.DEBUG {
            writeln("\n==== Pattern Statistics ====");
            writeln("Total unique patterns: ", motifCounts.size);
            writeln("\nSignificant Motifs:");
            for pattern in patternStats.keys() {
                var (freq, zscore, pvalue) = patternStats[pattern];
                if isMotif(pattern, freq, zscore, pvalue) {
                    writeln("Pattern: ", pattern);
                    writeln("  Frequency: ", freq);
                    writeln("  Z-score: ", zscore);
                    writeln("  P-value: ", pvalue);
                }
            }
        }
    }

    /* Clean up resources */
    proc cleanup() {
        pattern.clear();
        motifCounts.clear();
        if logLevel == LogLevel.DEBUG {
            writeln("Processed ", totalPatterns.read(), " patterns");
            writeln("Maximum pattern size: ", maxPatternSize.read());
        }
    }
}


/* Identify if a pattern is a motif based on statistical criteria */
proc isMotif(pattern: string, freq: int, zscore: real, pvalue: real): bool {
    // Criteria from the paper
    const minFreq = 4;              // Minimum frequency threshold
    const pValueThreshold = 0.01;    // Maximum p-value threshold
    const minZScore = 1.0;          // Minimum z-score threshold

    var isSignificant = freq >= minFreq && 
                       pvalue < pValueThreshold && 
                       zscore > minZScore;

    if logLevel == LogLevel.DEBUG && isSignificant {
        writeln("Found significant motif:");
        writeln("  Frequency: ", freq, " (threshold: ", minFreq, ")");
        writeln("  Z-score: ", zscore, " (threshold: ", minZScore, ")");
        writeln("  P-value: ", pvalue, " (threshold: ", pValueThreshold, ")");
    }

    return isSignificant;
}

  class RandomizationState {
    var changedEdges = new map((int,int), int);
    var rng: randomStream(int);
    var nEdges: int;

    proc init(nEdges: int, seed: int = 12345) {
      this.rng = new randomStream(int, seed=seed);
      this.nEdges = nEdges;
      if logLevel == LogLevel.DEBUG {
        writeln("RandomizationState initialized with ", nEdges, " edges");
      }
    }
  }


  proc runMotifCounting(g1: SegGraph, g2: SegGraph, semanticCheckType: string, 
              sizeLimit: string, in timeLimit: int, in printProgressInterval: int,
              algType: string, returnIsosAs:string, st: borrowed SymTab) throws {
    var numIso: int = 0;
    var numIsoAtomic: chpl__processorAtomicType(int) = 0;
    var semanticAndCheck = if semanticCheckType == "and" then true else false;
    var semanticOrCheck = if semanticCheckType == "or" then true else false;
    var matchLimit = if sizeLimit != "none" then sizeLimit:int else 0;
    var limitSize:bool = if matchLimit > 0 then true else false;
    var limitTime:bool = if timeLimit > 0 then true else false;
    var stopper:atomic bool = false;
    timeLimit *= 60;

    // Extract the g1/G/g information from the SegGraph data structure.
    const ref srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    const ref dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    const ref segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
    const ref dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
    const ref segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;

    // Extract the g2/H/h information from the SegGraph data structure.
    const ref srcNodesG2 = toSymEntry(g2.getComp("SRC_SDI"), int).a;
    const ref dstNodesG2 = toSymEntry(g2.getComp("DST_SDI"), int).a;
    const ref segGraphG2 = toSymEntry(g2.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG2 = toSymEntry(g2.getComp("SRC_R_SDI"), int).a;
    const ref dstRG2 = toSymEntry(g2.getComp("DST_R_SDI"), int).a;
    const ref segRG2 = toSymEntry(g2.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG2 = toSymEntry(g2.getComp("VERTEX_MAP_SDI"), int).a;

    // Get the number of vertices and edges for each graph.
    var nG1 = nodeMapGraphG1.size;
    var mG1 = srcNodesG1.size;
    var nG2 = nodeMapGraphG2.size;
    var mG2 = srcNodesG2.size;

    // Returns the map of attribute name to tuple of symbol table identifier and array data type
    // to be used to extract a given attribute array.
    var graphNodeAttributes = g1.getNodeAttributes();
    var subgraphNodeAttributes = g2.getNodeAttributes();
    var graphEdgeAttributes = g1.getEdgeAttributes();
    var subgraphEdgeAttributes = g2.getEdgeAttributes();

    // If there are no vertex attributes, then check the edge attributes instead.
    var noVertexAttributes = if subgraphNodeAttributes.size == 0 then true else false;

    // To Oliver: Introduce a boolean or a parameter in runMotifCounting to decide

    var useRandomizationFlag: bool = false;

    // Execute core algorithm
    var n = g1.n_edges;
    var k = 3; // Oliver: This should be as an argument from Python side
    if logLevel == LogLevel.DEBUG {
      writeln("Starting motif counting for k=", k);
      writeln("Graph has ", n, " vertices and ", mG1, " edges");
      writeln("Randomization flag is set to ", useRandomizationFlag);
      writeln("Calling Kavosh.......................");
    }

    // Create RandomizationState
    //var rndState = new RandomizationState(mG1);
    var rndState: owned RandomizationState? = nil;
if useRandomizationFlag {
  // Initialize randomization
  rndState = new owned RandomizationState(mG1);
        var myState = rndState!;
        performEdgeSwaps(myState, 10000);
    } 

    // Call Kavosh with or without randomization
    var results: map(string, atomic int);
    if useRandomizationFlag {
        results = Kavosh(n, k, rndState);
    } else {
        results = Kavosh(n, k, nil);
    }
// performEdgeSwaps(rndState, 10000);// For example 10k swaps?!


    if logLevel == LogLevel.DEBUG {
    // Check point

    writeln("\nK=", k," Motif Summary:");
    writeln("Unique motifs found: ", results.size);
        
    // Print motif frequencies
    for key in results.keysToArray(){
      writeln("Motif: ", key, " Count: ", results[key].read());
    }


        writeln("\n==== Motif Finding Complete ====");
    }
 

    // performEdgeSwaps(rndState, 10000);// For example 10k swaps?!

    // // Pass rndState to Kavosh. Note rndState is optional. If you set rndState = nil, no randomization.
    // var results = Kavosh(n, k, rndState);


//////////////////// RandomizationState class ////////////////////////


  proc edgeToSrcOffset(E: int): (int,int) {
    // if logLevel == LogLevel.DEBUG {
    //   writeln("\n==== Starting edgeToSrcOffset ====");
    //   writeln("E: ", E);
    // }

    var low = 0;
    var high = segGraphG1.size - 2;
    while low <= high {
      var mid = (low+high)>>1;
      if segGraphG1[mid+1] <= E {
        low = mid+1;
      } else {
        high = mid-1;
      }
    }

    var src = low;

    // Verify that segGraphG1[src] <= E < segGraphG1[src+1]
    if src < 0 || src >= segGraphG1.size-1 {
      // Invalid src
      return (-1, -1);
    }

    if E < segGraphG1[src] || E >= segGraphG1[src+1] {
      // E not in the range of src's edges
      return (-1, -1);
    }
    var offset = E - segGraphG1[src];

    if logLevel == LogLevel.DEBUG {
      writeln("src is ", src, " and offset is ", offset);
    }
    return (src, offset);
  }

  proc srcOffsetToEdge(src: int, offset: int): int {
    return segGraphG1[src] + offset;
  }

  proc getDstForEdge(const ref rndState: RandomizationState, src: int, offset: int): int throws{
    if rndState.changedEdges.contains((src, offset)) {
      return rndState.changedEdges[(src, offset)];
    } else {
      var globalE = srcOffsetToEdge(src, offset);
      return dstNodesG1[globalE];
    }
  }

  proc performEdgeSwaps(ref rndState: RandomizationState, numSwaps: int) throws{
    
    if logLevel == LogLevel.DEBUG {
      writeln("\n==== Starting performEdgeSwaps ====");
      writeln("Performing ", numSwaps, " edge swaps...");
    }

    const E = rndState.nEdges;

    var numSwapsNew = numSwaps;

    if numSwaps > E then numSwapsNew = E;

    for attempt in 1..numSwapsNew {
      var e1 = rndState.rng.next() % E;
      var e2 = rndState.rng.next() % E;
      if e1 == e2 then continue;

      var (u1, off1) = edgeToSrcOffset(e1);
      var (u2, off2) = edgeToSrcOffset(e2);

      // Check validity
      if u1 == -1 || off1 == -1 || u2 == -1 || off2 == -1 {
        continue;         // Invalid edge mapping, skip this swap
      }

      var v1 = getDstForEdge(rndState, u1, off1);
      var v2 = getDstForEdge(rndState, u2, off2);

      if v1<0 || v1>=g1.n_vertices || v2<0 || v2>=g1.n_vertices{
        continue;// Invalid vertex index, skip
      }

      if u1 == v2 || u2 == v1 {
        continue;// Self loop would result, skip
      }

      rndState.changedEdges[(u1, off1)] = v2;
      rndState.changedEdges[(u2, off2)] = v1;

      if logLevel == LogLevel.DEBUG && attempt % 1000 == 0 {
        writeln("Swapped edges #", attempt, ": (", u1, "->", v1, ") with (", u2, "->", v2, ")");
      }
    }

    if logLevel == LogLevel.DEBUG {
      writeln("Completed edge swaps. Total changed edges: ", rndState.changedEdges.size);
    }
  }
//////////////////// End of RandomizationState ////////////////////////

 /********************************************
   * Using the Randomized Graph
   *
   * Now we have a RandomizationState with changedEdges.
   * We can define a function getNeighbors(u) that returns the neighbors of u
   * under the randomized scenario.
   ********************************************/

  // Return neighbors of u, using rndState if provided
  proc getNeighbors(u: int, ref rndState: RandomizationState): list(int) {
    var nbrs = new list(int);
    var start = segGraphG1[u];
    var end = segGraphG1[u+1];
    for e in start..<end {
      var offset = e - segGraphG1[u];
      var dst: int;
      if rndState == nil {
        // No randomization
        dst = dstNodesG1[e];
      } else {
        // Use randomized destination
        dst = rndState!.getDstForEdge(u, offset);
      }
      nbrs.pushBack(dst);
    }
    return nbrs;
  }



////////////////////////////////////////////////////////////////////////////////////////////



    /* Generate integer compositions */
    proc generateCompositions(n: int): list(list(int)) {
      var compositions: list(list(int));
      
      if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting generateCompositions ====");
      }

      proc compositionHelper(remaining: int, maxFirst: int, current: list(int)) {
        if remaining == 0 {
          compositions.pushBack(current);
          return;
        }
        
        for i in 1..min(maxFirst, remaining) {
          var next = new list(int);
          for x in current do next.pushBack(x);
          next.pushBack(i);
          compositionHelper(remaining-i, i, next);
        }
      }
      
      compositionHelper(n, n, new list(int));
      
      if logLevel == LogLevel.DEBUG {
        writeln("\nEnd of generateCompositions. Compositions are: ", compositions);
      }

      return compositions;
    }// End of generateCompositions

    /* Get valid neighbors for a vertex */
    proc getValidNeighbors(v: int, state: KavoshState): domain(int) {
      var validNbrs: domain(int);
      
      // Get outgoing neighbors
      var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
      for nbr in outNeighbors {
        if !state.visited[nbr] {
          validNbrs.add(nbr);
        }
      }
      
      // Get incoming neighbors
      var inNeighbors = dstRG1[segRG1[v]..<segRG1[v+1]];
      for nbr in inNeighbors {
        if !state.visited[nbr] {
          validNbrs.add(nbr);
        }
      }
      
      return validNbrs;
    }// End of getValidNeighbors

    /*                                                                             
    * Process a found motif pattern by generating its canonical label 
    * and updating counts.
    */
    proc processFoundMotif(ref state: KavoshState) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("\n==== Starting processFoundMotif ====");
          writeln("Processing pattern of size ", state.patternSize);
          writeln("Current pattern: ", state.pattern[0..<state.patternSize]);  
          writeln("Expected size: ", state.k);          
      }

      if state.patternSize != state.k {
          writeln("Warning: Pattern size mismatch");
          return;
      }

      // Orbit-breaking: Ensure the root is the smallest vertex in the subgraph
      var minVertex = state.pattern[0];
      for i in 1..<state.patternSize {
          if state.pattern[i] < minVertex {
              minVertex = state.pattern[i];
          }
      }
      // If the root is not the smallest vertex, skip counting this pattern
      if state.pattern[0] != minVertex {
          if logLevel == LogLevel.DEBUG {
              writeln("Skipping motif, root is not the smallest vertex in the pattern.");
          }
          return;
      }

      // Check uniqueness: Create a sorted copy of the pattern to ensure uniqueness
      var patternArr = state.pattern[0..<state.patternSize];
      sort(patternArr);
      var patternKey = "";
      for v in patternArr {
        patternKey += v:string + ",";
      }

      // Check if we've already seen this subgraph
      if state.seenPatterns.contains(patternKey) {
          // Already counted this subgraph
          if logLevel == LogLevel.DEBUG {
              writeln("Skipping motif, pattern already seen:", patternKey);
          }
          return;
      } else {
          state.seenPatterns.add(patternKey);
      }

      // Build adjacency matrix only for the pattern size
      var n = state.patternSize;
      var adjMatrix: [0..<n, 0..<n] bool = false;

      // Fill adjacency matrix
      for i in 0..<n {
          var v = state.pattern[i];
          var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
          for nbr in outNeighbors {
              for j in 0..<n {
                  if state.pattern[j] == nbr {
                      adjMatrix[i, j] = true;
                      if logLevel == LogLevel.DEBUG {
                          writeln("adjMatrix[",i,", ",j,"] = ", adjMatrix[i, j]);
                      }
                      break;
                  }
              }
          }
      }

      var labela = generateCanonicalLabel(adjMatrix);
      updateMotifCount(labela, state);
      state.updateMemoryStats();

    }// End of processFoundMotif


    proc updateMotifCount(labela: string, ref state: KavoshState) {
      if !state.motifCounts.contains(labela) {
          var newCount: atomic int;
          newCount.write(1);
          state.motifCounts[labela] = newCount;
      } else {
          state.motifCounts[labela].add(1);
      }
    }// End of updateMotifCount

    /* 
    * Generate canonical label for directed graphs using NAUTY-like approach.
    * Takes adjacency matrix and returns unique string identifier.
    */
    proc generateCanonicalLabel(adjMatrix: [] bool): string throws {
        if logLevel == LogLevel.DEBUG {
            writeln("Generating canonical label for pattern");
        }

        var n = adjMatrix.domain.dim(0).size;
        var maxLabel: string;
        var bestPerm: [0..<n] int;
        var currentPerm: [0..<n] int;
        var visited: [0..<n] bool = false;
        
        // Calculate degrees for vertex ordering
        var inDegrees: [0..<n] int;
        var outDegrees: [0..<n] int;
        for i in 0..<n {
            for j in 0..<n {
                if adjMatrix[j,i] then inDegrees[i] += 1;
                if adjMatrix[i,j] then outDegrees[i] += 1;
            }
        }
        
        // Get degree-based vertex ordering
        var vertexOrder = getVertexOrdering(inDegrees, outDegrees);
        
        proc tryPermutation(depth: int) throws {
            if depth == n {
                // Generate label for current permutation
                var labela: string;
                for i in 0..<n {
                    for j in 0..<n {
                        labela += if adjMatrix[currentPerm[i], currentPerm[j]] then "1" else "0";
                    }
                }
                
                // Update if this is the maximal label
                if maxLabel == "" || labela > maxLabel {
                    maxLabel = labela;
                    bestPerm = currentPerm;
                }
                return;
            }
            
            for i in vertexOrder {
                if !visited[i] {
                    visited[i] = true;
                    currentPerm[depth] = i;
                    tryPermutation(depth + 1);
                    visited[i] = false;
                }
            }
        }
        
        // Find canonical form
        tryPermutation(0);
        
        if logLevel == LogLevel.DEBUG {
            writeln("Generated canonical label: ", maxLabel);
        }
        
        return maxLabel;
    }//End of generateCanonicalLabel


    /* 
    * Generate vertex ordering based on degrees for orbit optimization.
    * Returns array of vertex indices ordered by (inDegree, outDegree).
    */
    proc getVertexOrdering(inDegrees: [] int, outDegrees: [] int): [] int {
        var n = inDegrees.size;
        var order: [0..<n] int;
        var ranks: [0..<n] (int, int, int); // (inDegree, outDegree, vertex)
        
        // Create ranking tuples - higher degrees should come first
        for i in 0..<n {
            // Negative to sort in descending order
            ranks[i] = (-inDegrees[i], -outDegrees[i], i);
        }
        
        // Sort by degrees (will sort by first element, then second, then third)
        sort(ranks);
        
        // Extract vertex order
        for i in 0..<n {
            order[i] = ranks[i][2];
        }

        if logLevel == LogLevel.DEBUG {
            writeln("Vertex ordering: ", order);
        }
        
        return order;
    }// End of getVertexOrdering

    /*
    * Enumerate patterns based on layering defined by compositions.
      * Pass rndState as optional. If rndState != nil, use it for neighbor retrieval.

    */
 proc enumeratePattern(ref state: KavoshState,
                        ref comp: list(int),
                        depth: int,
                        ref rndState: RandomizationState?) throws {

    if state.patternSize == state.k {
      processFoundMotif(state);
      return;
    }

    if depth >= comp.size {
      return;
    }

    const toPick = comp[depth];
    var candidates = getCandidates(state, rndState);

    if candidates.size < toPick {
      return;
    }

    var combos = generateCombinations(candidates, toPick);

    for combo in combos {
      const initialSize = state.patternSize;
      try {
        for u in combo {
          state.addToPattern(u);
          state.visited[u] = true;
        }

        enumeratePattern(state, comp, depth + 1, rndState);

        while state.patternSize > initialSize {
          const last = state.pattern[state.patternSize - 1];
          state.removeFromPattern();
          state.visited[last] = false;
        }
      } catch e {
        while state.patternSize > initialSize {
          const last = state.pattern[state.patternSize - 1];
          state.removeFromPattern();
          state.visited[last] = false;
        }
        writeln("Error in enumeratePattern: ", e.message());
      }
    }
  }
    /* 
    * Implementation of the revolving door ordering algorithm for generating combinations
    * This is called within runMotifCounting() to generate vertex combinations efficiently
    * References paper section: "Here, by using the 'revolving door ordering' algorithm
    * all combinations containing ki vertices from the ni vertices are selected."
    */

    proc generateCombinations(domaina: domain(int, parSafe=true), k: int): list(list(int)) {
      if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting generateCombinations ====");
        writeln("Generating combinations: n=", domaina.size, " k=", k);
      }
      
      var combinations = new list(list(int));
      
      // Safety check
      if k > domaina.size {
          if logLevel == LogLevel.DEBUG {
              writeln("Warning: k(", k, ") larger than available vertices(", domaina.size, ")");
          }
          return combinations;
      }

      // Create array from domain elements
      var elements: [0..<domaina.size] int;
      var idx = 0;
      for x in domaina {
          elements[idx] = x;
          idx += 1;
      }

      if logLevel == LogLevel.DEBUG {
          writeln("  Initial elements: ", elements);
      }

      // Initialize first combination
      var current = new list(int);
      for i in 0..<k {
          current.pushBack(elements[i]);
      }
      combinations.pushBack(current);
      
      if logLevel == LogLevel.DEBUG {
          writeln("  First combination: ", current);
      }

      // Track positions that can move
      var movable = new list(int);
      
      while true {
          movable.clear();
          
          if logLevel == LogLevel.DEBUG {
              writeln("  Current state - Combination: ", current);
          }

          // Find movable elements
          for i in 0..<k {
              var pos = -1;
              for j in 0..<elements.size {
                  if elements[j] == current[i] {
                      pos = j;
                      break;
                  }
              }
              
              // Check if element can move right
              if pos < elements.size - (k - i) {
                  movable.pushBack(i);
                  if logLevel == LogLevel.DEBUG {
                      writeln("    Found movable element at position ", i);
                  }
              }
          }
          
          if movable.size == 0 then break;
          
          // Move rightmost movable element
          var moveIdx = movable[movable.size-1];
          var currentValue = current[moveIdx];
          var currentPos = -1;
          
          // Find current element's position
          for i in 0..<elements.size {
              if elements[i] == currentValue {
                  currentPos = i;
                  break;
              }
          }
          
          if logLevel == LogLevel.DEBUG {
              writeln("  Moving element from position ", moveIdx);
          }

          // Replace with next element
          current[moveIdx] = elements[currentPos + 1];
          
          // Adjust subsequent elements
          for i in moveIdx+1..<k {
              if currentPos + 1 + (i - moveIdx) < elements.size {
                  current[i] = elements[currentPos + 1 + (i - moveIdx)];
              }
          }
          
          // Add new combination
          var nextComb = new list(int);
          for x in current do nextComb.pushBack(x);
          combinations.pushBack(nextComb);
          
          if logLevel == LogLevel.DEBUG {
              writeln("  Added new combination: ", nextComb);
          }
      }
      
      if logLevel == LogLevel.DEBUG {
          writeln("Generated ", combinations.size, " combinations");
          writeln("Final combinations: ", combinations);
      }
      
      return combinations;

    }// End of generateCombinations

/* Get the candidate neighbors from the current pattern
 * Candidates are all unvisited vertices that have an edge (in or out)
 * to any vertex in the currently selected pattern.
 * This ensures that each newly chosen vertex is connected to the
 * subgraph formed so far, maintaining connectivity.
 */

   proc getCandidates(ref state: KavoshState,
                     ref rndState: RandomizationState?): domain(int, parSafe=true) throws{
    var candidates: domain(int, parSafe=true);

    for vIdx in 0..<state.patternSize {
      const v = state.pattern[vIdx];

      // Outgoing neighbors (randomized)
      var start = segGraphG1[v];
      var end = segGraphG1[v+1];
      for e in start..<end {
        var offset = e - segGraphG1[v];
        var nbr = getDstForEdge(rndState, v, offset);
        if !state.visited[nbr] {
          candidates.add(nbr);
        }
      }

      // Incoming neighbors (not randomized)
      start = segRG1[v];
      end = segRG1[v+1];
      for e in start..<end {
        var nbr = dstRG1[e];
        if !state.visited[nbr] {
          candidates.add(nbr);
        }
      }
    }
    return candidates;
  }

  /*
    * Kavosh main function
    * Add an argument for rndState. If rndState is nil, no randomization is used.
    */
proc Kavosh(n: int, k: int, rndState: owned RandomizationState?) throws {

      if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Kavosh ====");
      }

      var state = new KavoshState(n, k);
    var compositions = generateCompositions(k-1);

      // Process each vertex as root
      //forall v in 0..<n with (ref state) {
      for v in 0..<n {
        if logLevel == LogLevel.DEBUG {
            writeln("\nProcessing root vertex: ", v);
        }

        state.visited[v] = true;
        state.addToPattern(v);

        // Process patterns
       for comp in compositions {
            enumeratePattern(state, comp, 0, rndState);
        }

        state.visited[v] = false;
        state.removeFromPattern();
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nAt the end of Kavosh. state is: ", state);
        writeln("Total patterns found: ", state.totalPatterns.read());
        writeln("Max pattern size reached: ", state.maxPatternSize.read());
    }

    writeln("\nK=", k," Motif Summary:");
    writeln("Unique motifs found: ", state.motifCounts.size);
    for key in state.motifCounts.keysToArray(){
        writeln("Motif: ", key, " Count: ", state.motifCounts[key].read());
    }

    }// end of Kavosh
/////////////////////////////////////////////Randomized part////////////////////////


///////////////////////////////////////////////////////////////////////////////////




    var tempArr: [0..0] int;
    var srcPerIso = makeDistArray(2*2, int);
    var dstPerIso = makeDistArray(2*2, int);
    return (srcPerIso, dstPerIso, tempArr, tempArr);
  }// End of runMotifCounting
}