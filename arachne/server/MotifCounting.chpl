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


  /* State tracking class - declared at module level since it's referenced in multiple procs */
  /* In KavoshState class */
  class KavoshState {
      var n: int;              
      var k: int;              
      var visited: [0..<n] bool;
      var pattern: list(int);   
      var motifCounts: map(string, atomic int);  // Map of motif label to atomic counter
      
      proc init(n: int, k: int) {
          this.n = n;
          this.k = k;
          this.visited = false;
          this.pattern = new list(int);
          this.motifCounts = new map(string, atomic int);
      }
      
      proc reset() {
          this.visited = false;
          this.pattern.clear();
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



/* 
 * Implementation of the revolving door ordering algorithm for generating combinations
 * This is called within runMotifCounting() to generate vertex combinations efficiently
 * References paper section: "Here, by using the 'revolving door ordering' algorithm
 * all combinations containing ki vertices from the ni vertices are selected."
 */
proc generateCombinations(domaina: domain(int), k: int): list(list(int)) {
    if logLevel == LogLevel.DEBUG {
        writeln("Generating combinations: n=", domaina.size, " k=", k);
    }
    
    var combinations = new list(list(int));
    var elements: [1..domaina.size] int;
    var idx = 1;
    
    // Convert domain to array for indexing
    for x in domaina {
        elements[idx] = x;
        idx += 1;
    }
    
    // Initialize first combination
    var current = new list(int);
    for i in 1..k {
        current.pushBack(elements[i]);
    }
    combinations.pushBack(current);
    
    // Track positions that can move
    var movable = new list(int);
    
    while true {
        movable.clear();
        
        // Find movable elements (elements that can shift right)
        for i in 1..k {
            var pos = -1;
            // Find position of current element
            for j in 1..elements.size {
                if elements[j] == current[i-1] {
                    pos = j;
                    break;
                }
            }
            
            // Check if element can move right
            if pos < elements.size - (k - i) {
                movable.pushBack(i-1);
            }
        }
        
        if movable.size == 0 then break;
        
        // Move rightmost movable element
        var moveIdx = movable[movable.size-1];
        var currentValue = current[moveIdx];
        var currentPos = -1;
        
        // Find position in elements array
        for i in 1..elements.size {
            if elements[i] == currentValue {
                currentPos = i;
                break;
            }
        }
        
        // Replace with next element
        current[moveIdx] = elements[currentPos + 1];
        
        // Adjust subsequent elements if needed
        for i in moveIdx+1..k-1 {
            current[i] = elements[currentPos + 1 + (i - moveIdx)];
        }
        
        // Add new combination
        var nextComb = new list(int);
        for x in current do nextComb.pushBack(x);
        combinations.pushBack(nextComb);
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Generated ", combinations.size, " combinations");
    }
    
    return combinations;
}

   /* Local procedure for getting valid neighbors */
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
    }

    /* Local procedure to generate integer compositions */
    proc generateCompositions(n: int): list(list(int)) {
      var compositions: list(list(int));
      
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
      return compositions;
    }

    /* Local procedure to process motif patterns */
    proc processPattern(state: KavoshState) {
      if state.pattern.size < 2 then return;
      
      // Build adjacency matrix for the pattern
      var n = state.pattern.size;
      var adjMatrix: [0..<n, 0..<n] bool;
      
      // Add edges
      for (i, v) in zip(0..<n, state.pattern) {
        var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
        for u in outNeighbors {
          var idx = state.pattern.find(u);
          if idx != -1 {
            adjMatrix[i, idx] = true;
          }
        }
      }
      
      // Get canonical label and update counts
      var labela = generateCanonicalLabel(adjMatrix);
      state.motifCounts[labela].add(1);
    }

    /* Local procedure for composition-based enumeration */
    proc processComposition(v: int, composition: list(int), depth: int, state: KavoshState) {
      if depth == composition.size {
        processPattern(state);
        return;
      }
      
      var validNbrs = getValidNeighbors(v, state);
      var need = composition[depth];
      
      if validNbrs.size >= need {
        var combos = generateCombinations(validNbrs, need);
        
        for combo in combos {
          // Add vertices
          for u in combo {
            state.pattern.pushBack(u);
            state.visited[u] = true;
          }
          
          // Recurse
          for u in combo {
            processComposition(u, composition, depth+1, state);
          }
          
          // Remove vertices
          for u in combo {
            state.pattern.removeLast();
            state.visited[u] = false;
          }
        }
      }
    }
/* Core enumeration procedure for processing vertices by composition pattern */
proc enumeratePattern(v: int, pattern: list(int), currentDepth: int, state: KavoshState) {
    if logLevel == LogLevel.DEBUG {
        writeln("Processing vertex ", v, " at depth ", currentDepth);
    }

    if currentDepth == pattern.size {
        // Found complete pattern - process it
        processSubgraph(state);
        return;
    }

    // Get neighbors using segment-based access for directed graph
    var inNeighbors = dstRG1[segRG1[v]..<segRG1[v+1]];
    var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

    // Build valid neighbor set respecting direction
    var validNeighbors: domain(int);
    
    // Check outgoing neighbors
    for nbr in outNeighbors {
        if !state.visited[nbr] {
            validNeighbors.add(nbr);
        }
    }

    // Check incoming neighbors 
    for nbr in inNeighbors {
        if !state.visited[nbr] {
            validNeighbors.add(nbr);
        }
    }

    // Get required number of vertices for this level
    var k = pattern[currentDepth];

    // Only proceed if we have enough valid neighbors
    if validNeighbors.size >= k {
        // Generate combinations using revolving door ordering
        var combinations = generateCombinations(validNeighbors, k);

        // Process each combination
        for combo in combinations {
            // Track which vertices we're adding for backtracking
            var addedVertices: list(int);

            // Add all vertices in combination to pattern
            for u in combo {
                state.pattern.append(u);
                state.visited[u] = true;
                addedVertices.append(u);
            }

            // Recursively process from each vertex in combination
            for u in combo {
                enumeratePattern(u, pattern, currentDepth + 1, state);
            }

            // Backtrack - remove vertices added from this combination
            for u in addedVertices {
                state.pattern.removeLast();
                state.visited[u] = false;
            }
        }
    }
}
proc updateMotifCount(labela: string, ref state: KavoshState) {
    if !state.motifCounts.contains(labela) {
        var newCount: atomic int;
        newCount.write(1);
        state.motifCounts[labela] = newCount;
    } else {
        state.motifCounts[labela].add(1);
    }
}
/* Process found subgraph patterns */
proc processSubgraph(state: KavoshState) {
    if logLevel == LogLevel.DEBUG {
        writeln("Processing found subgraph with vertices: ", state.pattern);
    }

    // Build adjacency matrix for the pattern
    var n = state.pattern.size;
    var adjMatrix: [0..<n, 0..<n] bool = false;

    // Add edges preserving direction
    for (i, v) in zip(0..<n, state.pattern) {
        // Get outgoing edges
        var outStart = segGraphG1[v];
        var outEnd = segGraphG1[v+1];
        
        for j in outStart..<outEnd {
            var u = dstNodesG1[j];
            var idx = state.pattern.find(u);
            if idx != -1 {
                adjMatrix[i,idx] = true;
            }
        }
    }

    // Get canonical labeling
    var labela = generateCanonicalLabel(adjMatrix);

    // Update count atomically
    updateMotifCount(labela, state);
}
/* 
 * Enumerate vertices according to composition pattern.
 * Called by Kavosh() for each composition to build motifs.
 */
proc enumeratePattern(v: int, pattern: list(int), depth: int, state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Enumerating at depth ", depth, " from vertex ", v);
    }

    // Base case: found complete pattern
    if depth == pattern.size {
        processFoundMotif(state);
        return;
    }

    // Get neighbors of current vertex
    var inNeighbors = dstRG1[segRG1[v]..<segRG1[v+1]];      
    var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

    // Build valid neighbor set
    var validNbrs: domain(int);
    
    // Add unvisited outgoing neighbors
    for nbr in outNeighbors {
        if !state.visited[nbr] {
            validNbrs.add(nbr);
        }
    }

    // Add unvisited incoming neighbors
    for nbr in inNeighbors {
        if !state.visited[nbr] {
            validNbrs.add(nbr);
        }
    }

    var needed = pattern[depth];
    if validNbrs.size >= needed {
        // Generate combinations using revolving door
        var combinations = generateCombinations(validNbrs, needed);
        
        // Process each combination
        for combo in combinations {
            // Mark vertices in combination
            for u in combo {
                state.pattern.pushBack(u);
                state.visited[u] = true;
            }
            
            // Recurse on each vertex in combination
            for u in combo {
                enumeratePattern(u, pattern, depth+1, state);
            }
            
            // Unmark vertices (backtrack)
            for u in combo {
                state.pattern.removeLast();  
                state.visited[u] = false;
            }
        }
    }
}
/* 
 * Process a found motif pattern by generating its canonical label 
 * and updating counts.
 */
proc processFoundMotif(state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Found motif pattern: ", state.pattern);
    }

    // Build adjacency matrix for the pattern
    var n = state.pattern.size;
    var adjMatrix: [0..<n, 0..<n] bool = false;

    // Add edges preserving direction
    for (i, v) in zip(0..<n, state.pattern) {
        // Get outgoing edges
        var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
        for nbr in outNeighbors {
            var idx = state.pattern.find(nbr);
            if idx != -1 {
                adjMatrix[i, idx] = true;
            }
        }
    }

    // Get canonical label (will implement next)
    var labela = generateCanonicalLabel(adjMatrix);
    
    // Update counts atomically
    // Update count atomically
    updateMotifCount(labela, state);
}
/* 
 * Generate canonical label for directed subgraph using NAUTY-like approach.
 * Based on: "Classification is another major subtasks of motif finding algorithms.
 * In Kavosh, NAUTY algorithm which is the best known tool for this subtask is used."
 */
proc generateCanonicalLabel(adjMatrix: [] bool): string throws {
    var n = adjMatrix.domain.dim(0).size;
    
    // Track vertex permutations
    var maxLabel: string;
    var permutation: [0..<n] int;
    var used: [0..<n] bool;
    
    // Helper to try a permutation
    proc tryPermutation(depth: int) throws {
        if depth == n {
            // Generate label for this permutation
            var labela: string;
            for i in 0..<n {
                for j in 0..<n {
                    // Preserve edge direction in label
                    labela += if adjMatrix[permutation[i], permutation[j]] then "1" else "0";
                }
            }
            
            // Update max label if this is larger
            if maxLabel == "" || labela > maxLabel {
                maxLabel = labela;
            }
            return;
        }
        
        // Generate degrees for unused vertices
        var degrees: [0..<n] (int, int, int); // (inDegree, outDegree, vertex)
        var idx = 0;
        
        for v in 0..<n {
            if !used[v] {
                var inDeg = 0;
                var outDeg = 0;
                
                // Count edges involving vertex v
                for i in 0..<n {
                    if adjMatrix[i,v] then inDeg += 1;
                    if adjMatrix[v,i] then outDeg += 1;
                }
                
                degrees[idx] = (inDeg, outDeg, v);
                idx += 1;
            }
        }
        
        // Sort vertices by (inDegree, outDegree) for canonical ordering
        QuickSort(degrees[0..<idx]);
        
        // Try each unused vertex in sorted order
        for i in 0..<idx {
            var v = degrees[i][2];
            if !used[v] {
                permutation[depth] = v;
                used[v] = true;
                tryPermutation(depth + 1);
                used[v] = false;
            }
        }
    }
    
    // Sort vertices by degree first
    proc QuickSort(arr: [] (int, int, int)) {
        proc partition(arr: [] (int, int, int), low: int, high: int) {
            var pivot = arr[high];
            var i = low - 1;
            
            for j in low..high-1 {
                // Compare tuples lexicographically
                if (arr[j][0] > pivot[0]) || 
                   (arr[j][0] == pivot[0] && arr[j][1] > pivot[1]) {
                    i += 1;
                    var temp = arr[i];
                    arr[i] = arr[j];
                    arr[j] = temp;
                }
            }
            
            var temp = arr[i+1];
            arr[i+1] = arr[high];
            arr[high] = temp;
            return i + 1;
        }
        
        proc quickSortHelper(arr: [] (int, int, int), low: int, high: int) {
            if low < high {
                var pi = partition(arr, low, high);
                quickSortHelper(arr, low, pi-1);
                quickSortHelper(arr, pi+1, high);
            }
        }
        
        quickSortHelper(arr, arr.domain.low, arr.domain.high);
    }
    
    // Initialize state
    for i in 0..<n {
        permutation[i] = i;
        used[i] = false;
    }
    
    // Try all permutations
    tryPermutation(0);
    
    return maxLabel;
}
/* Main execution procedure using these functions */
proc Kavosh(n: int, k: int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Kavosh ====");
    }

    var state = new KavoshState(n, k);
    var timer = new stopwatch();
    timer.start();
    
    // Process each vertex as root
    forall v in 0..<n with (ref state) {
        // Stop if time limit exceeded
        if limitTime && timer.elapsed():int >= timeLimit {
            stopper.testAndSet();
            continue;
        }
        
        // Stop if size limit reached
        if limitSize && state.motifCounts.size >= matchLimit {
            stopper.testAndSet();
            continue; 
        }

        if logLevel == LogLevel.DEBUG && v % 1000 == 0 {
            writeln("Processing root vertex ", v);
        }

        state.reset();
        state.visited[v] = true;
        state.pattern.pushBack(v);

        // Generate compositions for (k-1) remaining vertices
        var compositions = generateCompositions(k-1);
        
        // Process each composition pattern
        for comp in compositions {
            if stopper.read() then break;
            enumeratePattern(v, comp, 0, state);
        }

        state.visited[v] = false;
        state.pattern.removeLast();
    }

    timer.stop();
    
    if logLevel == LogLevel.DEBUG {
        writeln("Kavosh completed in ", timer.elapsed(), " seconds");
        writeln("Found ", state.motifCounts.size, " distinct motifs");
    }

    return state; // Return results for significance calculation
}
/* Wrapper function to prepare and execute Kavosh */
proc runKavosh() {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Kavosh wrapper ====");
    }
    // Initialize state tracking
    var n = g1.n_vertices;
    var k = g2.n_vertices; // Use subgraph size as motif size

    
    // Call the main algorithm
    Kavosh(n, k);
    

}

    // Execute Kavosh algorithm
    runKavosh(); // Using subgraph size as motif size
  }
}