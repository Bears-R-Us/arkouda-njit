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


  /* State tracking class - declared at module level since it's referenced in multiple procs */
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

  // Run integrated motif finding
    var motifResults = findMotifs();

    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Motif Finding Complete ====");
    }


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
            state.pattern.popBack();
            state.visited[u] = false;
          }
        }
      }
    }

/* 
 * Enumerate vertices according to composition pattern.
 * Called by Kavosh() for each composition to build motifs.
 */
proc enumeratePattern(v: int, pattern: list(int), depth: int, state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Enumerating pattern at depth ", depth, " from vertex ", v);
    }

    // Base case: found complete pattern
    if depth == pattern.size {
        processFoundMotif(state);
        return;
    }

    // Get neighbors using segment-based access for directed graph
    var inNeighbors = dstRG1[segRG1[v]..<segRG1[v+1]];      
    var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

    if logLevel == LogLevel.DEBUG {
        writeln("  Found ", inNeighbors.size, " in-neighbors and ", outNeighbors.size, " out-neighbors");
    }

    // Build valid neighbor set respecting graph direction and validation
    var validNbrs: domain(int);
    
    // Process outgoing neighbors
    for nbr in outNeighbors {
        if !state.visited[nbr] {
            // Validate vertex for next level
            if validateVertex(nbr, depth, state) {
                validNbrs.add(nbr);
                if logLevel == LogLevel.DEBUG {
                    writeln("  Added valid out-neighbor: ", nbr);
                }
            }
        }
    }

    // Process incoming neighbors 
    for nbr in inNeighbors {
        if !state.visited[nbr] {
            // Validate vertex for next level
            if validateVertex(nbr, depth, state) {
                validNbrs.add(nbr);
                if logLevel == LogLevel.DEBUG {
                    writeln("  Added valid in-neighbor: ", nbr);
                }
            }
        }
    }

    // Get required number of vertices for this level
    var k = pattern[depth];
    
    if logLevel == LogLevel.DEBUG {
        writeln("  Need ", k, " vertices at depth ", depth);
        writeln("  Have ", validNbrs.size, " valid neighbors to choose from");
    }

    // Only proceed if we have enough valid neighbors
    if validNbrs.size >= k {
        // Generate combinations using revolving door ordering
        var combinations = generateCombinations(validNbrs, k);

        if logLevel == LogLevel.DEBUG {
            writeln("  Generated ", combinations.size, " combinations");
        }

        // Process each combination
        for combo in combinations {
            // Track vertices for backtracking
            var addedVertices: list(int);

            // Add vertices in combination
            for u in combo {
                state.pattern.pushBack(u);
                state.visited[u] = true;
                addedVertices.pushBack(u);
                
                if logLevel == LogLevel.DEBUG {
                    writeln("    Added vertex ", u, " to pattern");
                }
            }

            // Recurse on each vertex in combination
            for u in combo {
                enumeratePattern(u, pattern, depth + 1, state);
                if stopper.read() then break;  // Check for early termination
            }

            // Backtrack - remove added vertices
            for u in addedVertices {
                state.pattern.popBack();
                state.visited[u] = false;
            }

            if logLevel == LogLevel.DEBUG {
                writeln("    Backtracked combination at depth ", depth);
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
 * Process a found motif pattern by generating its canonical label 
 * and updating counts.
 */
proc processFoundMotif(ref state: KavoshState) throws {
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
    
    // Update count atomically
    updateMotifCount(labela, state);
}

/* 
 * NAUTY-like canonical labeling for directed graphs.
 * Takes adjacency matrix and generates unique identifier.
 */
proc generateCanonicalLabel(adjMatrix: [] bool): string throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Generating canonical label for pattern");
    }

    var n = adjMatrix.domain.dim(0).size;
    
    // Track best labeling found
    var maxLabel: string = "";
    var bestPerm: [0..<n] int;
    var currentPerm: [0..<n] int;
    var visited: [0..<n] bool = false;
    
    // For orbit optimization
    var inDegrees: [0..<n] int;
    var outDegrees: [0..<n] int;
    
    // Calculate degrees for orbit partitioning
    for i in 0..<n {
        var inDeg = 0;
        var outDeg = 0;
        for j in 0..<n {
            if adjMatrix[j,i] then inDeg += 1;
            if adjMatrix[i,j] then outDeg += 1;
        }
        inDegrees[i] = inDeg;
        outDegrees[i] = outDeg;
    }
    
    // Get initial vertex ordering based on degrees
    var vertexOrder = getVertexOrdering(inDegrees, outDegrees);
    
    // Try permutations following vertex ordering
    proc tryPermutations(depth: int) throws {
        if depth == n {
            var labela = generateLabel(currentPerm, adjMatrix);
            if maxLabel == "" || labela > maxLabel {
                maxLabel = labela;
                bestPerm = currentPerm;
            }
            return;
        }
        
        // Try vertices in degree-based order
        for i in vertexOrder {
            if !visited[i] {
                visited[i] = true;
                currentPerm[depth] = i;
                tryPermutations(depth + 1);
                visited[i] = false;
            }
        }
    }
    
    // Generate canonical form
    tryPermutations(0);
    return maxLabel;
}
/* Generate random networks preserving degree sequence */
proc generateRandomNetworks(numNetworks: int) {
    if logLevel == LogLevel.DEBUG {
        writeln("Generating ", numNetworks, " random networks");
    }

    // Store original graph edges
    var edges: list((int,int));
    for v in 0..<g1.n_vertices {
        var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
        for u in outNeighbors {
            edges.pushBack((v,u));
        }
    }

    // Generate each random network
    for i in 1..numNetworks {
        if logLevel == LogLevel.DEBUG {
            writeln("Generating random network ", i);
        }

        // Create copy of edges to shuffle
        var randomEdges = edges;
        
        // Perform edge switches to randomize
        var numSwitches = 100 * edges.size; // As specified in paper
        for j in 1..numSwitches {
            // Select two random edges
            var idx1 = rand.getNext(0, edges.size-1);
            var idx2 = rand.getNext(0, edges.size-1);
            
            var edge1 = randomEdges[idx1];
            var edge2 = randomEdges[idx2];

            // Try to switch while preserving degrees
            if edge1[1] != edge2[1] && edge1[0] != edge2[0] {
                // Check if new edges already exist
                if !edgeExists(edge1[0], edge2[1]) && 
                   !edgeExists(edge2[0], edge1[1]) {
                    // Perform switch
                    randomEdges[idx1] = (edge1[0], edge2[1]);
                    randomEdges[idx2] = (edge2[0], edge1[1]);
                }
            }
        }

        // Build random graph and find its motifs
        var randomGraph = buildGraphFromEdges(randomEdges);
        var randomMotifs = runKavosh(/* params for random graph */);
        
        // Store motif counts for significance calculation
        updateRandomMotifCounts(randomMotifs);
    }
}
/* Calculate motif significance metrics */
proc calculateMotifSignificance(originalMotifs: map(string, atomic int), 
                              randomMotifs: [?d] map(string, atomic int)) {
    if logLevel == LogLevel.DEBUG {
        writeln("Calculating motif significance metrics");
    }

    // Store significance results
    var zScores: map(string, real);
    var pValues: map(string, real);
    var frequencies: map(string, int);

    // Calculate for each motif pattern found in original graph
    for (pattern, count) in originalMotifs {
        var origCount = count.read();
        frequencies[pattern] = origCount;

        // Calculate mean and std dev from random networks
        var randomCounts: [0..#randomMotifs.size] real;
        for i in 0..#randomMotifs.size {
            if randomMotifs[i].contains(pattern) {
                randomCounts[i] = randomMotifs[i][pattern].read():real;
            }
        }

        var meanRandom = calculateMean(randomCounts);
        var stdRandom = calculateStdDev(randomCounts, meanRandom);

        // Calculate Z-score: (Nreal - <Nrand>)/std(Nrand)
        var zscore = 0.0;
        if stdRandom != 0.0 {
            zscore = (origCount - meanRandom) / stdRandom;
        }
        zScores[pattern] = zscore;

        // Calculate P-value: number of random networks where motif appears more often
        var moreFrequent = 0;
        for counts in randomCounts {
            if counts >= origCount then moreFrequent += 1;
        }
        pValues[pattern] = moreFrequent:real / randomMotifs.size:real;
    }

    return (frequencies, zScores, pValues);
}

/* Calculate mean of array */
proc calculateMean(arr: [] real): real {
    var sum = 0.0;
    for x in arr do sum += x;
    return sum / arr.size:real;
}

/* Calculate standard deviation */
proc calculateStdDev(arr: [] real, mean: real): real {
    var sumSquares = 0.0;
    for x in arr {
        var diff = x - mean;
        sumSquares += diff * diff;
    }
    return sqrt(sumSquares / (arr.size:real - 1));
}

/* Determine if subgraph is a motif based on significance thresholds */
proc isMotif(pattern: string, freq: int, zscore: real, pvalue: real): bool {
    // Following paper's criteria:
    // 1. Frequency must be above minimum threshold
    const minFreq = 4; // As specified in paper
    
    // 2. P-value must be below significance threshold
    const pValueThreshold = 0.01; // As specified in paper
    
    // 3. Z-score must be above minimum threshold
    const minZScore = 1.0; // As specified in paper

    return freq >= minFreq && 
           pvalue < pValueThreshold && 
           zscore > minZScore;
}

/* Print motif analysis results */
proc printMotifResults(frequencies: map(string, int),
                      zScores: map(string, real),
                      pValues: map(string, real)) {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Motif Analysis Results ====");
        for pattern in frequencies.keys() {
            var freq = frequencies[pattern];
            var zscore = zScores[pattern];
            var pvalue = pValues[pattern];
            
            if isMotif(pattern, freq, zscore, pvalue) {
                writeln("Found motif pattern: ", pattern);
                writeln("  Frequency: ", freq);
                writeln("  Z-score: ", zscore);
                writeln("  P-value: ", pvalue);
                writeln();
            }
        }
    }
}
/* Generate random graphs while preserving degree sequence */
proc generateRandomGraphs(numGraphs: int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Generating ", numGraphs, " random graphs ====");
    }

    // Initialize degree tracking
    var degrees: [0..<g1.n_vertices] (int,int); // (inDegree, outDegree)
    
    // Calculate initial degrees
    for v in 0..<g1.n_vertices {
        var inDeg = segRG1[v+1] - segRG1[v];
        var outDeg = segGraphG1[v+1] - segGraphG1[v];
        degrees[v] = (inDeg, outDeg);
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Initial degree sequence calculated");
    }

    // Store original edges
    var edges: list((int,int));
    for v in 0..<g1.n_vertices {
        var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
        for u in outNeighbors {
            edges.pushBack((v,u));
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Original graph has ", edges.size, " edges");
    }

    // Initialize array for random graph results
    var randomResults: [0..#numGraphs] map(string, atomic int);

    // Generate each random network
    forall i in 0..#numGraphs {
        if logLevel == LogLevel.DEBUG {
            writeln("\nGenerating random graph ", i+1);
        }

        // Create copy of edges to shuffle
        var randomEdges = new list((int,int));
        for e in edges do randomEdges.pushBack(e);

        // Track current degrees for this random graph
        var currentDegrees = degrees;

        // Number of edge switches (100|E| as per paper)
        var numSwitches = 100 * edges.size;
        
        if logLevel == LogLevel.DEBUG {
            writeln("  Performing ", numSwitches, " edge switches");
        }

        // Perform edge switches
        for j in 1..numSwitches {
            // Select two random edges
            var idx1 = rand.getNext(0, randomEdges.size-1);
            var idx2 = rand.getNext(0, randomEdges.size-1);
            
            var edge1 = randomEdges[idx1];
            var edge2 = randomEdges[idx2];

            // Validate edge switch
            if validateEdgeSwitch(edge1, edge2, currentDegrees) {
                // Perform switch: (s1,d1), (s2,d2) -> (s1,d2), (s2,d1)
                randomEdges[idx1] = (edge1(0), edge2(1));
                randomEdges[idx2] = (edge2(0), edge1(1));
                
                if logLevel == LogLevel.DEBUG && j % (numSwitches/10) == 0 {
                    writeln("    Completed ", (j*100)/numSwitches, "% of switches");
                }

                // Update degree tracking
                // Decrement old degrees
                currentDegrees[edge1(0)] = (currentDegrees[edge1(0)][0], 
                                          currentDegrees[edge1(0)][1] - 1);
                currentDegrees[edge2(0)] = (currentDegrees[edge2(0)][0], 
                                          currentDegrees[edge2(0)][1] - 1);
                currentDegrees[edge1(1)] = (currentDegrees[edge1(1)][0] - 1, 
                                          currentDegrees[edge1(1)][1]);
                currentDegrees[edge2(1)] = (currentDegrees[edge2(1)][0] - 1, 
                                          currentDegrees[edge2(1)][1]);

                // Increment new degrees
                currentDegrees[edge1(0)] = (currentDegrees[edge1(0)][0], 
                                          currentDegrees[edge1(0)][1] + 1);
                currentDegrees[edge2(0)] = (currentDegrees[edge2(0)][0], 
                                          currentDegrees[edge2(0)][1] + 1);
                currentDegrees[edge2(1)] = (currentDegrees[edge2(1)][0] + 1, 
                                          currentDegrees[edge2(1)][1]);
                currentDegrees[edge1(1)] = (currentDegrees[edge1(1)][0] + 1, 
                                          currentDegrees[edge1(1)][1]);
            }
        }

        // Convert edge list to graph format and analyze
        var (randomSrc, randomDst, randomSeg) = buildRandomGraph(randomEdges);
        var randomState = new KavoshState(g1.n_vertices, g2.n_vertices);
        runKavoshOnRandom(randomState, randomSrc, randomDst, randomSeg);
        
        // Store results
        randomResults[i] = randomState.motifCounts;

        if logLevel == LogLevel.DEBUG {
            writeln("  Completed random graph ", i+1);
            writeln("  Found ", randomState.motifCounts.size, " patterns");
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nRandom graph generation complete");
    }

    return randomResults;
}

/* Check if an edge switch is valid */
proc isValidSwitch(src1: int, dst1: int, src2: int, dst2: int, 
                         edges: list((int,int))): bool {
    // Cannot switch if vertices are same
    if src1 == src2 || dst1 == dst2 || src1 == dst2 || src2 == dst1 then
        return false;

    // Check if new edges would create self-loops
    if src1 == dst2 || src2 == dst1 then
        return false;

    // Check if new edges already exist
    var newEdge1 = (src1, dst2);
    var newEdge2 = (src2, dst1);

    for e in edges {
        if e == newEdge1 || e == newEdge2 then
            return false;
    }

    return true;
}

/* Build random graph from edge list for comparison */
proc buildRandomGraph(edges: list((int,int))) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Building random graph from ", edges.size, " edges");
    }
    
    var n = g1.n_vertices;  // Use same number of vertices as original
    var m = edges.size;
    
    // Create arrays for graph representation
    var srcNodes: [0..#m] int;
    var dstNodes: [0..#m] int;
    var segments: [0..#(n+1)] int;
    
    // Initialize segments
    segments.fill(0);
    
    // Count outgoing edges per vertex
    for (src, _) in edges {
        segments[src+1] += 1;
    }
    
    // Compute segment offsets
    for i in 1..n {
        segments[i] += segments[i-1];
    }
    
    // Fill src/dst arrays maintaining edge order
    var counts: [0..#n] int;
    for (src, dst) in edges {
        var idx = segments[src] + counts[src];
        srcNodes[idx] = src;
        dstNodes[idx] = dst;
        counts[src] += 1;
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Built random graph with ", n, " vertices and ", m, " edges");
    }
    
    return (srcNodes, dstNodes, segments);
}

/* Run Kavosh on random graph */
proc runKavoshOnRandom(state: KavoshState, 
                             srcNodes: [] int,
                             dstNodes: [] int,
                             segments: [] int) {
    // Similar to main Kavosh but using provided arrays
    forall v in 0..<state.n {
        state.reset();
        state.visited[v] = true;
        state.pattern.pushBack(v);

        var compositions = generateCompositions(state.k-1);
        for comp in compositions {
            enumeratePatternRandom(v, comp, 0, state, srcNodes, dstNodes, segments);
        }

        state.visited[v] = false;
        state.pattern.popBack();
    }
}

/* Pattern enumeration for random graphs */
proc enumeratePatternRandom(v: int, pattern: list(int), depth: int,
                          ref state: KavoshState,
                          const ref srcNodes: [] int,
                          const ref dstNodes: [] int,
                          const ref segments: [] int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Random enumeration at depth ", depth, " from vertex ", v);
    }

    // Base case: found complete pattern
    if depth == pattern.size {
        processFoundMotif(state);
        return;
    }

    // Get neighbors from random graph structure
    var validNbrs: domain(int);
    
    // Get outgoing neighbors
    var outStart = segments[v];
    var outEnd = if v < segments.domain.high then segments[v+1] else dstNodes.size;
    
    // Add valid unvisited neighbors
    for i in outStart..<outEnd {
        var nbr = dstNodes[i];
        if !state.visited[nbr] {
            validNbrs.add(nbr);
            if logLevel == LogLevel.DEBUG {
                writeln("  Added valid neighbor: ", nbr);
            }
        }
    }

    // Required vertices for this level
    var k = pattern[depth];
    
    if logLevel == LogLevel.DEBUG {
        writeln("  Need ", k, " vertices at depth ", depth);
        writeln("  Have ", validNbrs.size, " valid neighbors");
    }

    // Process if enough valid neighbors exist
    if validNbrs.size >= k {
        var combinations = generateCombinations(validNbrs, k);
        
        for combo in combinations {
            // Track added vertices for backtracking
            var addedVertices: list(int);

            // Add vertices
            for u in combo {
                state.pattern.pushBack(u);
                state.visited[u] = true;
                addedVertices.pushBack(u);
                
                if logLevel == LogLevel.DEBUG {
                    writeln("    Added vertex ", u);
                }
            }
            
            // Recurse on each vertex
            for u in combo {
                enumeratePatternRandom(u, pattern, depth+1,
                                     state, srcNodes, dstNodes, segments);
            }
            
            // Backtrack
            for u in addedVertices {
                state.pattern.popBack();
                state.visited[u] = false;
            }

            if logLevel == LogLevel.DEBUG {
                writeln("    Backtracked at depth ", depth);
            }
        }
    }
}

/* Main result structure to hold motif analysis data */
class MotifAnalysisResults {
    var frequencies: map(string, int);        // Original graph frequencies
    var zScores: map(string, real);          // Z-scores for each motif
    var pValues: map(string, real);          // P-values for each motif
    var significantMotifs: list(string);     // Patterns that are motifs
    
    proc init() {
        this.frequencies = new map(string, int);
        this.zScores = new map(string, real);
        this.pValues = new map(string, real);
        this.significantMotifs = new list(string);
    }
}

/* Main execution procedure - integrates all components */
proc findMotifs() throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Motif Finding ====");
    }
    
    var timer = new stopwatch();
    timer.start();

    // 1. Run Kavosh on original graph
    if logLevel == LogLevel.DEBUG {
        writeln("Analyzing original graph...");
    }
    runKavosh();
    var originalMotifs = state.motifCounts;

    // 2. Generate random graphs and analyze them
    if logLevel == LogLevel.DEBUG {
        writeln("Generating and analyzing random graphs...");
    }
    const numRandomGraphs = 1000; // As specified in paper
    var randomResults = generateRandomGraphs(numRandomGraphs);

    // 3. Calculate significance
    if logLevel == LogLevel.DEBUG {
        writeln("Calculating motif significance...");
    }
    var (frequencies, zScores, pValues) = 
        calculateMotifSignificance(originalMotifs, randomResults);

    // 4. Identify significant motifs
    var results = new MotifAnalysisResults();
    results.frequencies = frequencies;
    results.zScores = zScores;
    results.pValues = pValues;

    // Store significant motifs based on criteria
    for pattern in frequencies.keys() {
        var freq = frequencies[pattern];
        var zscore = zScores[pattern];
        var pvalue = pValues[pattern];
        
        if isMotif(pattern, freq, zscore, pvalue) {
            results.significantMotifs.pushBack(pattern);
        }
    }

    timer.stop();

    // 5. Report results
    reportResults(results, timer.elapsed());

    return results;
}

/* Comprehensive result reporting */
proc reportResults(results: MotifAnalysisResults, time: real) {
    if logLevel == LogLevel.DEBUG {
        writeln("\n======= Motif Analysis Results =======");
        writeln("Total execution time: ", time, " seconds");
        writeln("Found ", results.significantMotifs.size, " significant motifs");
        writeln("\nSignificant Motifs Details:");
        
        for pattern in results.significantMotifs {
            writeln("\nMotif Pattern: ", pattern);
            writeln("  Frequency: ", results.frequencies[pattern]);
            writeln("  Z-score: ", results.zScores[pattern]);
            writeln("  P-value: ", results.pValues[pattern]);
            
            // Convert pattern to adjacency matrix for visualization
            var n = sqrt(pattern.length): int;  // Pattern is flattened matrix
            writeln("\n  Adjacency Matrix:");
            for i in 0..<n {
                write("  ");
                for j in 0..<n {
                    write(pattern[i*n + j], " ");
                }
                writeln();
            }
        }
        writeln("\n=====================================");
    }
}
/* 
 * Generate vertex ordering based on degrees for orbit optimization.
 * Returns array of vertex indices ordered by (inDegree, outDegree).
 */
proc getVertexOrdering(inDegrees: [] int, outDegrees: [] int): [] int {
    var n = inDegrees.size;
    var order: [0..<n] int;
    var ranks: [0..<n] (int, int, int); // (inDegree, outDegree, vertex)
    
    // Create ranking tuples
    for i in 0..<n {
        ranks[i] = (inDegrees[i], outDegrees[i], i);
    }
    
    // Sort by degrees
    sort(ranks);
    
    // Extract vertex order
    for i in 0..<n {
        order[i] = ranks[i][2];
    }
    
    return order;
}

/* 
 * Generate string label from permutation and adjacency matrix.
 * Format ensures unique representation for isomorphic graphs.
 */
proc generateLabel(perm: [] int, adjMatrix: [] bool): string {
    var n = perm.size;
    var labela: string;
    
    // Build label string following permutation
    for i in 0..<n {
        for j in 0..<n {
            labela += if adjMatrix[perm[i], perm[j]] then "1" else "0";
        }
    }
    
    return labela;
}

/* 
 * Validate vertex for next level processing.
 * Ensures proper vertex selection based on graph structure.
 */
proc validateVertex(v: int, level: int, const ref state: KavoshState): bool {
    // Get current vertex neighbors
    var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
    var inNeighbors = dstRG1[segRG1[v]..<segRG1[v+1]];
    
    // Check connectivity constraints
    var hasUpperConnection = false;
    var hasLowerConnection = false;
    
    // Check connections to previous level
    for u in inNeighbors {
        if state.pattern.find(u) != -1 {
            hasUpperConnection = true;
            break;
        }
    }
    
    // Check potential for next level connections
    for u in outNeighbors {
        if !state.visited[u] {
            hasLowerConnection = true;
            break;
        }
    }
    
    return hasUpperConnection && hasLowerConnection;
}

/* 
 * Enhanced edge validity checking for random graphs.
 * Ensures degree sequence preservation.
 */
proc validateEdgeSwitch(edge1: (int,int), edge2: (int,int), 
                       const ref degrees: [?d] (int,int)): bool {
    var (src1, dst1) = edge1;
    var (src2, dst2) = edge2;
    
    // Check for direct overlap
    if src1 == src2 || dst1 == dst2 || src1 == dst2 || src2 == dst1 {
        return false;
    }
    
    // Check degree preservation
    var oldSrc1Out = degrees[src1][1];
    var oldDst1In = degrees[dst1][0];
    var oldSrc2Out = degrees[src2][1];
    var oldDst2In = degrees[dst2][0];
    
    // Simulate switch
    var newSrc1Out = oldSrc1Out;
    var newDst1In = oldDst1In - 1;
    var newSrc2Out = oldSrc2Out;
    var newDst2In = oldDst2In - 1;
    
    // Check if degrees remain valid
    return newSrc1Out >= 0 && newDst1In >= 0 && 
           newSrc2Out >= 0 && newDst2In >= 0;
}
/* Main execution procedure using these functions */
proc Kavosh(n: int, k: int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Kavosh ====");
    }

    var state = new KavoshState(n, k);
    
    // Process each vertex as root
    forall v in 0..<n with (ref state) {
        state.reset();
        state.visited[v] = true;
        state.pattern.pushBack(v);

        // Generate compositions
        var compositions = generateCompositions(k-1);
        
        // Process patterns
        for comp in compositions {
            enumeratePattern(v, comp, 0, state);
        }

        state.visited[v] = false;
        state.pattern.popBack();
    }

    return state.motifCounts;
}
    /* 
    * Wrapper function that orchestrates the entire motif finding process.
    * Called from runMotifCounting after graph data is extracted.
    */
    proc runKavosh() throws {
        if logLevel == LogLevel.DEBUG {
            writeln("\n==== Starting Kavosh wrapper ====");
            writeln("Graph info - Vertices: ", g1.n_vertices, " Edges: ", srcNodesG1.size);
            writeln("Motif size to find: ", g2.n_vertices);
        }

        var timer = new stopwatch();
        timer.start();
        
        // Initialize parameters for the core algorithm
        var n = g1.n_vertices;  // Size of main graph
        var k = g2.n_vertices;  // Size of motifs to find (from subgraph)

        if logLevel == LogLevel.DEBUG {
            writeln("\n-- Phase 1: Running core Kavosh algorithm on original graph");
        }
        
        // Run main Kavosh algorithm on original graph
        var originalMotifs = Kavosh(n, k);

        if logLevel == LogLevel.DEBUG {
            writeln("Found ", originalMotifs.size, " different subgraph patterns");
            writeln("\nPattern counts in original graph:");
            for (pattern, count) in originalMotifs {
                writeln("  Pattern: ", pattern, " Count: ", count.read());
            }
        }

        // Early termination check
        if limitTime && timer.elapsed():int >= timeLimit {
            if logLevel == LogLevel.DEBUG {
                writeln("Time limit reached after original graph analysis");
            }
            stopper.testAndSet();
            return originalMotifs;
        }

        if logLevel == LogLevel.DEBUG {
            writeln("\n-- Phase 2: Generating and analyzing random graphs");
        }

        // Generate and analyze random graphs for comparison
        const numRandomGraphs = 1000;  // As specified in paper
        var randomResults = generateRandomGraphs(numRandomGraphs);

        if logLevel == LogLevel.DEBUG {
            writeln("Generated and analyzed ", numRandomGraphs, " random graphs");
            writeln("Time elapsed: ", timer.elapsed(), " seconds");
        }


        if logLevel == LogLevel.DEBUG {
            writeln("\n-- Phase 3: Calculating significance metrics");
        }

        // Calculate statistical significance
        var (frequencies, zScores, pValues) = 
            calculateMotifSignificance(originalMotifs, randomResults);

        if logLevel == LogLevel.DEBUG {
            writeln("Completed significance calculations");
            writeln("Time elapsed: ", timer.elapsed(), " seconds");
        }

        // Organize results
        var results = new MotifAnalysisResults();
        results.frequencies = frequencies;
        results.zScores = zScores;
        results.pValues = pValues;

        // Identify significant motifs
        if logLevel == LogLevel.DEBUG {
            writeln("\n-- Phase 4: Identifying significant motifs");
        }

        for pattern in frequencies.keys() {
            var freq = frequencies[pattern];
            var zscore = zScores[pattern];
            var pvalue = pValues[pattern];
            
            if isMotif(pattern, freq, zscore, pvalue) {
                results.significantMotifs.pushBack(pattern);
                
                if logLevel == LogLevel.DEBUG {
                    writeln("\nFound significant motif:");
                    writeln("  Pattern: ", pattern);
                    writeln("  Frequency: ", freq);
                    writeln("  Z-score: ", zscore);
                    writeln("  P-value: ", pvalue);
                }
            }
        }

        timer.stop();

        if logLevel == LogLevel.DEBUG {
            writeln("\n==== Kavosh Analysis Complete ====");
            writeln("Total execution time: ", timer.elapsed(), " seconds");
            writeln("Found ", results.significantMotifs.size, " significant motifs");
            writeln("Processed ", frequencies.size, " total patterns");
        }

        return results;
    }// end of runKavosh 

    // Execute Kavosh algorithm
    runKavosh(); // Using subgraph size as motif size
      var tempArr: [0..0] int;
      var srcPerIso = makeDistArray(2*2, int);
      var dstPerIso = makeDistArray(2*2, int);
      return (srcPerIso, dstPerIso, tempArr, tempArr);
  }
}