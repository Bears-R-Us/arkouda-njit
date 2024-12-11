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


  var rng = new randomStream(real);

  /* Memory-efficient state management for large graphs */
class KavoshState {
    var n: int;              // Number of vertices
    var k: int;              // Motif size
    var visited: [0..<n] bool;
    var pattern: list(int);   
    var motifCounts: map(string, atomic int);
    
    // Track memory usage
    var totalPatterns: atomic int = 0;
    var maxPatternSize: atomic int = 0;
    
    proc init(n: int, k: int) {
        this.n = n;
        this.k = k;
        this.visited = false;
        this.pattern = new list(int);
        this.motifCounts = new map(string, atomic int);

        if logLevel == LogLevel.DEBUG {
            writeln("Initialized KavoshState for graph with ", n, " vertices");
            writeln("Looking for motifs of size ", k);
        }
    }
    
    proc reset() {
        this.visited = false;
        this.pattern.clear();
    }

    /* Track memory usage */
    proc updateMemoryStats() {
        totalPatterns.add(1);
        maxPatternSize.write(max(maxPatternSize.read(), pattern.size));
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
proc generateCombinations(domaina: domain(int, parSafe=true), k: int): list(list(int)) {
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

/* Generate integer compositions */
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



/* 
 * Process vertices according to a composition pattern. procedure for composition-based enumeration
*/
proc processComposition(v: int, composition: list(int), depth: int, state: KavoshState) {
    if logLevel == LogLevel.DEBUG {
        writeln("Processing composition at depth ", depth, " from vertex ", v);
    }

    // Base case: reached end of composition pattern
    if depth == composition.size {
        processFoundMotif(state);  // Changed from processPattern to processFoundMotif
        return;
    }
    
    // Get valid neighbors for current vertex
    var validNbrs = getValidNeighbors(v, state);
    var need = composition[depth];
    
    if logLevel == LogLevel.DEBUG {
        writeln("  Need ", need, " vertices at depth ", depth);
        writeln("  Found ", validNbrs.size, " valid neighbors");
    }
    
    // Only proceed if we have enough valid neighbors
    if validNbrs.size >= need {
        var combos = generateCombinations(validNbrs, need);
        
        if logLevel == LogLevel.DEBUG {
            writeln("  Generated ", combos.size, " combinations");
        }
        
        // Process each combination
        for combo in combos {
            // Add vertices
            for u in combo {
                state.pattern.pushBack(u);
                state.visited[u] = true;
                
                if logLevel == LogLevel.DEBUG {
                    writeln("    Added vertex ", u, " to pattern");
                }
            }
            
            // Recurse
            for u in combo {
                processComposition(u, composition, depth+1, state);
            }
            
            // Remove vertices (backtrack)
            for u in combo {
                state.pattern.popBack();
                state.visited[u] = false;
            }
            
            if logLevel == LogLevel.DEBUG {
                writeln("    Backtracked combination at depth ", depth);
            }
        }
    }
}
/* 
 * Check if edge exists in the graph

 */
proc edgeExists(src: int, dst: int): bool {
    if logLevel == LogLevel.DEBUG {
        writeln("Checking edge existence: ", src, " -> ", dst);
    }

    // Check in original graph's edge list
    var start = segGraphG1[src];
    var end = segGraphG1[src+1];
    
    for i in start..<end {
        if dstNodesG1[i] == dst {
            if logLevel == LogLevel.DEBUG {
                writeln("  Edge found");
            }
            return true;
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("  Edge not found");
    }
    return false;
}

/* 
 * Build a graph from a list of edges
 */
proc buildGraphFromEdges(edges: list((int,int))) {
    if logLevel == LogLevel.DEBUG {
        writeln("Building graph from ", edges.size, " edges");
    }

    var n = g1.n_vertices;  // Use same number of vertices as original graph
    var m = edges.size;

    // Create arrays for graph representation
    var srcNodes = makeDistArray(m, int);
    var dstNodes = makeDistArray(m, int);
    var segments = makeDistArray(n+1, int);
    
    segments = 0;  // Initialize segments array

    // Count edges per vertex
    for (src, _) in edges {
        segments[src+1] += 1;
    }

    if logLevel == LogLevel.DEBUG {
        writeln("  Counted edges per vertex");
    }

    // Calculate segment offsets
    for i in 1..n {
        segments[i] += segments[i-1];
    }

    // Place edges
    var counts = makeDistArray(n, int);
    counts = 0;
    
    for (src, dst) in edges {
        var idx = segments[src] + counts[src];
        srcNodes[idx] = src;
        dstNodes[idx] = dst;
        counts[src] += 1;
    }

    if logLevel == LogLevel.DEBUG {
        writeln("  Built graph with:");
        writeln("    Vertices: ", n);
        writeln("    Edges: ", m);
        var maxDegree = max reduce counts;
        writeln("    Max degree: ", maxDegree);
    }

    return (srcNodes, dstNodes, segments);
}

/* 
 * Update motif counts from random graph analysis
 */
proc updateRandomMotifCounts(motifs: map(string, atomic int)) {
    if logLevel == LogLevel.DEBUG {
        writeln("Updating random motif counts");
        writeln("  Processing ", motifs.size, " patterns");
    }

    // This function would update global statistics about random graph motifs
    // Implementation depends on how you want to store and process random graph results
    
    if logLevel == LogLevel.DEBUG {
        writeln("  Updated random motif counts");
    }
}

/* 
 * Enumerate vertices according to composition pattern.
 * Called by Kavosh() for each composition to build motifs.
 */
proc enumeratePattern(v: int, pattern: list(int), depth: int, ref state: KavoshState) throws {
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
    var validNbrs: domain(int, parSafe=true);
    
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

/* 
 * Process a found motif pattern by generating its canonical label 
 * and updating counts.
 */
proc processFoundMotif(ref state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Processing pattern of size ", state.pattern.size);
    }

    // Build adjacency matrix only for the pattern size
    var n = state.pattern.size;
    var adjMatrix: [0..<n, 0..<n] bool = false;

    // Fill adjacency matrix efficiently
    for (i, v) in zip(0..<n, state.pattern) {
        var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
        for nbr in outNeighbors {
            var idx = state.pattern.find(nbr);
            if idx != -1 {
                adjMatrix[i, idx] = true;
            }
        }
    }

    var labela = generateCanonicalLabel(adjMatrix);
    updateMotifCount(labela, state);
    state.updateMemoryStats();
}

/* 
 * NAUTY-like canonical labeling for directed graphs.
 * Takes adjacency matrix and generates unique identifier.
 */
/* Generate canonical label for directed graphs using NAUTY-like approach */
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
}

/* Calculate statistical significance of potential motifs */
proc calculateMotifSignificance(originalMotifs: map(string, atomic int), 
                              randomMotifs: [?d] map(string, atomic int)) {
    var zScores: map(string, real);
    var pValues: map(string, real);
    var frequencies: map(string, int);

    // Process each pattern in parallel
    var patterns = originalMotifs.keys();
    forall pattern in patterns with (ref zScores, ref pValues, ref frequencies) {
        var origCount = originalMotifs[pattern].read();
        frequencies[pattern] = origCount;

        // Local accumulators for this pattern
        var sum = 0.0;
        var sumSquares = 0.0;
        var moreFrequent = 0;
        var validCount = 0;

        // Process random networks
        forall i in randomMotifs.domain with (+ reduce sum, 
                                            + reduce sumSquares,
                                            + reduce moreFrequent,
                                            + reduce validCount) {
            if randomMotifs[i].contains(pattern) {
                var count = randomMotifs[i][pattern].read():real;
                sum += count;
                sumSquares += count * count;
                if count >= origCount then moreFrequent += 1;
                validCount += 1;
            }
        }

        // Calculate statistics
        if validCount > 0 {
            var mean = sum / validCount;
            var variance = (sumSquares - (sum * sum / validCount)) / (validCount - 1);
            var stdDev = sqrt(max(0.0, variance));
            
            zScores[pattern] = if stdDev > 0.0 then (origCount - mean) / stdDev else 0.0;
            pValues[pattern] = moreFrequent:real / validCount:real;
        } else {
            zScores[pattern] = if origCount > 0 then max(real) else 0.0;
            pValues[pattern] = 0.0;
        }
    }

    return (frequencies, zScores, pValues);
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
/* Generate random graphs preserving degree sequence */
proc generateRandomGraphs(numGraphs: int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Generating ", numGraphs, " random graphs");
    }

    // Original graph edges - shared read-only data
    var edges: list((int,int));
    var degrees: [0..<g1.n_vertices] (int,int);

    // Initialize shared data - done once
    {
        // Calculate initial degrees
        forall v in 0..<g1.n_vertices {
            degrees[v] = (
                segRG1[v+1] - segRG1[v],      // inDegree
                segGraphG1[v+1] - segGraphG1[v] // outDegree
            );
        }

        // Collect edges
        for v in 0..<g1.n_vertices {
            var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
            for u in outNeighbors {
                edges.pushBack((v,u));
            }
        }
    }

    // Results array - each task writes to its own index
    var randomResults: [0..#numGraphs] map(string, atomic int);

    // Generate random graphs in parallel
    forall i in 0..#numGraphs with (ref randomResults) {
        // Create local copies for this task
        var localEdges = new list((int,int));
        var localDegrees = degrees;
        
        // Copy edges locally
        for e in edges do localEdges.pushBack(e);

        // Perform edge switches
        var numSwitches = 100 * edges.size;
        var rngStream = new randomStream(real, seed=i); // Unique RNG per task

        for j in 1..numSwitches {
            var idx1 = (rngStream.next() * (localEdges.size-1)):int;
            var idx2 = (rngStream.next() * (localEdges.size-1)):int;
            
            if validateEdgeSwitch(localEdges[idx1], localEdges[idx2], localDegrees, localEdges) {
                // Perform switch
                var (src1, dst1) = localEdges[idx1];
                var (src2, dst2) = localEdges[idx2];
                
                localEdges[idx1] = (src1, dst2);
                localEdges[idx2] = (src2, dst1);
            }
        }

        // Build and analyze random graph
        var (randomSrc, randomDst, randomSeg) = buildRandomGraph(localEdges);
        var randomState = new KavoshState(g1.n_vertices, g2.n_vertices);
        
        // Process the random graph
        runKavoshOnRandom(randomState, randomSrc, randomDst, randomSeg);
        
        // Store results
        randomResults[i] = randomState.motifCounts;


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
        writeln("Building random graph with ", edges.size, " edges");
    }
    
    var n = g1.n_vertices;
    var m = edges.size;
    
    // Pre-allocate arrays
    var srcNodes = makeDistArray(m, int);
    var dstNodes = makeDistArray(m, int);
    var segments = makeDistArray(n+1, int);
    
    segments = 0;
    
    // Two-pass approach to minimize memory usage
    // First pass: count edges per vertex
    for (src, _) in edges {
        segments[src+1] += 1;
    }
    
    // Calculate offsets
    for i in 1..n {
        segments[i] += segments[i-1];
    }
    
    // Second pass: place edges
    var counts = makeDistArray(n, int);
    counts = 0;
    
    for (src, dst) in edges {
        var idx = segments[src] + counts[src];
        srcNodes[idx] = src;
        dstNodes[idx] = dst;
        counts[src] += 1;
    }
    
    if logLevel == LogLevel.DEBUG {
        var maxEdgesPerVertex = max reduce counts;
        writeln("Maximum edges per vertex: ", maxEdgesPerVertex);
    }
    
    return (srcNodes, dstNodes, segments);
}


/* Run Kavosh on random graph */
proc runKavoshOnRandom(ref state: KavoshState, 
                      const ref srcNodes: [] int,
                      const ref dstNodes: [] int,
                      const ref segments: [] int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Running Kavosh on random graph");
    }
    
    state.reset(); // Ensure clean state before starting

    forall v in 0..<state.n with (ref state) {
        // Save original state for backtracking
        var originalVisited = state.visited;
        var originalPattern = state.pattern;

        state.visited[v] = true;
        state.pattern.pushBack(v);

        var compositions = generateCompositions(state.k-1);
        for comp in compositions {
            enumeratePatternRandom(v, comp, 0, state, srcNodes, dstNodes, segments);
        }

        // Restore original state
        state.visited = originalVisited;
        state.pattern = originalPattern;
    }
}

/* Pattern enumeration for random graph analysis */
proc enumeratePatternRandom(v: int, pattern: list(int), depth: int,
                          ref state: KavoshState,
                          const ref srcNodes: [] int,
                          const ref dstNodes: [] int,
                          const ref segments: [] int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Random enumeration at depth ", depth, " from vertex ", v);
    }

    // Base case: pattern complete
    if depth == pattern.size {
        processFoundMotif(state);
        return;
    }

    // Get neighbors from random graph's segment representation
    var validNbrs: domain(int, parSafe=true);
    
    // Get range for outgoing edges
    var start = segments[v];
    var end = if v < segments.domain.high then segments[v+1] else dstNodes.size;
    
    // Add valid unvisited neighbors
    for i in start..<end {
        var nbr = dstNodes[i];
        if !state.visited[nbr] {
            // We still use validateVertex to maintain connectivity constraints
            if validateVertex(nbr, depth, state) {
                validNbrs.add(nbr);
                if logLevel == LogLevel.DEBUG {
                    writeln("  Added valid neighbor: ", nbr);
                }
            }
        }
    }

    var k = pattern[depth];
    if validNbrs.size >= k {
        var combinations = generateCombinations(validNbrs, k);
        
        // Process each combination
        for combo in combinations {
            var addedVertices: list(int);

            // Add vertices in combination
            for u in combo {
                state.pattern.pushBack(u);
                state.visited[u] = true;
                addedVertices.pushBack(u);
            }
            
            // Recurse on each vertex
            for u in combo {
                enumeratePatternRandom(u, pattern, depth+1,
                                     state, srcNodes, dstNodes, segments);
                if stopper.read() then break;
            }
            
            // Backtrack - remove added vertices
            for u in addedVertices {
                state.pattern.popBack();
                state.visited[u] = false;
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

    // 1. Get patterns from Kavosh
    var originalMotifs = runKavosh();

    if logLevel == LogLevel.DEBUG {
        writeln("\n-- Phase 1: Original graph analysis complete");
        writeln("Found patterns: ", originalMotifs.size);
    }

    // 2. Generate and analyze random graphs
    if logLevel == LogLevel.DEBUG {
        writeln("\n-- Phase 2: Random Graph Analysis");
    }
    
    const numRandomGraphs = 1000;
    var randomResults = generateRandomGraphs(numRandomGraphs);

    // 3. Calculate significance
    if logLevel == LogLevel.DEBUG {
        writeln("\n-- Phase 3: Statistical Analysis");
    }
    var (frequencies, zScores, pValues) = 
        calculateMotifSignificance(originalMotifs, randomResults);

    // 4. Prepare results
    var results = new MotifAnalysisResults();
    results.frequencies = frequencies;
    results.zScores = zScores;
    results.pValues = pValues;

    // Identify significant motifs
    for pattern in frequencies.keys() {
        if isMotif(pattern, frequencies[pattern], zScores[pattern], pValues[pattern]) {
            results.significantMotifs.pushBack(pattern);
        }
    }

    // Report results
    reportResults(results);
    
    return results;
}


/* Comprehensive result reporting */
proc reportResults(results: MotifAnalysisResults) {
    if logLevel == LogLevel.DEBUG {
        writeln("\n======= Motif Analysis Results =======");
        writeln("Found ", results.significantMotifs.size, " significant motifs");
        writeln("\nSignificant Motifs Details:");
        
        for pattern in results.significantMotifs {
            writeln("\nMotif Pattern: ", pattern);
            writeln("  Frequency: ", results.frequencies[pattern]);
            writeln("  Z-score: ", results.zScores[pattern]);
            writeln("  P-value: ", results.pValues[pattern]);
            /*
            // Convert pattern to adjacency matrix for visualization
            var n = sqrt(pattern.length): int;  // Pattern is flattened matrix
            writeln("\n  Adjacency Matrix:");
            for i in 0..<n {
                write("  ");
                for j in 0..<n {
                    write(pattern[i*n + j], " ");
                }
                writeln();
            }*/
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

/* Validate edge switch while preserving degrees */
proc validateEdgeSwitch(edge1: (int,int), edge2: (int,int), 
                       const ref degrees: [?d] (int,int),
                       const ref edges: list((int,int))): bool {
    var (src1, dst1) = edge1;
    var (src2, dst2) = edge2;
    
    // Basic validity checks
    if src1 == src2 || dst1 == dst2 || 
       src1 == dst2 || src2 == dst1 || 
       src1 == dst1 || src2 == dst2 {
        return false;
    }
    
    // Check if new edges would exist after switch
    var newEdge1 = (src1, dst2);
    var newEdge2 = (src2, dst1);
    
    // Check for edge existence in O(1) using a domain
    var edgeSet: domain((int,int));
    for e in edges do edgeSet.add(e);
    
    if edgeSet.contains(newEdge1) || edgeSet.contains(newEdge2) {
        return false;
    }

    // Verify degree sequence preservation
    var (inDeg1, outDeg1) = degrees[src1];
    var (inDeg2, outDeg2) = degrees[src2];
    var (inDegD1, outDegD1) = degrees[dst1];
    var (inDegD2, outDegD2) = degrees[dst2];

    // Degrees should remain same after switch
    if inDeg1 != inDegD2 || inDeg2 != inDegD1 ||
       outDeg1 != outDegD2 || outDeg2 != outDegD1 {
        return false;
    }

    return true;
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
}// end of Kavosh
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

    // Initialize parameters for the core algorithm
    var n = g1.n_vertices;
    var k = g2.n_vertices;

    // Run main Kavosh algorithm on original graph
    var originalMotifs = Kavosh(n, k);

    if logLevel == LogLevel.DEBUG {
        writeln("Found ", originalMotifs.size, " different subgraph patterns");
    }

    return originalMotifs;
}// end of runKavosh 

    // Execute Kavosh algorithm
    runKavosh(); // Using subgraph size as motif size
      var tempArr: [0..0] int;
      var srcPerIso = makeDistArray(2*2, int);
      var dstPerIso = makeDistArray(2*2, int);
      return (srcPerIso, dstPerIso, tempArr, tempArr);
  }
}