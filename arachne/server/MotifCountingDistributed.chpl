module MotifCountingDistributed {
  // Chapel modules.
  use Reflection;
  use Map;
  use List;
  use Set;
  use Random;
  use IO;
  use Time;
  use Sort;
  use Math;
  use Search;
  use CTypes;
  use CommDiagnostics;
  import CopyAggregation.SrcAggregator;
  import CopyAggregation.DstAggregator;

  // Arachne modules.
  use GraphArray;
  use Utils;
  use Logging;
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;

  import MotifCountingMsg.siLogger_motif;

  // C header and object files for nauty.
  require "nauty-wrapper/bin/nautyClassify.o",
          "nauty-wrapper/include/nautyClassify.h",
          "nauty-wrapper/bin/nauty.o",
          "nauty-wrapper/bin/nautil.o",
          "nauty-wrapper/bin/naugraph.o",
          "nauty-wrapper/bin/schreier.o",
          "nauty-wrapper/bin/naurng.o",
          "nauty-wrapper/bin/nausparse.o";

  // External C function for classifying subgraphs
  extern proc c_nautyClassify(
      subgraph: [] int(64), 
      subgraphSize: int(64), 
      results: [] int(64),
      performCheck: int(64),
      verbose: int(64),
      batchSize: int(64)
  ) : int(64);

  /* KavoshState class keeps track of the state during the enumeration of subgraphs */
  class KavoshState {
    var n: int;
    var k: int;
    var maxDeg: int;
    var visited: domain(int, parSafe=true);

    // Use 1D arrays for storage
    var subgraph: [0..#(k * (k+1))] int;  
    var childSet: [0..#(k * ((maxDeg*k)+2))] int;
    var indexMap: [0..#(k * ((maxDeg*k)+2))] int;

    var localSubgraphCount: int;
    var motifVertices: list(int, parSafe=true);

    // Helper functions to convert 2D indexing to 1D
    inline proc getSubgraphIndex(level: int, pos: int): int {
      return level * (k+1) + pos;
    }

    inline proc getChildSetIndex(level: int, pos: int): int {
      return level * ((maxDeg*k)+2) + pos;
    }

    inline proc getIndexMapIndex(level: int, pos: int): int {
      return level * ((maxDeg*k)+2) + pos;
    }

    // Functions to get/set values using 2D-style indexing
    inline proc getSubgraph(level: int, pos: int): int {
      return subgraph[getSubgraphIndex(level, pos)];
    }

    inline proc setSubgraph(level: int, pos: int, value: int) {
      subgraph[getSubgraphIndex(level, pos)] = value;
    }

    inline proc getChildSet(level: int, pos: int): int {
      return childSet[getChildSetIndex(level, pos)];
    }

    inline proc setChildSet(level: int, pos: int, value: int) {
      childSet[getChildSetIndex(level, pos)] = value;
    }

    inline proc getIndexMap(level: int, pos: int): int {
      return indexMap[getIndexMapIndex(level, pos)];
    }

    inline proc setIndexMap(level: int, pos: int, value: int) {
      indexMap[getIndexMapIndex(level, pos)] = value;
    }

    proc init(n: int, k: int, maxDeg: int) {
      this.n = n;
      this.k = k;
      this.maxDeg = maxDeg;
      this.visited = {1..0};
      this.subgraph = 0;
      this.childSet = 0;
      this.indexMap = 0;
      this.localSubgraphCount = 0;
      this.motifVertices = new list(int, parSafe=true);
    }
  }

  /* Record for comparing motif patterns by frequency */
  record PatternComparator {
    proc compare(a: (uint(64), int), b: (uint(64), int)): int {
      // Sort by count (descending)
      if a(1):int != b(1):int then
        return b(1):int - a(1):int;
      // Break ties by pattern ID
      return a(0):int - b(0):int;
    }
  }

  /* Main entry point for distributed MotifCounting motif counting */
  proc runMotifCountingDistributed(g1: SegGraph,  
               motifSize: int, doSampling: int, in printProgressInterval: int,
               algType: string, returnIsosAs:string, st: borrowed SymTab) throws {
    
    var startTime:stopwatch;
    startTime.start();
    // Extract graph components
    const ref srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    const ref dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    const ref segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
    const ref dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
    const ref segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;

    // Get graph size
    var n = nodeMapGraphG1.size;
    var mG1 = srcNodesG1.size;
    var k = motifSize;

    var outMsg = "Starting Kavosh with k = " + k:string + " on graph with " + 
                 n:string + " vertices and " + mG1:string + " edges";
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);

    // Make block-distributed domain where each locale will own a subset of vertices
    var localeDom = blockDist.createDomain(0..<numLocales);
    
    // Calculate vertices per locale for balanced distribution
    const verticesPerLocale = (n + numLocales - 1) / numLocales;
    var vertexRanges: [localeDom] range(int); 
    
    // Create vertex ranges for each locale
    for loc in 0..<numLocales {
      var start = min(loc * verticesPerLocale, n);
      var end = min((loc + 1) * verticesPerLocale, n);
      vertexRanges[loc] = start..<end;
    }
    
    // Log the distribution of vertices
    for loc in 0..<numLocales {
      siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(),
                      "Locale " + loc:string + " received vertices " + 
                      vertexRanges[loc].low:string + " to " + vertexRanges[loc].high:string + 
                      " (total: " + vertexRanges[loc].size:string + ")");
    }

    // --- Precompute ALL node neighbors on locale 0 ---
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(),
                     "Precomputing all node neighbors (optimized approach)");
    
    // Create global arrays for node data
    var nodeDegree: [0..<n] int;
    var nodeNeighbors: [0..<n] domain(int, parSafe=true);
    var nodeOutNeighbors: [0..<n] domain(int, parSafe=true);
    
    // Compute all neighbors on locale 0
    forall v in 0..<n with (ref nodeDegree, ref nodeNeighbors, ref nodeOutNeighbors) {
      var neighbors: domain(int, parSafe=true);
      
      // Get in-neighbors (reverse edges)
      const neiIn = dstRG1[segRG1[v]..<segRG1[v+1]];
      for nei in neiIn {
        neighbors.add(nei);
      }
      
      // Get out-neighbors (forward edges)
      const neiOut = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
      for nei in neiOut {
        nodeOutNeighbors[v].add(nei);
        neighbors.add(nei);
      }
      
      // Store all neighbors and degree
      nodeNeighbors[v] = neighbors;
      nodeDegree[v] = neighbors.size;
    }
    
    // Compute global max degree
    var maxDeg = max reduce nodeDegree;
    
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(), 
                     "Maximum degree in graph: " + maxDeg:string);
    
    // --- Efficient data transfer to all locales ---
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(),
                     "Distributing neighbor data to all locales");

    // Create distributed data structures for each locale
    var nodeNeighborsDist: [localeDom] [0..<n] domain(int, parSafe=true);
    var nodeOutNeighborsDist: [localeDom] [0..<n] domain(int, parSafe=true);
    var nodeDegreeDist: [localeDom] [0..<n] int;

    // Start tracking communication
    startCommDiagnostics();

    // Copy data to each locale using efficient aggregation
    coforall loc in Locales do on loc {
      const blockSize = 1000;  // Process data in blocks for efficiency
      
      // Initialize arrays for this locale
      var localNodeNeighbors: [0..<n] domain(int, parSafe=true);
      var localNodeOutNeighbors: [0..<n] domain(int, parSafe=true);
      var localNodeDegree: [0..<n] int;
      
      // Copy data from locale 0 using aggregators
      for blockStart in 0..n by blockSize {
        const blockEnd = min(blockStart + blockSize, n);
        
        // Copy degree values (simple integers)
        if loc.id != 0 {  // Skip locale 0 which already has the data
          forall v in blockStart..<blockEnd with (var agg = new SrcAggregator(int)) {
            agg.copy(localNodeDegree[v], nodeDegree[v]);
          }
        }
        
        // Note: Domains need special handling as they can't be directly copied with aggregators
        // We'll recreate them by copying the elements
        forall v in blockStart..<blockEnd {
          if loc.id == 0 {
            // Locale 0 already has the data, just copy references
            localNodeNeighbors[v] = nodeNeighbors[v];
            localNodeOutNeighbors[v] = nodeOutNeighbors[v];
          } else {
            // Other locales need to rebuild the domains
            // Get the neighbors from locale 0
            const neighbors = nodeNeighbors[v];
            const outNeighbors = nodeOutNeighbors[v];
            
            // Add each neighbor to the local domain
            for nei in neighbors {
              localNodeNeighbors[v].add(nei);
            }
            
            for nei in outNeighbors {
              localNodeOutNeighbors[v].add(nei);
            }
          }
        }
      }
      
      // Store in distributed arrays
      nodeNeighborsDist[loc.id] = localNodeNeighbors;
      nodeOutNeighborsDist[loc.id] = localNodeOutNeighbors;
      nodeDegreeDist[loc.id] = localNodeDegree;
    }

    // Print communication diagnostics for data copying
    outMsg = "Communication statistics for copying neighbor data:";
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
    printCommDiagnosticsTable();
    resetCommDiagnostics();

    // Create global motif tracking structures
    var globalMotifCountDist: [localeDom] atomic int;
    var globalMotifSetDist: [localeDom] set(uint(64), parSafe=true);
    var globalMotifMapDist: [localeDom] map(uint(64), int, parSafe=true);
    var seenMatricesDist: [localeDom] set(uint(64), parSafe=true);

    // Start diagnosing the computation phase
    startCommDiagnostics();
    
    // --- Run Kavosh in parallel across locales ---
    coforall loc in Locales do on loc {
      const myVertices = vertexRanges[loc.id];
      var localCount: atomic int;
      localCount.write(0);
      
      // Get local references to neighbor data for this locale
      const ref localNodeNeighbors = nodeNeighborsDist[loc.id];
      const ref localNodeOutNeighbors = nodeOutNeighborsDist[loc.id];
      const ref localNodeDegree = nodeDegreeDist[loc.id];
      
      if logLevel == LogLevel.DEBUG {
        siLogger_motif.debug(getModuleName(), getRoutineName(), getLineNumber(),
                         "Locale " + loc.id:string + " processing vertices " + 
                         myVertices.low:string + " to " + (myVertices.high):string);
      }
      
      /* Helper function to gather neighbors for a subgraph state */
      proc initChildSet(ref state: KavoshState, root: int, level: int) {
        // Initialize count for this level to 0
        state.setChildSet(level, 0, 0);
        const parentsCount = state.getSubgraph(level-1, 0);
        
        // For each vertex chosen at the previous level, get its neighbors
        for p in 1..parentsCount {
          const parent = state.getSubgraph(level-1, p);
          
          // Direct neighbor lookup from local arrays
          for neighbor in localNodeNeighbors[parent] {
            // Must be greater than root and not visited
            if neighbor > root && !state.visited.contains(neighbor) {
              // Increment count and add neighbor
              const currentCount = state.getChildSet(level, 0) + 1;
              state.setChildSet(level, 0, currentCount);
              state.setChildSet(level, currentCount, neighbor);
              state.visited.add(neighbor);
            }
          }
        }
      }
      
      /* Helper function to prepare arguments for nauty */
      proc prepareNautyArguments(ref state: KavoshState) {
        // Build array of chosen vertices
        var chosenVerts: [1..state.k] int;
        var idx = 1;
        
        // Gather vertices level by level
        for level in 0..<state.k {
          const vertCount = state.getSubgraph(level, 0);
          for pos in 1..vertCount {
            chosenVerts[idx] = state.getSubgraph(level, pos);
            idx += 1;
          }
        }
        
        // Create adjacency matrix
        var adjMatrix: [0..#(state.k * state.k)] int = 0;
        
        // Fill adjacency matrix - direct access to nodeOutNeighbors
        for i in 0..#state.k {
          for j in 0..#state.k {
            if i != j {  // Skip self-loops
              var u = chosenVerts[i+1];  // +1 because chosenVerts is 1-based
              var w = chosenVerts[j+1];
              
              // Direct neighbor check (no cross-locale lookup needed)
              if localNodeOutNeighbors[u].contains(w) {
                adjMatrix[i * state.k + j] = 1;
              }
            }
          }
        }
        
        return (adjMatrix, chosenVerts);
      }
      
      /* Main recursive subgraph exploration function */
      proc explore(ref state: KavoshState, root: int, level: int, remainedToVisit: int) {
        // Base case: all k vertices chosen, we've found a motif
        if remainedToVisit == 0 {
          // Extract the chosen vertices
          var chosenVerts: [1..state.k] int;
          var idx = 1;
          
          // Gather vertices level by level
          for level in 0..<state.k {
            const vertCount = state.getSubgraph(level, 0);
            for pos in 1..vertCount {
              chosenVerts[idx] = state.getSubgraph(level, pos);
              state.motifVertices.pushBack(chosenVerts[idx]);
              idx += 1;
            }
          }
          state.localSubgraphCount += 1;
          
          return;
        }
        
        // Get children for this level
        initChildSet(state, root, level);
        const childCount = state.getChildSet(level, 0);
        
        // Try all possible selection sizes at this level
        for selSize in 1..remainedToVisit {
          if childCount < selSize {
            // Not enough children, clean up and return
            for i in 1..childCount {
              state.visited.remove(state.getChildSet(level, i));
            }
            return;
          }
          
          // Initial selection: pick the first selSize children
          state.setSubgraph(level, 0, selSize);
          for i in 1..selSize {
            state.setSubgraph(level, i, state.getChildSet(level, i));
            state.setIndexMap(level, i, i);
          }
          
          // Recurse with chosen selection
          explore(state, root, level+1, remainedToVisit - selSize);
          
          // Generate other combinations using revolve-door algorithm
          forwardGenerator(childCount, selSize, root, level, remainedToVisit, selSize, state);
        }
        
        // Cleanup: Unmark visited children
        for i in 1..childCount {
          state.visited.remove(state.getChildSet(level, i));
        }
        state.setSubgraph(level, 0, 0);
      }
      
      /* swappingFunction: Used by revolve-door algorithm */
      proc swappingFunction(i: int, j: int, root: int, level: int, remainedToVisit: int, m: int, 
                          ref state: KavoshState) {
        state.setIndexMap(level, i, state.getIndexMap(level, j));
        state.setSubgraph(level, state.getIndexMap(level, i), state.getChildSet(level, i));
        
        explore(state, root, level+1, remainedToVisit - m);
      }
      
      /* forwardGenerator: Part of revolve-door combination generation */
      proc forwardGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, 
                          ref state: KavoshState) {
        if k > 0 && k < n {
          forwardGenerator(n-1, k, root, level, remainedToVisit, m, state);
          
          if k == 1 {
            swappingFunction(n, n-1, root, level, remainedToVisit, m, state);
          } else {
            swappingFunction(n, k-1, root, level, remainedToVisit, m, state);
          }
          
          reverseGenerator(n-1, k-1, root, level, remainedToVisit, m, state);
        }
      }
      
      /* reverseGenerator: Another part of revolve-door combination generation */
      proc reverseGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, 
                          ref state: KavoshState) {
        if k > 0 && k < n {
          forwardGenerator(n-1, k-1, root, level, remainedToVisit, m, state);
          
          if k == 1 {
            swappingFunction(n-1, n, root, level, remainedToVisit, m, state);
          } else {
            swappingFunction(k-1, n, root, level, remainedToVisit, m, state);
          }
          
          reverseGenerator(n-1, k, root, level, remainedToVisit, m, state);
        }
      }
      
      /* Generate canonical pattern from adjacency matrix and nauty labels */
      proc generateNautyPattern(adjMatrix: [] int, nautyLabels: [] int, k: int): uint(64) {
        var pattern: uint(64) = 0;
        var pos = 0;
        
        // Generate canonical pattern by applying nauty labeling
        for i in 0..<k {
          for j in 0..<k {
            if i != j {  // Skip self-loops
              // Get the position in the input matrix based on nauty labels
              var row = nautyLabels[i];
              var col = nautyLabels[j];
              
              // Check if there's an edge in the original matrix at these positions
              if row < k && col < k && adjMatrix[row * k + col] == 1 {
                // Set bit for this edge in canonical pattern
                pattern |= 1:uint(64) << pos;
              }
            }
            pos += 1;
          }
        }
        
        return pattern;
      }
      
      /* Process discovered motifs to find canonical patterns */
      proc processMotifs(ref state: KavoshState, k: int) {
        const numMotifs = state.localSubgraphCount;
        const totalVertices = state.motifVertices.size;
        
        // Skip if no motifs found
        if numMotifs == 0 || totalVertices == 0 {
          return;
        }
        
        // Get the motif vertices as an array
        var motifVerticesArray = state.motifVertices.toArray();
        
        // Create arrays for batch processing
        var batchedMatrices: [0..#(numMotifs * k * k)] int = 0;
        var batchedResults: [0..#(numMotifs * k)] int;
        
        // Track which matrices need to be processed
        var matricesToProcess: list((int, uint(64)));  // (index, binary) pairs for new matrices
        var seenIndices: domain(int, parSafe=false);  // Indices of matrices we've seen before
        var patternToOriginalMapping: map(uint(64), list(uint(64)));  // Map to track original patterns
        
        // Fill matrices and check for duplicates
        for i in 0..<numMotifs {
          var baseIdx = i * k;
          var matrixBinary: uint(64) = 0;  // Binary representation for this matrix
          
          // Create adjacency matrix for this motif
          for row in 0..<k {
            for col in 0..<k {
              if row != col {  // Skip self-loops
                var u = motifVerticesArray[baseIdx + row];
                var w = motifVerticesArray[baseIdx + col];
                
                // Direct neighbor check (no cross-locale lookup needed)
                if localNodeOutNeighbors[u].contains(w) {
                  batchedMatrices[i * (k * k) + row * k + col] = 1;
                  
                  // Update binary representation
                  matrixBinary |= 1:uint(64) << (row * k + col);
                }
              }
            }
          }
          
          // Check if we've seen this matrix before
          if seenMatricesDist[loc.id].contains(matrixBinary) {
            // We've seen this pattern before, skip Nauty processing
            seenIndices.add(i);
          } else {
            // New pattern, add to seen matrices and process
            seenMatricesDist[loc.id].add(matrixBinary);
            matricesToProcess.pushBack((i, matrixBinary));
          }
        }
        
        // Process only unseen matrices with Nauty
        if matricesToProcess.size > 0 {
          // Create smaller batch arrays for just the unseen matrices
          var uniqueCount = matricesToProcess.size;
          var uniqueMatrices: [0..#(uniqueCount * k * k)] int = 0;
          var uniqueResults: [0..#(uniqueCount * k)] int;
          
          // Fill unique matrices array
          for i in 0..<uniqueCount {
            var (origIdx, _) = matricesToProcess[i];
            var origOffset = origIdx * (k * k);
            var newOffset = i * (k * k);
            
            // Copy matrix from original batch to unique batch
            for j in 0..<(k * k) {
              uniqueMatrices[newOffset + j] = batchedMatrices[origOffset + j];
            }
          }
          
          // Process only unique matrices with Nauty
          var status = c_nautyClassify(uniqueMatrices, k, uniqueResults, 1, 0, uniqueCount);
          
          // Process results to get canonical patterns
          for i in 0..<uniqueCount {
            var (origIdx, originalBinary) = matricesToProcess[i];
            var resultOffset = i * k;
            
            // Extract nauty labels for this matrix
            var nautyLabels: [0..<k] int;
            for j in 0..<k {
              nautyLabels[j] = uniqueResults[resultOffset + j];
            }
            
            // Get adjacency matrix for this motif
            var adjMatrixStart = origIdx * (k * k);
            var adjMatrix: [0..#(k*k)] int;
            for j in 0..#(k*k) {
              adjMatrix[j] = batchedMatrices[adjMatrixStart + j];
            }
            
            // Generate canonical pattern
            var canonicalPattern = generateNautyPattern(adjMatrix, nautyLabels, k);
            
            // Add mapping from original binary to canonical pattern
            if !patternToOriginalMapping.contains(canonicalPattern) {
              patternToOriginalMapping[canonicalPattern] = new list(uint(64));
            }
            patternToOriginalMapping[canonicalPattern].pushBack(originalBinary);
            
            // Add to global set
            globalMotifSetDist[loc.id].add(canonicalPattern);
            
            // Update count in global map - using thread-safe operations
            if globalMotifMapDist[loc.id].contains(canonicalPattern) {
              var defaultCount: int = 0; // Provide a default value
              var currentCount = globalMotifMapDist[loc.id].get(canonicalPattern, defaultCount);
              globalMotifMapDist[loc.id].addOrReplace(canonicalPattern, currentCount + 1);
            } else {
              globalMotifMapDist[loc.id].add(canonicalPattern, 1);
            }
          }
        }
        
        // Count all motifs
        localCount.add(numMotifs);
      }
      
      /* Main execution for each vertex on this locale */
      forall v in myVertices {
        var state = new KavoshState(n, k, maxDeg);
        
        // Initialize root vertex in subgraph
        state.setSubgraph(0, 0, 1);
        state.setSubgraph(0, 1, v);
        state.visited.clear();
        state.visited.add(v);
        
        // Find all motifs for this root
        explore(state, v, 1, state.k - 1);
        
        // Process the motifs to find canonical patterns
        processMotifs(state, k);
        
        // Print progress if appropriate
        // if printProgressInterval > 0 && v % printProgressInterval == 0 {
        //   siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(),
        //                    "Processed vertex " + v:string + " on locale " + loc.id:string);
        // }
      }
      
      // Update global count
      globalMotifCountDist[loc.id].write(localCount.read());
      
      siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(),
                       "Locale " + loc.id:string + " found " + localCount.read():string + 
                       " motifs with " + globalMotifSetDist[loc.id].size:string + " unique patterns");
    }
    
    // Print communication diagnostics for computation phase
    outMsg = "Communication statistics for motif enumeration:";
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
    printCommDiagnosticsTable();
    resetCommDiagnostics();
    
    // Start tracking communication for results collection
    startCommDiagnostics();
    
    // --- Efficiently merge results using WCC-style patterns ---
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(),
                     "Gathering and merging results from all locales");

    // First collect total motif counts and pattern counts
    var totalMotifCount: atomic int;
    var patternCounts: [localeDom] int;

    // Get counts from each locale
    coforall loc in Locales do on loc {
      // Add to total motif count
      totalMotifCount.add(globalMotifCountDist[loc.id].read());
      // Record number of unique patterns
      patternCounts[loc.id] = globalMotifSetDist[loc.id].size;
    }

    // Calculate offsets for pattern merging
    var patternOffsets: [0..numLocales] int;
    patternOffsets[0] = 0;
    for i in 1..numLocales {
      patternOffsets[i] = patternOffsets[i-1] + patternCounts[i-1];
    }

    // Allocate arrays on locale 0 for pattern data
    var totalPatterns = + reduce patternCounts;
    var globalPatterns: [0..<totalPatterns] (uint(64), int);

    // Merge pattern data from all locales using explicit ranges and aggregators
    coforall loc in Locales do on loc {
      // Create arrays of patterns and counts
      var localPatterns = globalMotifSetDist[loc.id].toArray();
      var localCounts: [localPatterns.domain] int;
      
      // Get counts for each pattern
      for i in localPatterns.domain {
        var pattern = localPatterns[i];
        var defaultCount: int = 0;
        localCounts[i] = globalMotifMapDist[loc.id].get(pattern, defaultCount);
      }
      
      // Define source and destination ranges
      var fromRange = 0..<localPatterns.size;
      var toRange = patternOffsets[loc.id]..<patternOffsets[loc.id] + localPatterns.size;
      
      // Transfer to locale 0 with aggregation
      on Locales[0] {
        for (i, j) in zip(fromRange, toRange) {
          globalPatterns[j] = (localPatterns[i], localCounts[i]);
        }
      }
    }

    // Process final results on locale 0
    var globalMotifSet: set(uint(64));
    var globalMotifMap: map(uint(64), int);
    
    on Locales[0] {
      // First, add all patterns to the set and initialize counts
      for (pattern, count) in globalPatterns {
        globalMotifSet.add(pattern);
        
        if !globalMotifMap.contains(pattern) {
          globalMotifMap.add(pattern, count);
        } else {
          // Add to existing count
          var currentCount = globalMotifMap.get(pattern, 0);
          globalMotifMap.addOrReplace(pattern, currentCount + count);
        }
      }
    }
    
    // Print communication diagnostics for result merging
    outMsg = "Communication statistics for merging results:";
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(), outMsg);
    printCommDiagnosticsTable();
    resetCommDiagnostics();
    
    // Write results to output file
    var outputPath:string = "./kavosh_results.txt";
    writeResultsToFile(outputPath, k, globalMotifSet, globalMotifMap, totalMotifCount.read(), n, mG1);
    
    startTime.stop();
    
    // Print final statistics
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(),
                     "Kavosh completed in " + startTime.elapsed():string + " seconds");
    siLogger_motif.info(getModuleName(), getRoutineName(), getLineNumber(),
                     "Found " + totalMotifCount.read():string + " motifs with " + 
                     globalMotifSet.size:string + " unique patterns");
                     
    // Create arrays for return values
    var patternCount = makeDistArray(2*2, int);
    patternCount[patternCount.domain.low] = globalMotifSet.size;       // Number of unique patterns after verification
    patternCount[patternCount.domain.low+1] = globalMotifSet.size;     // Before verification (same for now)
    patternCount[patternCount.domain.low+2] = totalMotifCount.read();  // Total motif count
    patternCount[patternCount.domain.low+3] = globalMotifMap.size;     // Number of unique patterns with counts
    
    // Prepare motif patterns array
    var motifPatterns: [0..<(globalMotifSet.size * k * k)] int = 0;
    var motifCounts: [0..<globalMotifSet.size] int = 0;
    var patternIdx = 0;
    
    for pattern in globalMotifSet {
      // Convert pattern to adjacency matrix
      var adjMatrix = patternToAdjMatrix(pattern, k);
      
      // Copy adjacency matrix to result array
      var startIdx = patternIdx * k * k;
      for i in 0..<(k * k) {
        motifPatterns[startIdx + i] = adjMatrix[i];
      }
      
      // Store count if available
      if globalMotifMap.contains(pattern) {
        motifCounts[patternIdx] = globalMotifMap.get(pattern, 0);
      }
      
      patternIdx += 1;
    }
    
    var tempArr: [0..<1] int;  // Empty array for placeholder
    
    return (patternCount, motifPatterns, motifCounts, tempArr);
  }
  
  /* Convert pattern (uint64) back to adjacency matrix */
  proc patternToAdjMatrix(pattern: uint(64), k: int) {
    var adjMatrix: [0..<(k * k)] int = 0;
    var pos = 0;
    
    for i in 0..<k {
      for j in 0..<k {
        if i != j {  // Skip self-loops
          if (pattern & (1:uint(64) << pos)) != 0 {
            adjMatrix[i * k + j] = 1;
          }
        }
        pos += 1;
      }
    }
    
    return adjMatrix;
  }
  
  /* Write results to a file */
  proc writeResultsToFile(outputPath: string, k: int, 
                        patterns: set(uint(64)), 
                        patternCounts: map(uint(64), int),
                        totalCount: int, n: int, m: int) throws {
    var outfile = open(outputPath, ioMode.cw);
    var writer = outfile.writer(locking=false);
    
    // Write header information
    writer.writeln("# Kavosh Motif Counting Results");
    writer.writeln("# Graph Size: " + n:string + " vertices, " + m:string + " edges");
    writer.writeln("# Motif Size (k): " + k:string);
    writer.writeln("# Total Motifs Found: " + totalCount:string);
    writer.writeln("# Unique Patterns: " + patterns.size:string);
    
    // Write vertex distribution across locales
    writer.writeln("# Vertex distribution across locales:");
    for loc in 0..<numLocales {
      var start = min(loc * ((n + numLocales - 1) / numLocales), n);
      var end = min((loc + 1) * ((n + numLocales - 1) / numLocales), n);
      writer.writeln("# Locale " + loc:string + ": " + (end-start):string + 
                     " vertices (" + start:string + " to " + (end-1):string + ")");
    }
    
    writer.writeln("# ");
    writer.writeln("# Format: PatternID Count CanonicalForm");
    writer.writeln();
    
    // Sort patterns by frequency
    var patternList: [1..patterns.size] (uint(64), int);
    var idx = 1;
    for pattern in patterns {
      var count = 0;
      if patternCounts.contains(pattern) {
        count = patternCounts.get(pattern, 0);
      }
      patternList[idx] = (pattern, count);
      idx += 1;
    }
    
    // Sort by frequency (highest first)
    //sort(patternList, comparator=new PatternComparator());
    
    // Write each pattern
    var patternId = 1;
    for (pattern, count) in patternList {
      writer.write(patternId, " ", count, " ");
      
      // Write canonical form as binary representation
      writer.write(pattern:string);
      
      // Also write as adjacency matrix for readability
      var adjMatrix = patternToAdjMatrix(pattern, k);
      writer.write(" [");
      for i in 0..<k {
        writer.write("[");
        for j in 0..<k-1 {
          writer.write(adjMatrix[i*k + j], ", ");
        }
        writer.write(adjMatrix[i*k + k-1], "]");
        if i < k-1 then writer.write(", ");
      }
      writer.writeln("]");
      
      patternId += 1;
    }
    
    writer.close();
    outfile.close();
  }
}