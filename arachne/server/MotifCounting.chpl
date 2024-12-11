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
    var pattern: list(int);   
    var motifCounts: map(string, atomic int);
    
    // Track memory usage
    var totalPatterns: atomic int = 0;
    var maxPatternSize: atomic int = 0;
    
    proc init(n: int, k: int) {
      if logLevel == LogLevel.DEBUG {
        writeln("Initializing KavoshState: n=", n, " k=", k);
      }
        this.n = n;
        this.k = k;
        this.visited = false;
        this.pattern = new list(int);
        this.motifCounts = new map(string, atomic int);

        this.pattern.pushBack(-1);  // TEST
        this.pattern.popBack();     

        if logLevel == LogLevel.DEBUG {
          writeln("Initialized KavoshState for graph with ", n, " vertices");
          writeln("Looking for motifs of size ", k);
          writeln("pattern after push and pop of -1 ", pattern);
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
        writeln("Processing pattern of size ", state.pattern.size);
        writeln("Current pattern: ", state.pattern);  // Add this
        writeln("Expected size: ", state.k);          // Add this
      }
      if state.pattern.size != state.k {
          writeln("Warning: Pattern size mismatch");
          return;
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
    * Core enumeration function that builds motif patterns according to specified depth.
    * Called by Kavosh() for each composition to build motifs.
    */
    proc enumeratePattern(v: int, pattern: list(int), depth: int, ref state: KavoshState) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("\n==== Starting enumeratePattern ====");
          writeln("Depth: ", depth, ", Vertices needed at this depth: ", pattern[depth]);
          writeln("Current pattern size: ", state.pattern.size);
          writeln("Target size: ", state.k);
          writeln("Processing vertex: ", v);
          writeln("Current pattern: ", state.pattern);
      }

      // Check if we've reached target size
      if state.pattern.size == state.k {
          if logLevel == LogLevel.DEBUG {
              writeln("Found complete pattern of size ", state.k);
          }
          processFoundMotif(state);
          return;
      }

      // Check if we've gone too far
      if depth >= pattern.size {
          if logLevel == LogLevel.DEBUG {
              writeln("Reached max depth without complete pattern");
          }
          return;
      }

      // Get neighbors using segment-based access for directed graph
      var inNeighbors = dstRG1[segRG1[v]..<segRG1[v+1]];      
      var outNeighbors = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

      if logLevel == LogLevel.DEBUG {
          writeln("  Found ", inNeighbors.size, " in-neighbors and ", outNeighbors.size, " out-neighbors");
      }

      // Build valid neighbor set respecting graph direction
      var validNbrs: domain(int, parSafe=true);
      
      // Process outgoing neighbors
      for nbr in outNeighbors {
          if !state.visited[nbr] {
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
          if logLevel == LogLevel.DEBUG {
              writeln("  About to generate combinations of size ", k);
          }

          var combinations = generateCombinations(validNbrs, k);

          if logLevel == LogLevel.DEBUG {
              writeln("  Generated combinations: ", combinations);
          }

          // Process each combination
          for combo in combinations {
              // Track vertices for backtracking
              var addedVertices: list(int);
              var initialSize = state.pattern.size;

              try {
                  // Add vertices in combination
                  for u in combo {
                      if !state.visited[u] {
                          state.pattern.pushBack(u);
                          state.visited[u] = true;
                          addedVertices.pushBack(u);
                          
                          if logLevel == LogLevel.DEBUG {
                              writeln("    Added vertex ", u);
                              writeln("    Current pattern: ", state.pattern);
                          }
                      } else {
                          if logLevel == LogLevel.DEBUG {
                              writeln("Warning: Attempted to add already visited vertex ", u);
                          }
                      }
                  }

                  // Only recurse if we added vertices successfully
                  if addedVertices.size == k {
                      // Process from each added vertex
                      for u in addedVertices {
                          enumeratePattern(u, pattern, depth + 1, state);
                          if stopper.read() then break;
                      }
                  } else {
                      if logLevel == LogLevel.DEBUG {
                          writeln("Warning: Failed to add all vertices in combination");
                      }
                  }

                  // Backtrack - remove added vertices
                  while state.pattern.size > initialSize {
                      var u = state.pattern.popBack();
                      state.visited[u] = false;
                      if logLevel == LogLevel.DEBUG {
                          writeln("    Removed vertex ", u);
                          writeln("    Pattern after removal: ", state.pattern);
                      }
                  }

              } catch e {
                  writeln("Error processing combination: ", e.message());
                  // Ensure cleanup
                  for u in addedVertices {
                      state.pattern.popBack();
                      state.visited[u] = false;
                  }
              }

              if logLevel == LogLevel.DEBUG {
                  writeln("    After processing combination: ", combo);
                  writeln("    Pattern size: ", state.pattern.size);
                  writeln("    Current pattern: ", state.pattern);
              }
          }
      }

      if logLevel == LogLevel.DEBUG {
          writeln("==== Completed enumeratePattern at depth ", depth, " ====");
          writeln("Final pattern: ", state.pattern);
      }

    }// End of enumeratePattern

    /* 
    * Validate vertex for next level processing.
    * Returns true if vertex is valid for the current pattern level.
    */

    proc validateVertex(v: int, level: int, const ref state: KavoshState): bool throws{
        if logLevel == LogLevel.DEBUG {
            writeln("Validating vertex ", v, " at level ", level);
        }

        // For first level (level 0), all unvisited vertices are valid
        if level == 0 {
            if logLevel == LogLevel.DEBUG {
                writeln("Level 0: returning true for unvisited vertex");
            }
            return !state.visited[v];
        }

        // Must have connection to at least one previous pattern vertex
        var hasConnection = false;
        for u in state.pattern {
            // Check both directions
            if getEdgeId(u, v, dstNodesG1, segGraphG1) != -1 || 
              getEdgeId(v, u, dstNodesG1, segGraphG1) != -1 {
                hasConnection = true;
                break;
            }
        }

        if logLevel == LogLevel.DEBUG {
            writeln("  Vertex ", v, " has connection to pattern: ", hasConnection);
            writeln("  Vertex ", v, " visited status: ", state.visited[v]);
        }

        return hasConnection && !state.visited[v];
    }// End of validateVertex

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


    /* Core Kavosh algorithm */
    proc Kavosh(n: int, k: int) throws {
      if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Kavosh ====");
      }

      var state = new KavoshState(n, k);
        
      // Process each vertex as root
      //forall v in 0..<n with (ref state) {
      for v in 0..<n {
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

    // Execute core algorithm
    var n = g1.n_vertices;
    var k = g2.n_vertices;
    
    var results = Kavosh(n, k);

    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Motif Finding Complete ====");
    }
    var tempArr: [0..0] int;
    var srcPerIso = makeDistArray(2*2, int);
    var dstPerIso = makeDistArray(2*2, int);
    return (srcPerIso, dstPerIso, tempArr, tempArr);
  }// End of runMotifCounting
}