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

/* Enhanced state tracking for level-based motif exploration */
class KavoshState {
    var n: int;                        // Number of vertices in graph
    var k: int;                        // Size of motifs to find
    var maxDegree: int;                // Maximum vertex degree in graph
    var visited: [0..<n] bool;         // Track visited vertices
    
    // Level-based organization
    var subgraph: [0..<k, 0..<k] int;  // Store vertices at each level [level, position]
    var levelSizes: [0..<k] int;       // Number of vertices at each level
    
    // Child set management (matching C++ implementation)
    var childSet: [0..<k, 0..<1000] int;    // Valid children at each level
    var childCount: [0..<k] int;            // Number of valid children per level
    var vertexIndex: [0..<k, 0..<1000] int; // Track vertex positions for swapping
    
    // Motif counting and statistics
    var motifCounts: map(string, atomic int);
    var seenPatterns: domain(string);       // Track unique patterns
    var totalPatterns: atomic int;          // Total patterns found
    var maxPatternSize: atomic int;         // Largest pattern size seen
    
    /* Initialize state */
    proc init(n: int, k: int, maxDeg: int) {
        if logLevel == LogLevel.DEBUG {
            writeln("Initializing KavoshState:");
            writeln("  Graph size (n) = ", n);
            writeln("  Motif size (k) = ", k);
            writeln("  Max degree = ", maxDeg);
        }
        
        this.n = n;
        this.k = k;
        this.maxDegree = maxDeg;
        this.visited = false;
        this.subgraph = -1;           // Initialize with invalid vertex values
        this.levelSizes = 0;
        this.childCount = 0;
        this.vertexIndex = -1;        // Initialize with invalid indices
        this.motifCounts = new map(string, atomic int);
        // this.seenPatterns = new domain(string);
    }
    
    /* Reset state for new root vertex */
    proc reset() {
        if logLevel == LogLevel.DEBUG {
            writeln("\nResetting KavoshState for new root vertex");
        }
        
        this.visited = false;
        this.subgraph = -1;
        this.levelSizes = 0;
        this.childCount = 0;
        this.vertexIndex = -1;
    }
    
    /* Add vertices to a specific level */
    proc addToLevel(level: int, vertices) {
        if logLevel == LogLevel.DEBUG {
            writeln("\nAdding vertices to level ", level);
            writeln("  Vertices to add: ", vertices);
        }

        // Handle different input types
        if vertices.type == int {
            // Single vertex case
            if logLevel == LogLevel.DEBUG {
                writeln("  Adding single vertex: ", vertices);
            }
            levelSizes[level] = 1;
            subgraph[level, 0] = vertices;
            visited[vertices] = true;
            
        } else {
            // Array case
            var count = vertices.size;
            if logLevel == LogLevel.DEBUG {
                writeln("  Adding ", count, " vertices");
            }
            
            levelSizes[level] = count;
            for (i, v) in zip(0..#count, vertices) {
                subgraph[level, i] = v;
                visited[v] = true;
            }
        }
        
        updateMemoryStats();
        
        if logLevel == LogLevel.DEBUG {
            writeln("  Level ", level, " now contains ", levelSizes[level], " vertices");
            write("  Current level contents: ");
            for i in 0..#levelSizes[level] do write(subgraph[level, i], " ");
            writeln();
        }
    }
    
    /* Remove vertices from a level */
    proc removeFromLevel(level: int) {
        if logLevel == LogLevel.DEBUG {
            writeln("\nRemoving vertices from level ", level);
            writeln("  Removing ", levelSizes[level], " vertices");
        }
        
        for i in 0..#levelSizes[level] {
            visited[subgraph[level, i]] = false;
            subgraph[level, i] = -1;
        }
        levelSizes[level] = 0;
        
        if logLevel == LogLevel.DEBUG {
            writeln("  Level ", level, " cleared");
        }
    }
    
    /* Track memory usage and pattern statistics */
    proc updateMemoryStats() {
        totalPatterns.add(1);
        var currentSize = + reduce levelSizes;
        var currentMax = maxPatternSize.read();
        if currentSize > currentMax {
            maxPatternSize.write(currentSize);
            if logLevel == LogLevel.DEBUG {
                writeln("\nNew maximum pattern size: ", currentSize);
            }
        }
    }
    
    /* Print current state - useful for debugging */
    proc printCurrentState() {
        if logLevel == LogLevel.DEBUG {
            writeln("\n==== Current KavoshState ====");
            writeln("Motif size (k): ", k);
            writeln("Total patterns found: ", totalPatterns.read());
            writeln("Maximum pattern size: ", maxPatternSize.read());
            writeln("Unique motifs found: ", motifCounts.size);
            writeln("\nLevel occupancy:");
            for level in 0..<k {
                if levelSizes[level] > 0 {
                    write("  Level ", level, ": ");
                    for pos in 0..#levelSizes[level] {
                        write(subgraph[level, pos], " ");
                    }
                    writeln();
                }
            }
            writeln("==========================\n");
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

/* Helper function to check if edge exists between vertices */
proc isEdge(u: int, v: int): bool {
    if logLevel == LogLevel.DEBUG {
        writeln("\n=== Checking edge (", u, ",", v, ") ===");
    }
    
    // Check forward edge
    var start = segGraphG1[u];
    var end = segGraphG1[u+1];
    
    for idx in start..<end {
        if dstNodesG1[idx] == v {
            if logLevel == LogLevel.DEBUG {
                writeln("Found forward edge");
            }
            return true;
        }
    }
    
    // Check reverse edge in reverse graph
    start = segRG1[u];
    end = segRG1[u+1];
    
    for idx in start..<end {
        if dstRG1[idx] == v {
            if logLevel == LogLevel.DEBUG {
                writeln("Found reverse edge");
            }
            return true;
        }
    }
    
    return false;
}

/* Generate canonical label for directed graphs using NAUTY-like approach */
proc generateCanonicalLabel(ref adjMatrix: [] bool): string throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n=== Generating Canonical Label ===");
    }

    var n = adjMatrix.domain.dim(0).size;
    var maxLabel: string = "";
    var bestPerm: [0..<n] int;
    var currentPerm: [0..<n] int;
    var visited: [0..<n] bool = false;
    
    // Calculate degrees for vertex ordering optimization
    var inDegrees: [0..<n] int;
    var outDegrees: [0..<n] int;
    
    if logLevel == LogLevel.DEBUG {
        writeln("Computing vertex degrees for graph of size ", n);
    }
    
    // Compute in/out degrees from adjacency matrix
    for i in 0..<n {
        for j in 0..<n {
            if adjMatrix[j,i] then inDegrees[i] += 1;
            if adjMatrix[i,j] then outDegrees[i] += 1;
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("In-degrees: ", inDegrees);
        writeln("Out-degrees: ", outDegrees);
    }
    
    /* Recursive permutation generation */
    proc tryPermutation(depth: int) throws {
        if depth == n {
            // Generate label for current permutation
            var labela: string;
            for i in 0..<n {
                for j in 0..<n {
                    labela += if adjMatrix[currentPerm[i], currentPerm[j]] then "1" else "0";
                }
            }
            
            if logLevel == LogLevel.DEBUG {
                writeln("Generated label for permutation: ", labela);
                write("Current permutation: ");
                for i in 0..<n do write(currentPerm[i], " ");
                writeln();
            }
            
            // Update if this is the maximal label
            if maxLabel == "" || labela > maxLabel {
                maxLabel = labela;
                bestPerm = currentPerm;
                
                if logLevel == LogLevel.DEBUG {
                    writeln("New maximal label found: ", maxLabel);
                }
            }
            return;
        }

        // Try each unvisited vertex, prioritizing by degree
        for idx in 0..<n {
            var i = idx; // Vertex selection order can be optimized here
            if !visited[i] {
                if logLevel == LogLevel.DEBUG {
                    writeln("Trying vertex ", i, " at depth ", depth);
                }
                
                visited[i] = true;
                currentPerm[depth] = i;
                tryPermutation(depth + 1);
                visited[i] = false;
            }
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Starting permutation generation");
    }
    
    // Generate all permutations and find canonical form
    tryPermutation(0);
    
    if logLevel == LogLevel.DEBUG {
        writeln("Final canonical label: ", maxLabel);
        write("Best permutation found: ");
        for i in 0..<n do write(bestPerm[i], " ");
        writeln("\n=== Canonical Label Generation Complete ===\n");
    }

    return maxLabel;
}
/* 
* Generate all possible compositions of integer n
* A composition of n is a way of writing n as a sum of positive integers
* The order matters: (1,2) and (2,1) are different compositions
* Each composition will determine how many vertices to select at each level
*/
proc generateCompositions(n: int): list(list(int)) {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Generating compositions for n=", n, " ====");
    }
    
    var compositions: list(list(int));

    // Handle invalid input
    if n <= 0 {
        if logLevel == LogLevel.DEBUG {
            writeln("Error: Cannot generate compositions for n <= 0");
        }
        return compositions;
    }

    /* Recursive helper to build compositions */
    proc compositionHelper(remaining: int, maxFirst: int, current: list(int)) {
        if logLevel == LogLevel.DEBUG {
            writeln("\nComposition state:");
            writeln("  Remaining: ", remaining);
            writeln("  Max first value: ", maxFirst);
            writeln("  Current composition: ", current);
        }

        // Base case: found valid composition
        if remaining == 0 {
            // Make deep copy of current composition
            var validComp = new list(int);
            for x in current do validComp.pushBack(x);
            
            if logLevel == LogLevel.DEBUG {
                writeln("  Found valid composition: ", validComp);
            }
            
            compositions.pushBack(validComp);
            return;
        }

        // Try each possible first number, up to min(maxFirst, remaining)
        for i in 1..min(maxFirst, remaining) {
            if logLevel == LogLevel.DEBUG {
                writeln("  Trying value ", i);
            }

            // Create next composition by extending current
            var next = new list(int);
            for x in current do next.pushBack(x);
            next.pushBack(i);
            
            if logLevel == LogLevel.DEBUG {
                writeln("  New partial composition: ", next);
            }

            // Recursive call with updated parameters
            compositionHelper(remaining-i, i, next);
        }
    }

    // Start with empty composition
    var initial = new list(int);
    compositionHelper(n, n, initial);

    if logLevel == LogLevel.DEBUG {
        writeln("\nFinal compositions generated:");
        writeln("Total count: ", compositions.size);
        writeln("Compositions: ", compositions);
        writeln("==== Composition Generation Complete ====\n");
    }

    return compositions;
}
/* Initialize valid child set - following C++ implementation exactly */
proc initChildSet(root: int, level: int, ref state: KavoshState) {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Initializing child set for level ", level, " ====");
        writeln("Processing from level ", level-1, " with size ", state.levelSizes[level-1]);
    }

    state.childCount[level] = 0;

    // Process vertices from previous level
    for i in 0..<state.levelSizes[level-1] {
        var parentVertex = state.subgraph[level-1, i];
        
        // Get outgoing + ingoing edges
        var inNeigs = dstRG1[segRG1[parentVertex]..<segRG1[parentVertex+1]];            
        var outNeigs = dstNodesG1[segGraphG1[parentVertex]..<segGraphG1[parentVertex+1]];
        
        var parentNeigs: domain(int, parSafe=true);
        
        parentNeigs += inNeigs;
        parentNeigs += outNeigs;

        for nbr in parentNeigs {
            // Only two conditions from C++ code:
            // 1. Not visited
            // 2. Greater than root
            if !state.visited[nbr] && nbr > root {
                state.childSet[level, state.childCount[level]] = nbr;
                state.childCount[level] += 1;
                
                if logLevel == LogLevel.DEBUG {
                    writeln("  Added neighbor ", nbr, " from parent ", parentVertex);
                }
            }
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Found ", state.childCount[level], " valid children");
        write("Child set: ");
        for i in 0..<state.childCount[level] {
            write(state.childSet[level, i], " ");
        }
        writeln();
    }
}

/*
* Main enumeration procedure that drives the motif finding process
* This implements the tree-based approach from the Kavosh paper
* Each vertex is considered as root, and patterns are built level by level
*/
proc enumerateMotifs(ref state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Motif Enumeration ====");
        writeln("Graph size: ", state.n);
        writeln("Motif size: ", state.k);
        writeln("Maximum degree: ", state.maxDegree);
    }

    // Process each vertex as potential root
    for v in 0..<state.n {
        if logLevel == LogLevel.DEBUG {
            writeln("\n---- Processing Root Vertex ", v, " ----");
        }
        
        // Reset state for new root
        state.reset();
        
        // Initialize first level with root vertex
        state.subgraph[0,0] = v;
        state.levelSizes[0] = 1;
        state.visited[v] = true;
        
        if logLevel == LogLevel.DEBUG {
            writeln("Initialized level 0 with vertex ", v);
        }

        // Generate compositions of k-1 (as we already used root vertex)
        var compositions = generateCompositions(state.k - 1);
        
        if logLevel == LogLevel.DEBUG {
            writeln("\nGenerated ", compositions.size, " compositions for k-1=", state.k-1);
            writeln("Compositions: ", compositions);
        }

        // Process each composition pattern
        for comp in compositions {
            if logLevel == LogLevel.DEBUG {
                writeln("\n>> Processing composition pattern: ", comp);
                writeln("Current state:");
                state.printCurrentState();
            }
            
            // Explore pattern starting from level 1
            explorePattern(v, 1, state.k - 1, comp, state);
        }

        // Cleanup root vertex
        state.visited[v] = false;
        
        if logLevel == LogLevel.DEBUG {
            writeln("\n---- Completed Root Vertex ", v, " ----");
            writeln("Current motif counts:");
            
            for pattern in state.motifCounts.keysToArray() {
                writeln("Pattern: ", pattern, " Count: ", state.motifCounts[pattern].read());
            }

        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Motif Enumeration Complete ====");
        writeln("Total patterns processed: ", state.totalPatterns.read());
        writeln("Unique motifs found: ", state.motifCounts.size);
    }
}

/* Tree building following paper's approach */
proc explorePattern(root: int, level: int, remainder: int, const ref comp: list(int), ref state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Exploring Pattern at Level ", level, " ====");
        writeln("Root: ", root, ", Level: ", level, ", Remainder: ", remainder);
    }

    // Base case: found complete pattern
    if remainder == 0 {
        processMotif(state);
        return;
    }

    // Get valid children
    initChildSet(root, level, state);
    var numChildren = state.childCount[level];
    var k = comp[level-1];  // Number of vertices to select at this level

    // Check if enough vertices available
    if numChildren < k {
        if logLevel == LogLevel.DEBUG {
            writeln("Insufficient vertices at level ", level);
        }
        return;
    }

    // Initial selection - first k vertices
    state.levelSizes[level] = k;
    for i in 0..<k {
        var v = state.childSet[level, i];
        state.subgraph[level, i] = v;
        state.vertexIndex[level, i] = i;
        state.visited[v] = true;
    }

    // Process initial selection
    explorePattern(root, level + 1, remainder - k, comp, state);

    // Generate other combinations using revolving door
    if k > 1 && numChildren > k {
        GEN(numChildren, k, root, level, remainder, comp, state);
    }

    // Cleanup this level - backtracking
    for i in 0..<k {
        state.visited[state.subgraph[level, i]] = false;
    }
    state.levelSizes[level] = 0;
}

/* Get valid children for the current level */
proc getValidChildren(root: int, level: int, ref state: KavoshState): int {
    if logLevel == LogLevel.DEBUG {
        writeln("\n=== Getting valid children for level ", level, " ===");
        writeln("Current vertex selections:");
        for i in 0..<level {
            if state.levelSizes[i] > 0 {
                write("  Level ", i, ": ");
                for j in 0..<state.levelSizes[i] {
                    write(state.subgraph[i,j], " ");
                }
                writeln();
            }
        }
    }

    var count = 0;
    
    // Get neighbors of vertices in previous level
    for i in 0..<state.levelSizes[level-1] {
        var v = state.subgraph[level-1,i];
        
        // Check outgoing edges
        var start = segGraphG1[v];
        var end = segGraphG1[v+1];
        
        for idx in start..<end {
            var nbr = dstNodesG1[idx];
            if !state.visited[nbr] && nbr > root {  // Maintain vertex ordering
                var isConnected = false;
                
                // Check connectivity with all previous levels
                for l in 0..<level {
                    for p in 0..<state.levelSizes[l] {
                        var u = state.subgraph[l,p];
                        if isEdge(u, nbr) || isEdge(nbr, u) {
                            isConnected = true;
                            break;
                        }
                    }
                    if isConnected then break;
                }
                
                if isConnected {
                    // Add to childSet if not already present
                    var isNew = true;
                    for j in 0..<count {
                        if state.childSet[level,j] == nbr {
                            isNew = false;
                            break;
                        }
                    }
                    if isNew {
                        state.childSet[level,count] = nbr;
                        count += 1;
                    }
                }
            }
        }
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Found ", count, " valid children");
        write("Valid children: { ");
        for i in 0..<count {
            write(state.childSet[level,i], " ");
        }
        writeln("}");
    }

    return count;
}




/* Implementation of backtracking as described in paper */
/* Enhanced revolving door swap with detailed debugging */
proc revolving_door_swap(i: int, j: int, root: int, level: int, remainder: int, k: int, const ref comp: list(int), ref state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Revolving Door Swap ====");
        writeln("  Level: ", level);
        writeln("  Swapping indices i=", i, " j=", j);
        writeln("  Before swap state:");
        state.printCurrentState();
        writeln("  Current selection at level ", level, ":");
        for x in 0..<state.levelSizes[level] {
            write(state.subgraph[level, x], " ");
        }
        writeln();
    }

    // Save current state for backtracking
    var oldVertex = state.subgraph[level, state.vertexIndex[level, i]];
    
    // Perform swap
    state.vertexIndex[level, i] = state.vertexIndex[level, j];
    var newVertex = state.childSet[level, i];
    
    // Update state
    state.subgraph[level, state.vertexIndex[level, i]] = newVertex;
    state.visited[oldVertex] = false;  // Unvisit old vertex
    state.visited[newVertex] = true;   // Visit new vertex

    if logLevel == LogLevel.DEBUG {
        writeln("  After swap:");
        writeln("  New vertex selection: ");
        for x in 0..<k do write(state.subgraph[level, x], " ");
        writeln("\n  Visiting vertex: ", newVertex);
        writeln("  Unvisiting vertex: ", oldVertex);
    }

    // Explore with new configuration
    explorePattern(root, level + 1, remainder - k, comp, state);

    // Restore state (backtrack)
    if logLevel == LogLevel.DEBUG {
        writeln("  Backtracking:");
        writeln("  Restoring vertex ", oldVertex, " at position ", state.vertexIndex[level, i]);
        writeln("  Unvisiting ", newVertex);
    }

    state.visited[newVertex] = false;
    state.visited[oldVertex] = true;
    state.subgraph[level, state.vertexIndex[level, i]] = oldVertex;

    if logLevel == LogLevel.DEBUG {
        writeln("  After backtrack state:");
        state.printCurrentState();
        writeln("==== End Revolving Door Swap ====\n");
    }
}

/* Generate combinations using revolving door ordering */
proc GEN(n: int, k: int, root: int, level: int, remainder: int, const ref comp: list(int), ref state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== GEN Call ====");
        writeln("  n=", n, " k=", k, " level=", level);
        writeln("  Current pattern state:");
        state.printCurrentState();
        writeln("  Current vertex selection at level ", level, ":");
        for i in 0..<state.levelSizes[level] {
            write(state.subgraph[level, i], " ");
        }
        writeln();
    }

    if k > 0 && k < n {
        if logLevel == LogLevel.DEBUG {
            writeln("  Making recursive GEN call with n-1=", n-1);
        }
        GEN(n-1, k, root, level, remainder, comp, state);

        if k == 1 {
            if logLevel == LogLevel.DEBUG {
                writeln("  k=1 case: swapping positions ", n, " and ", n-1);
            }
            revolving_door_swap(n, n-1, root, level, remainder, k, comp, state);
        } else {
            if logLevel == LogLevel.DEBUG {
                writeln("  k>1 case: swapping positions ", n, " and ", k-1);
            }
            revolving_door_swap(n, k-1, root, level, remainder, k, comp, state);
        }

        if logLevel == LogLevel.DEBUG {
            writeln("  Making NEG call with n-1=", n-1, " k-1=", k-1);
        }
        NEG(n-1, k-1, root, level, remainder, comp, state);
    }

    if logLevel == LogLevel.DEBUG {
        writeln("==== End GEN Call ====\n");
    }
}
/* Complementary function to GEN */
proc NEG(n: int, k: int, root: int, level: int, remainder: int, const ref comp: list(int), ref state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== NEG Call ====");
        writeln("  n=", n, " k=", k, " level=", level);
        writeln("  Current pattern state:");
        state.printCurrentState();
        writeln("  Current vertex selection at level ", level, ":");
        for i in 0..<state.levelSizes[level] {
            write(state.subgraph[level, i], " ");
        }
        writeln();
    }

    if k > 0 && k < n {
        if logLevel == LogLevel.DEBUG {
            writeln("  Making GEN call with n-1=", n-1, " k-1=", k-1);
        }
        GEN(n-1, k-1, root, level, remainder, comp, state);

        if k == 1 {
            if logLevel == LogLevel.DEBUG {
                writeln("  k=1 case: swapping positions ", n-1, " and ", n);
            }
            revolving_door_swap(n-1, n, root, level, remainder, k, comp, state);
        } else {
            if logLevel == LogLevel.DEBUG {
                writeln("  k>1 case: swapping positions ", k-1, " and ", n);
            }
            revolving_door_swap(k-1, n, root, level, remainder, k, comp, state);
        }

        if logLevel == LogLevel.DEBUG {
            writeln("  Making recursive NEG call with n-1=", n-1);
        }
        NEG(n-1, k, root, level, remainder, comp, state);
    }

    if logLevel == LogLevel.DEBUG {
        writeln("==== End NEG Call ====\n");
    }
}
/* Helper for checking edge existence with bidirectional support */
proc isConnected(u: int, v: int): bool throws{
    if logLevel == LogLevel.DEBUG {
        writeln("Checking connectivity between ", u, " and ", v);
    }

    // Check forward edge
    var eid1 = getEdgeId(u, v, dstNodesG1, segGraphG1);
    if eid1 != -1 then return true;
    
    // Check reverse edge
    var eid2 = getEdgeId(v, u, dstNodesG1, segGraphG1);
    return eid2 != -1;
}
/* Modified motif processing with orbit checking */
proc processMotif(ref state: KavoshState) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n=== Processing Motif Pattern ===");
        state.printCurrentState();
    }
    
    // Collect vertices in order
    var vertices: [0..<state.k] int;
    var idx = 0;
    for level in 0..<state.k {
        for pos in 0..<state.levelSizes[level] {
            vertices[idx] = state.subgraph[level,pos];
            idx += 1;
        }
    }
    
   // Build adjacency matrix - only outgoing edges
    var adjMatrix: [0..<state.k, 0..<state.k] bool;
    for i in 0..<state.k {
        var v = vertices[i];
        // Get only outgoing edges
        var start = segGraphG1[v];
        var end = segGraphG1[v+1];
        
        for edgeIdx in start..<end {
            var nbr = dstNodesG1[edgeIdx];
            // Find position of neighbor in vertices array
            for j in 0..<state.k {
                if vertices[j] == nbr {
                    adjMatrix[i,j] = true;
                    break;
                }
            }
        }
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Built adjacency matrix (directed edges only):");
        for i in 0..<state.k {
            for j in 0..<state.k {
                write(if adjMatrix[i,j] then "1" else "0", " ");
            }
            writeln();
        }
    }
    
    
    // Generate canonical label and update counts
    var canonLabel = generateCanonicalLabel(adjMatrix);
    if !state.seenPatterns.contains(canonLabel) {
        state.seenPatterns.add(canonLabel);
    }
    
    if !state.motifCounts.contains(canonLabel) {
        var newCount: atomic int;
        newCount.write(1);
        state.motifCounts[canonLabel] = newCount;
    } else {
        state.motifCounts[canonLabel].add(1);
    }
    
    state.updateMemoryStats();
    
    if logLevel == LogLevel.DEBUG {
        writeln("Generated canonical label: ", canonLabel);
        writeln("Updated count: ", state.motifCounts[canonLabel].read());
    }
}

    // Execute core algorithm
    var n = g1.n_vertices;
    var k = 3; // Oliver: This should be as an argument from Python side
    var maxDeg: int = 0; 
    var nodeDegree: [0..<n] int;

    forall v in 0..<n with(ref nodeDegree){
      var Tin = dstRG1[segRG1[v]..<segRG1[v+1]];
      var Tout = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
      nodeDegree[v] = Tin.size + Tout.size;
    }
    maxDeg = max reduce nodeDegree;

    if logLevel == LogLevel.DEBUG {
        writeln("Starting motif counting for k=", k);
        writeln("Graph has ", n, " vertices and ", srcNodesG1.size, " edges");
        writeln("Maximum degree: ", maxDeg);
    }

    var state = new KavoshState(n, k, maxDeg);
    // Run motif enumeration
    enumerateMotifs(state);
    
    if logLevel == LogLevel.DEBUG {
        writeln("\nMotif counting complete");
        writeln("Total patterns found: ", state.totalPatterns.read());
        writeln("Unique motifs found: ", state.motifCounts.size);
        
        var results = state.motifCounts;
        // Print motif statistics
        writeln("\nMotif frequencies:");
        for key in results.keysToArray(){
            writeln("Pattern: ", key, " Count: ", results[key].read());
        }

      
      writeln("Unique motifs found: ", results.size);
      writeln("\n==== Motif Finding Complete ====");

    }

    var tempArr: [0..0] int;
    var srcPerIso = makeDistArray(2*2, int);
    var dstPerIso = makeDistArray(2*2, int);
    return (srcPerIso, dstPerIso, tempArr, tempArr);
  }// End of runMotifCounting
}