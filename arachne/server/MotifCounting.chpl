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
    use Math;
    use BigInteger;

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
        var visited: domain(int, parSafe=true);

        // Convert 2D arrays to 1D
        // For subgraph: original was [0..<k, 0..<k+1]. remember it for Paper
        var subgraph: [0..#(k * (k+1))] int;  

        // For childSet: original was [0..<k, 0..(maxDeg*k)+1]
        var childSet: [0..#(k * ((maxDeg*k)+2))] int;

        // For indexMap: original was [0..<k, 0..(maxDeg*k)+1]
        var indexMap: [0..#(k * ((maxDeg*k)+2))] int;

        var localsubgraphCount: int;
    
        // A list to store vertex sets for each motif found
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
            this.localsubgraphCount = 0;
        this.motifVertices = new list(int, parSafe=true);

            // Initialize the new map
            //this.localClassCounts = new map(uint(64), int, parSafe=false);
        }
    }// End of KavoshState


    // C header and object files.
    require "nauty-wrapper/bin/nautyClassify.o",
            "nauty-wrapper/include/nautyClassify.h",
            "nauty-wrapper/bin/nauty.o",
            "nauty-wrapper/bin/nautil.o",
            "nauty-wrapper/bin/naugraph.o",
            "nauty-wrapper/bin/schreier.o",
            "nauty-wrapper/bin/naurng.o",
            "nauty-wrapper/bin/nausparse.o";

    // The function signature stays the same, just uses int64_t Don't change to POINTER!
    extern proc c_nautyClassify(
        subgraph: [] int(64), 
        subgraphSize: int(64), 
        results: [] int(64),
        performCheck: int(64),
        verbose: int(64),
        batchSize: int(64)

    ) : int(64);
  

    proc runMotifCounting(g1: SegGraph,  
              // sizeLimit: string, in timeLimit: int, in printProgressInterval: int,
               motifSize: int, doSampling: int, in printProgressInterval: int,
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
        
        // Setup the problem
        var n = nodeMapGraphG1.size;
        var k = motifSize; // Looking for motifs of size motifSize
        var nodeDegree: [0..<n] int;
        var node_IN_Neighbours: [0..<n] domain(int);
        var node_OUT_Neighbours: [0..<n] domain(int);
        var nodeNeighbours: [0..<n] domain(int);
        var newNodeNeighbours: [0..<n] domain(int);

        forall v in 0..<n with (ref nodeDegree) {
            var neighbours: domain(int, parSafe=true);

            const NeiIn = dstRG1[segRG1[v]..<segRG1[v+1]];
            const NeiOut = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

            neighbours += NeiIn;
            neighbours += NeiOut;

            nodeDegree[v] = neighbours.size;
            // Collect all neighbors (both in and out) 
            nodeNeighbours[v] = neighbours;
            node_IN_Neighbours[v] = NeiIn;
            node_OUT_Neighbours[v] = NeiOut;
        }

        var maxDeg = max reduce nodeDegree;

        // All motif counting and classify variables
        var globalMotifCount: atomic int;
        // var globalMotifSet: set(uint(64), parSafe=true);
        // Initiate it to 0
        globalMotifCount.write(0);
        // A global map to track pattern counts across all threads
        var globalMotifMap: map(uint(64), int);
        //var syncVar: sync bool;
    
        // Define a record for comparing tuples by the second element (degree)
        record DegreeComparator {
        proc compare(a: (int, int), b: (int, int)): int {
            // Sort in descending order of degree (second element)
            return b(1) - a(1);
        }
        }

        // Create an array of (node, degree) pairs
        var nodeDegPairs: [0..<n] (int, int);
        forall v in 0..<n {
            nodeDegPairs[v] = (v, nodeDegree[v]);
        }
        // Sort in descending order of degree
        sort(nodeDegPairs, comparator=new DegreeComparator());

            var globalMotifSet: set(uint(64), parSafe=true);
            var totalCount: atomic int;
        totalCount.write(0);




        var nautyCallCounter: atomic int;  // Track total number of calls to c_nautyClassify
        var totalMatricesProcessed: atomic int;  // Track total number of matrices processed
        var cacheHits: atomic int;  // Track number of matrices skipped due to caching
        // global set to track seen matrix binary representations
        var seenMatrices: set(uint(64), parSafe=true);

        var Sampling: bool = false;
        if doSampling == 1 then Sampling = true;
    
        var doMOtifDetail: bool = true;

        var newDstNodesG1 = dstNodesG1;
        var newSegGraphG1 = segGraphG1;
////////////////////////////////////////////////////////////////////////////////////////////////////////////
proc swapNodeWithZero(targetNode: int) {
    writeln("Swapping node ", targetNode, " with node 0");
    
    // 1. Swap the neighbor sets of nodes 0 and targetNode
    var temp_in = node_IN_Neighbours[0];
    var temp_out = node_OUT_Neighbours[0];
    var temp_all = nodeNeighbours[0];
    
    node_IN_Neighbours[0] = node_IN_Neighbours[targetNode];
    node_OUT_Neighbours[0] = node_OUT_Neighbours[targetNode];
    nodeNeighbours[0] = nodeNeighbours[targetNode];
    
    node_IN_Neighbours[targetNode] = temp_in;
    node_OUT_Neighbours[targetNode] = temp_out;
    nodeNeighbours[targetNode] = temp_all;
    
    // 2. Update references to 0 and targetNode in all neighbor sets
    forall v in 0..<nodeNeighbours.domain.size {
        // Create new neighbor sets with updated references
        var new_in: domain(int, parSafe=true);
        var new_out: domain(int, parSafe=true);
        var new_all: domain(int, parSafe=true);
        
        // Update incoming neighbors
        for neighbor in node_IN_Neighbours[v] {
            if neighbor == 0 {
                new_in.add(targetNode);
            } else if neighbor == targetNode {
                new_in.add(0);
            } else {
                new_in.add(neighbor);
            }
        }
        
        // Update outgoing neighbors
        for neighbor in node_OUT_Neighbours[v] {
            if neighbor == 0 {
                new_out.add(targetNode);
            } else if neighbor == targetNode {
                new_out.add(0);
            } else {
                new_out.add(neighbor);
            }
        }
        
        // Update all neighbors
        new_all += new_in;
        new_all += new_out;
        
        // Assign the updated sets
        node_IN_Neighbours[v] = new_in;
        node_OUT_Neighbours[v] = new_out;
        nodeNeighbours[v] = new_all;
        if logLevel == LogLevel.DEBUG {
            writeln("Node ", v, " has In-Nei: ", node_IN_Neighbours[v], "Out-Nei: ", node_OUT_Neighbours[v] );
        }
    }
    
    // For verification
    writeln("After swap - node 0 neighbors: ", nodeNeighbours[0]);
    writeln("After swap - node ", targetNode, " neighbors: ", nodeNeighbours[targetNode]);
    
    return;
}
    // Run the swap 
    //swapNodeWithZero(doSampling); 
    
// Modified version of initChildSet that accepts the graph arrays as parameters
proc initChildSetSwapped(ref state: KavoshState, root: int, level: int, targetNode: int) throws {
    // Initialize count for this level to 0
    state.setChildSet(level, 0, 0);
    const parentsCount = state.getSubgraph(level-1, 0);

    // For each vertex chosen at the previous level, get its neighbors
    for p in 1..parentsCount {
        const parent = state.getSubgraph(level-1, p);
        
        // Get neighbors (they're already correctly swapped by swapNodeWithZero)
        for neighbor in nodeNeighbours[parent] {
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
    // Similar to original Explore but using swapped-aware helper functions
proc ExploreSwapped(ref state: KavoshState, root: int, level: int, remainedToVisit: int, targetNode:int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("===== ExploreSwapped called =====");
        writeln("Current root: ", root, " level: ", level, " remainedToVisit: ", remainedToVisit);
        writeln("Visited Vertices: ", state.visited);
        writeln("Current partial subgraph level by level:");
        for l in 0..<level {
            write("Level ", l, " (count=", state.getSubgraph(l, 0), "): ");
            for x in 1..state.getSubgraph(l, 0) {
                write(state.getSubgraph(l, x), " ");
            }
            writeln();
        }
        writeln("==========================");
    }

    // Base case: all k vertices chosen, now we have found a motif
    if remainedToVisit == 0 {
        // Base case: all k vertices chosen, we found a motif
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
        state.localsubgraphCount += 1;
        return;
    }

    // Get children for this level, using swap-aware function
    initChildSetSwapped(state, root, level, targetNode);
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
        ExploreSwapped(state, root, level+1, remainedToVisit - selSize, targetNode);

        // Generate other combinations using revolve-door algorithm
        ForwardGeneratorSwapped(childCount, selSize, root, level, remainedToVisit, selSize, state, targetNode);
    }

    // Cleanup: Unmark visited children
    for i in 1..childCount {
        state.visited.remove(state.getChildSet(level, i));
    }
    state.setSubgraph(level, 0, 0);
}

proc ForwardGeneratorSwapped(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, 
                            ref state: KavoshState, targetNode: int) throws {
    if k > 0 && k < n {
        ForwardGeneratorSwapped(n-1, k, root, level, remainedToVisit, m, state, targetNode);

        if k == 1 {
            swappingFunction(n, n-1, root, level, remainedToVisit, m, state, targetNode);
        } else {
            swappingFunction(n, k-1, root, level, remainedToVisit, m, state, targetNode);
        }

        reverseGeneratorSwapped(n-1, k-1, root, level, remainedToVisit, m, state, targetNode);
    }
}

proc reverseGeneratorSwapped(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, 
                           ref state: KavoshState, targetNode: int) throws {
    if k > 0 && k < n {
        ForwardGeneratorSwapped(n-1, k-1, root, level, remainedToVisit, m, state, targetNode);

        if k == 1 {
            swappingFunction(n-1, n, root, level, remainedToVisit, m, state, targetNode);
        } else {
            swappingFunction(k-1, n, root, level, remainedToVisit, m, state, targetNode);
        }

        reverseGeneratorSwapped(n-1, k, root, level, remainedToVisit, m, state, targetNode);
    }
}

proc swappingFunction(i: int, j: int, root: int, level: int, remainedToVisit: int, m: int, 
                     ref state: KavoshState, targetNode: int) throws {
    state.setIndexMap(level, i, state.getIndexMap(level, j));
    state.setSubgraph(level, state.getIndexMap(level, i), state.getChildSet(level, i));

    ExploreSwapped(state, root, level+1, remainedToVisit - m, targetNode);
}

// Function to check if an edge exists between u and w in the swapped graph
proc getEdgeIdSwapped(u: int, w: int, targetNode: int) throws{
    // Map nodes if they're 0 or targetNode
    var actualU = u;
    var actualW = w;
    
    if u == 0 {
        actualU = targetNode;
    } else if u == targetNode {
        actualU = 0;
    }
    
    if w == 0 {
        actualW = targetNode;
    } else if w == targetNode {
        actualW = 0;
    }
    
    // Now check with the mapped nodes
    return getEdgeId(actualU, actualW, dstNodesG1, segGraphG1);
}
// Modified version of prepareNaugtyArguments to handle swapped nodes
proc prepareNaugtyArgumentsSwapped(ref state: KavoshState, targetNode: int) throws {
    // Step 1: Build array of chosen vertices
    var chosenVerts: [1..state.k] int;
    var idx = 1;
    
    // Gather vertices level by level
    for level in 0..<state.k {
        const vertCount = state.getSubgraph(level, 0);
        for pos in 1..vertCount {
            if idx > state.k {
                halt("Error: More vertices than expected");
            }
            chosenVerts[idx] = state.getSubgraph(level, pos);
            idx += 1;
        }
    }

    if idx - 1 != state.k {
        halt("Error: Didn't find exactly k vertices");
    }

    // Step 2: Create adjacency matrix
    var adjMatrix: [0..#(state.k * state.k)] int = 0;

    // Step 3: Fill adjacency matrix
    for i in 0..#state.k {
        for j in 0..#state.k {
            if i != j {  // Skip self-loops
                var u = chosenVerts[i+1];
                var w = chosenVerts[j+1];
                
                // Use the swapped-aware edge check
                var eid = getEdgeIdSwapped(u, w, targetNode);
                if eid != -1 {
                    adjMatrix[i * state.k + j] = 1;
                }
            }
        }
    }

    return (adjMatrix, chosenVerts);
}

// Main function to run Kavosh for a specific node
proc EnumerateForNode(originalTargetNode: int, n: int, k: int, maxDeg: int) throws {
    writeln("===== Running Kavosh for node ", originalTargetNode, " =====");

    // Create state for tracking results
    var state = new KavoshState(n, k, maxDeg);

    state.setSubgraph(0, 0, 1);
    state.setSubgraph(0, 1, 0);
    state.visited.clear();
    state.visited.add(0);

    if originalTargetNode == 0 {        // If target is already 0, run Kavosh normally
        // Run Explore directly
        Explore(state, 0, 1, state.k - 1);
        writeln("Ran normal Explore for root 0");
    } else { // Run with 0 as root (representing the original target node)
        // Swap the target node with 0
        swapNodeWithZero(originalTargetNode);
        
        // Run Explore with swapped graph
        ExploreSwapped(state, 0, 1, state.k - 1, originalTargetNode);
    }
    
    // Process motifs exactly like in Enumerate
    const numMotifs = state.localsubgraphCount;
    const totalVertices = state.motifVertices.size;
    
    writeln("Found ", numMotifs, " motifs with a total of ", totalVertices, " vertices");
    
    // Skip if no motifs found
    if numMotifs == 0 || totalVertices == 0 {
        writeln("No motifs found. Skipping pattern processing.");
        return;
    }
    
    // Map to track canonical patterns and their counts
    var canonicalPatternMap: map(uint(64), int);
    
    // Get the motif vertices as an array
    var motifVerticesArray = state.motifVertices.toArray();

    if logLevel == LogLevel.DEBUG {

        writeln("Motif vertex sets:");
        for i in 0..<numMotifs {
            var baseIdx = i * k;
            write("  Motif ", i, ": ");
            for j in 0..<k {
                write(motifVerticesArray[baseIdx + j], " ");
            }
            writeln();
        }
    }
    // Create arrays for batch processing
    var batchedMatrices: [0..#(numMotifs * k * k)] int = 0;
    var batchedResults: [0..#(numMotifs * k)] int;
    
    // Track which matrices need to be processed
    var matricesToProcess: list((int, uint(64)));  // (index, binary) pairs for new matrices
    var seenIndices: domain(int, parSafe=false);  // Indices of matrices we've seen before
    var patternToOriginalMapping: map(uint(64), list(uint(64))); // Map to track original patterns per canonical form
    
    if logLevel == LogLevel.DEBUG {
        writeln("\nProcessing ", numMotifs, " motifs for pattern identification...");
    }
    // Fill matrices and check for duplicates
    for i in 0..<numMotifs {
        var baseIdx = i * k;
        var matrixBinary: uint(64) = 0;  // Binary representation for this matrix
        
        // Create adjacency matrix
        for row in 0..<k {
            for col in 0..<k {
                if row != col {  // Skip self-loops
                    var u = motifVerticesArray[baseIdx + row];
                    var w = motifVerticesArray[baseIdx + col];
                    
                    // Use the appropriate edge checking function
                    var eid;
                    if originalTargetNode == 0 {
                        eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                    } else {
                        eid = getEdgeIdSwapped(u, w, originalTargetNode);
                    }
                    
                    if eid != -1 {
                        batchedMatrices[i * (k * k) + row * k + col] = 1;
                        
                        // Update binary representation - set bit at position (row * k + col)
                        matrixBinary |= 1:uint(64) << (row * k + col);
                    }
                }
            }
        }
        
        if logLevel == LogLevel.DEBUG {
            writeln("  Motif ", i, " matrix binary: ", matrixBinary);

            // Visualize the adjacency matrix for this motif
            writeln("  Adjacency matrix for motif ", i, ":");
            for row in 0..<k {
                write("    ");
                for col in 0..<k {
                    write(batchedMatrices[i * (k * k) + row * k + col], " ");
                }
                writeln();
            }
        }
        // Check if we've seen this matrix before
        if seenMatrices.contains(matrixBinary) {
            // We've seen this pattern before, skip Nauty processing
            seenIndices.add(i);
            //writeln("  Matrix binary ", matrixBinary, " already seen - skipping Nauty");
        } else {
            // New pattern, add to seen matrices and process
            seenMatrices.add(matrixBinary);
            matricesToProcess.pushBack((i, matrixBinary));
            //writeln("  New matrix binary ", matrixBinary, " - will be processed by Nauty");
        }
    }

    //writeln("\nFound ", matricesToProcess.size, " unique matrices to process with Nauty");
    
    // Process only unseen matrices with Nauty
    if matricesToProcess.size > 0 {
        // Create smaller batch arrays for just the unseen matrices
        var uniqueCount = matricesToProcess.size;
        var uniqueMatrices: [0..#(uniqueCount * k * k)] int = 0;
        var uniqueResults: [0..#(uniqueCount * k)] int;
        
        // Fill unique matrices array
        for i in 0..<uniqueCount {
            var (origIdx, binary) = matricesToProcess[i];
            var origOffset = origIdx * (k * k);
            var newOffset = i * (k * k);
            
            // Copy matrix from original batch to unique batch
            for j in 0..<(k * k) {
                uniqueMatrices[newOffset + j] = batchedMatrices[origOffset + j];
            }
            
            //writeln("  Processing matrix ", i, " (original index ", origIdx, ") with binary ", binary);
        }
        
        // Process only unique matrices with Nauty
        var status = c_nautyClassify(uniqueMatrices, k, uniqueResults, 1, 0, uniqueCount);
        if logLevel == LogLevel.DEBUG {
            writeln("  Nauty processing complete with status: ", status);
            writeln("uniqueResults: ", uniqueResults);
            writeln("uniqueMatrices: ", uniqueMatrices);
            writeln("------------------------------------------------------");
        }
        
        // Copy results back to original results array
        for i in 0..<uniqueCount {
            var (origIdx, originalBinary) = matricesToProcess[i];
            var origOffset = origIdx * k;
            var newOffset = i * k;
            
            // Copy results
            for j in 0..<k {
                batchedResults[origOffset + j] = uniqueResults[newOffset + j];
            }
            
            // Extract nauty results for this matrix
            var nautyLabels: [0..<k] int;
            for j in 0..<k {
                nautyLabels[j] = uniqueResults[newOffset + j];
            }
            
            // Get adjacency matrix for this motif
            var adjMatrixStart = origIdx * (k * k);
            var adjMatrix: [0..#(k*k)] int;
            for j in 0..#(k*k) {
                adjMatrix[j] = batchedMatrices[adjMatrixStart + j];
            }
            
            // Generate canonical pattern using the consistent approach
            var canonicalPattern = generateNautyPattern(adjMatrix, nautyLabels, k);
            
            // Add mapping from original binary to canonical pattern
            if !patternToOriginalMapping.contains(canonicalPattern) {
                patternToOriginalMapping[canonicalPattern] = new list(uint(64));
            }
            patternToOriginalMapping[canonicalPattern].pushBack(originalBinary);
            
            if logLevel == LogLevel.DEBUG {
                writeln("  Matrix ", i, " (original index ", origIdx, ") with binary ", originalBinary);
                writeln("    is mapped to canonical pattern: ", canonicalPattern);
                write("    with nauty labels: ");
                for j in 0..<k {
                    write(nautyLabels[j], " ");
                }
                writeln();
            }
        }
    }

    // Count motifs for each canonical pattern
    for i in 0..<numMotifs {
        // Get the binary representation for this motif
        var matrixBinary: uint(64) = 0;
        var baseIdx = i * k;
        for row in 0..<k {
            for col in 0..<k {
                if row != col && batchedMatrices[i * (k * k) + row * k + col] == 1 {
                    matrixBinary |= 1:uint(64) << (row * k + col);
                }
            }
        }
        
        // If we've seen this exact matrix before, we need to find its canonical form
        var canonicalPattern: uint(64);
        if seenIndices.contains(i) {
            // Find which canonical pattern this binary maps to
            var found = false;
            for canonKey in patternToOriginalMapping.keys() {
                var originals = patternToOriginalMapping[canonKey];
                for original in originals {
                    if original == matrixBinary {
                        canonicalPattern = canonKey;
                        found = true;
                        break;
                    }
                }
                if found then break;
            }
        } else {
            // Get adjacency matrix for this motif
            var adjMatrixStart = i * (k * k);
            var adjMatrix: [0..#(k*k)] int;
            for j in 0..#(k*k) {
                adjMatrix[j] = batchedMatrices[adjMatrixStart + j];
            }
            
            // Extract nauty results for this matrix
            var nautyLabels: [0..<k] int;
            for j in 0..<k {
                nautyLabels[j] = batchedResults[i * k + j];
            }
            
            // Generate canonical pattern using the consistent approach
            canonicalPattern = generateNautyPattern(adjMatrix, nautyLabels, k);
        }
        
        // Update counts for this canonical pattern
        if !canonicalPatternMap.contains(canonicalPattern) {
            canonicalPatternMap[canonicalPattern] = 0;
        }
        canonicalPatternMap[canonicalPattern] += 1;
        
        // Also track the total count
        totalCount.add(1);
    }

    // Add canonical patterns to the global set
    for pattern in canonicalPatternMap.keys() {
        globalMotifSet.add(pattern);
        if !globalMotifMap.contains(pattern) {
            globalMotifMap[pattern] = 0;
        }
        globalMotifMap[pattern] += canonicalPatternMap[pattern];
    }
    
    // Print detailed pattern information
    writeln("\nPattern summary for node ", originalTargetNode, ":");
    writeln("  Total motifs found: ", numMotifs);
    writeln("  Unique canonical patterns: ", canonicalPatternMap.size);
    
    if canonicalPatternMap.size > 0 {
        writeln("\nPattern details:");
        var patternList: [1..canonicalPatternMap.size] (uint(64), int);
        var idx = 1;
        for pattern in canonicalPatternMap.keys() {
            patternList[idx] = (pattern, canonicalPatternMap[pattern]);
            idx += 1;
        }
        
        // Sort by frequency (highest first)
        sort(patternList, comparator=new PatternComparator());
        
        for (pattern, count) in patternList {
            writeln("  Canonical pattern ", pattern, ": ", count, " occurrences");
            
            // Show which original pattern(s) mapped to this canonical form
            if patternToOriginalMapping.contains(pattern) {
                write("    Original patterns: ");
                var first = true;
                for original in patternToOriginalMapping[pattern] {
                    if !first then write(", ");
                    write(original);
                    first = false;
                }
                writeln();
            }
        }
    }
    
    writeln("\nRunning totals:");
    writeln("  Global unique canonical patterns: ", globalMotifSet.size);
    writeln("  Global motif count: ", totalCount.read());
    writeln("====================================\n");
    
    // Set the final global count
    globalMotifCount.write(totalCount.read());
}


// Comparator for sorting patterns by frequency
record PatternComparator {
    proc compare(a: (uint(64), int), b: (uint(64), int)): int {
        // Sort by count (descending)
        if a(1):int != b(1):int then
            return b(1):int - a(1):int;
        // Break ties by pattern ID
        return a(0):int - b(0):int;
    }

}

// Helper function to access the correct neighbor set (local or global)
proc getNodeNeighbours(nodeIdx: int, ref isModified: [] bool, ref local_nodeNeighbours: [] domain(int)) {
    if isModified[nodeIdx] {
        return local_nodeNeighbours[nodeIdx];
    } else {
        return nodeNeighbours[nodeIdx];
    }
}

proc getNodeInNeighbours(nodeIdx: int, ref isModified: [] bool, ref local_node_IN_Neighbours: [] domain(int)) {
    if isModified[nodeIdx] {
        return local_node_IN_Neighbours[nodeIdx];
    } else {
        return node_IN_Neighbours[nodeIdx];
    }
}

proc getNodeOutNeighbours(nodeIdx: int, ref isModified: [] bool, ref local_node_OUT_Neighbours: [] domain(int)) {
    if isModified[nodeIdx] {
        return local_node_OUT_Neighbours[nodeIdx];
    } else {
        return node_OUT_Neighbours[nodeIdx];
    }
}

// Modified version of initChildSet that uses the local neighbor access functions
proc localInitChildSet(ref state: KavoshState, root: int, level: int, 
                      ref isModified: [] bool, 
                      ref local_nodeNeighbours: [] domain(int)) throws {
    // Initialize count for this level to 0
    state.setChildSet(level, 0, 0);
    const parentsCount = state.getSubgraph(level-1, 0);
    
    // For each vertex chosen at the previous level, get its neighbors
    for p in 1..parentsCount {
        const parent = state.getSubgraph(level-1, p);
        
        for neighbor in getNodeNeighbours(parent, isModified, local_nodeNeighbours) {
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
    
    if logLevel == LogLevel.DEBUG {
        writeln("localInitChildSet: Found ", state.getChildSet(level, 0), " valid children at level ", level);
        write("Children: ");
        for i in 1..state.getChildSet(level, 0) {
            write(state.getChildSet(level, i), " ");
        }
        writeln();
    }
}

// Helper function to check edge existence using the thread-local neighbor info
proc localGetEdgeId(u: int, w: int, 
                   ref isModified: [] bool, 
                   ref local_node_OUT_Neighbours: [] domain(int)) throws {
    // Check if there's an edge from u to w
    var uNeighbors = getNodeOutNeighbours(u, isModified, local_node_OUT_Neighbours);
    
    for neighbor in uNeighbors {
        if neighbor == w {
            // Edge exists, return positive value
            return 1;  
        }
    }
    
    return -1;  // No edge found
}

// Modified version of Explore that uses the local neighbor access
proc localExplore(ref state: KavoshState, root: int, level: int, remainedToVisit: int,
                 ref isModified: [] bool,
                 ref local_nodeNeighbours: [] domain(int),
                 ref local_node_IN_Neighbours: [] domain(int),
                 ref local_node_OUT_Neighbours: [] domain(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("===== localExplore called =====");
        writeln("Current root: ", root, " level: ", level, " remainedToVisit: ", remainedToVisit);
        writeln("Visited Vertices: ", state.visited);
        writeln("Current partial subgraph level by level:");
        for l in 0..<level {
            write("Level ", l, " (count=", state.getSubgraph(l, 0), "): ");
            for x in 1..state.getSubgraph(l, 0) {
                write(state.getSubgraph(l, x), " ");
            }
            writeln();
        }
        writeln("==========================");
    }
    
    // Base case: all k vertices chosen, now we have found a motif
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
        state.localsubgraphCount += 1;
        
        return;
    }
    
    // Get children for this level using the thread-local neighbor access
    localInitChildSet(state, root, level, isModified, local_nodeNeighbours);
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
        localExplore(state, root, level+1, remainedToVisit - selSize, isModified, 
                    local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
        
        // Generate other combinations using revolve-door algorithm
        localForwardGenerator(childCount, selSize, root, level, remainedToVisit, selSize, state, 
                             isModified, local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
    }
    
    // Cleanup: Unmark visited children
    for i in 1..childCount {
        state.visited.remove(state.getChildSet(level, i));
    }
    state.setSubgraph(level, 0, 0);
}

// Modified swapping function for the thread-local processing
proc localSwapping(i: int, j: int, root: int, level: int, remainedToVisit: int, m: int, 
                  ref state: KavoshState,
                  ref isModified: [] bool,
                  ref local_nodeNeighbours: [] domain(int),
                  ref local_node_IN_Neighbours: [] domain(int),
                  ref local_node_OUT_Neighbours: [] domain(int)) throws {
    state.setIndexMap(level, i, state.getIndexMap(level, j));
    state.setSubgraph(level, state.getIndexMap(level, i), state.getChildSet(level, i));
    
    localExplore(state, root, level+1, remainedToVisit - m, isModified, 
                local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
}

// Modified ForwardGenerator for thread-local processing
proc localForwardGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, 
                          ref state: KavoshState,
                          ref isModified: [] bool,
                          ref local_nodeNeighbours: [] domain(int),
                          ref local_node_IN_Neighbours: [] domain(int),
                          ref local_node_OUT_Neighbours: [] domain(int)) throws {
    if k > 0 && k < n {
        localForwardGenerator(n-1, k, root, level, remainedToVisit, m, state, isModified, 
                             local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
        
        if k == 1 {
            localSwapping(n, n-1, root, level, remainedToVisit, m, state, isModified, 
                         local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
        } else {
            localSwapping(n, k-1, root, level, remainedToVisit, m, state, isModified, 
                         local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
        }
        
        localReverseGenerator(n-1, k-1, root, level, remainedToVisit, m, state, isModified, 
                             local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
    }
}

// Modified ReverseGenerator for thread-local processing
proc localReverseGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, 
                          ref state: KavoshState,
                          ref isModified: [] bool,
                          ref local_nodeNeighbours: [] domain(int),
                          ref local_node_IN_Neighbours: [] domain(int),
                          ref local_node_OUT_Neighbours: [] domain(int)) throws {
    if k > 0 && k < n {
        localForwardGenerator(n-1, k-1, root, level, remainedToVisit, m, state, isModified, 
                             local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
        
        if k == 1 {
            localSwapping(n-1, n, root, level, remainedToVisit, m, state, isModified, 
                         local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
        } else {
            localSwapping(k-1, n, root, level, remainedToVisit, m, state, isModified, 
                         local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
        }
        
        localReverseGenerator(n-1, k, root, level, remainedToVisit, m, state, isModified, 
                             local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
    }
}

// New function to process multiple nodes in parallel
proc EnumerateForMultipleNodes(targetNodes: [] int, n: int, k: int, maxDeg: int) throws {
    // Process each node in parallel
    forall targetNode in targetNodes with (ref globalMotifSet, ref globalMotifMap, ref totalCount) {
        writeln("===== Processing node ", targetNode, " =====");
        
        // Create thread-local copies of the neighbor data structures that will be modified
        var local_node_IN_Neighbours: [0..<n] domain(int);
        var local_node_OUT_Neighbours: [0..<n] domain(int);
        var local_nodeNeighbours: [0..<n] domain(int);
        
        // Flag array to track which nodes have modified neighbor lists
        var isModified: [0..<n] bool = false;
        
        // Initialize with empty domains
        for i in 0..<n {
            local_node_IN_Neighbours[i] = {1..0}; // Empty domain
            local_node_OUT_Neighbours[i] = {1..0}; // Empty domain
            local_nodeNeighbours[i] = {1..0}; // Empty domain
        }
        
        // Only swap node if targetNode is not 0
        if targetNode != 0 {
            // Copy the neighbor sets for nodes 0 and targetNode
            local_node_IN_Neighbours[0] = node_IN_Neighbours[targetNode];
            local_node_OUT_Neighbours[0] = node_OUT_Neighbours[targetNode];
            local_nodeNeighbours[0] = nodeNeighbours[targetNode];
            
            local_node_IN_Neighbours[targetNode] = node_IN_Neighbours[0];
            local_node_OUT_Neighbours[targetNode] = node_OUT_Neighbours[0];
            local_nodeNeighbours[targetNode] = nodeNeighbours[0];
            
            // Mark these nodes as modified
            isModified[0] = true;
            isModified[targetNode] = true;
            
            // For all other nodes, we need to update references to 0 and targetNode
            for v in 0..<n {
                if v == 0 || v == targetNode {
                    continue; // Already handled above
                }
                
                // Check if this node has 0 or targetNode as a neighbor
                var hasReferencesToSwappedNodes = false;
                for neighbor in nodeNeighbours[v] {
                    if neighbor == 0 || neighbor == targetNode {
                        hasReferencesToSwappedNodes = true;
                        break;
                    }
                }
                
                // Only modify nodes that reference 0 or targetNode
                if hasReferencesToSwappedNodes {
                    var new_in: domain(int, parSafe=true);
                    var new_out: domain(int, parSafe=true);
                    var new_all: domain(int, parSafe=true);
                    
                    // Update incoming neighbors
                    for neighbor in node_IN_Neighbours[v] {
                        if neighbor == 0 {
                            new_in.add(targetNode);
                        } else if neighbor == targetNode {
                            new_in.add(0);
                        } else {
                            new_in.add(neighbor);
                        }
                    }
                    
                    // Update outgoing neighbors
                    for neighbor in node_OUT_Neighbours[v] {
                        if neighbor == 0 {
                            new_out.add(targetNode);
                        } else if neighbor == targetNode {
                            new_out.add(0);
                        } else {
                            new_out.add(neighbor);
                        }
                    }
                    
                    // Update all neighbors
                    new_all += new_in;
                    new_all += new_out;
                    
                    // Store in local copies
                    local_node_IN_Neighbours[v] = new_in;
                    local_node_OUT_Neighbours[v] = new_out;
                    local_nodeNeighbours[v] = new_all;
                    
                    // Mark as modified
                    isModified[v] = true;
                    
                    if logLevel == LogLevel.DEBUG {
                        writeln("Node ", v, " has modified In-Nei: ", local_node_IN_Neighbours[v], "Out-Nei: ", local_node_OUT_Neighbours[v]);
                    }
                }
            }
            
            if logLevel == LogLevel.DEBUG {
                writeln("After local swap - node 0 neighbors: ", local_nodeNeighbours[0]);
                writeln("After local swap - node ", targetNode, " neighbors: ", local_nodeNeighbours[targetNode]);
            }
        }
        
        // Create state for tracking results
        var state = new KavoshState(n, k, maxDeg);
        
        // Initialize with root 0 (which may represent our target node after swapping)
        state.setSubgraph(0, 0, 1);
        state.setSubgraph(0, 1, 0);
        state.visited.clear();
        state.visited.add(0);
        
        // Run the local Explore function with the thread-local neighbor data
        localExplore(state, 0, 1, state.k - 1, isModified, 
                    local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
        
        // Process the motifs found
        const numMotifs = state.localsubgraphCount;
        const totalVertices = state.motifVertices.size;
        
        writeln("Found ", numMotifs, " motifs for node ", targetNode);
        
        // Skip if no motifs found
        if numMotifs == 0 || totalVertices == 0 {
            writeln("No motifs found for node ", targetNode, ". Skipping pattern processing.");
            continue;
        }
        
        // Thread-local map to track canonical patterns and their counts
        var canonicalPatternMap: map(uint(64), int);
        
        // Get the motif vertices as an array
        var motifVerticesArray = state.motifVertices.toArray();
        
        // Create arrays for batch processing
        var batchedMatrices: [0..#(numMotifs * k * k)] int = 0;
        var batchedResults: [0..#(numMotifs * k)] int;
        
        // Track which matrices need to be processed
        var matricesToProcess: list((int, uint(64)));  // (index, binary) pairs for new matrices
        var seenIndices: domain(int, parSafe=false);  // Indices of matrices we've seen before
        var patternToOriginalMapping: map(uint(64), list(uint(64)));  // Map to track original patterns per canonical form
        
        // Thread-local set of seen matrices for cache optimization
        var localSeenMatrices: set(uint(64), parSafe=false);
        
        if logLevel == LogLevel.DEBUG {
            writeln("\nProcessing ", numMotifs, " motifs for pattern identification...");
        }
        
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
                        
                        // Use thread-local edge checking
                        var eid = localGetEdgeId(u, w, isModified, local_node_OUT_Neighbours);
                        if eid != -1 {
                            batchedMatrices[i * (k * k) + row * k + col] = 1;
                            
                            // Update binary representation - set bit at position (row * k + col)
                            matrixBinary |= 1:uint(64) << (row * k + col);
                        }
                    }
                }
            }
            
            if logLevel == LogLevel.DEBUG {
                writeln("  Motif ", i, " matrix binary: ", matrixBinary);
                
                // Visualize the adjacency matrix for this motif
                writeln("  Adjacency matrix for motif ", i, ":");
                for row in 0..<k {
                    write("    ");
                    for col in 0..<k {
                        write(batchedMatrices[i * (k * k) + row * k + col], " ");
                    }
                    writeln();
                }
            }
            
            // Check if we've seen this matrix before in this thread's processing
            if localSeenMatrices.contains(matrixBinary) {
                // We've seen this pattern before, skip Nauty processing
                seenIndices.add(i);
                if logLevel == LogLevel.DEBUG {
                    writeln("  Matrix binary ", matrixBinary, " already seen - skipping Nauty");
                }
            } else {
                // New pattern, add to seen matrices and process
                localSeenMatrices.add(matrixBinary);
                matricesToProcess.pushBack((i, matrixBinary));
                if logLevel == LogLevel.DEBUG {
                    writeln("  New matrix binary ", matrixBinary, " - will be processed by Nauty");
                }
            }
        }
        
        if logLevel == LogLevel.DEBUG {
            writeln("\nFound ", matricesToProcess.size, " unique matrices to process with Nauty");
        }
        
        // Process only unseen matrices with Nauty
        if matricesToProcess.size > 0 {
            // Create smaller batch arrays for just the unseen matrices
            var uniqueCount = matricesToProcess.size;
            var uniqueMatrices: [0..#(uniqueCount * k * k)] int = 0;
            var uniqueResults: [0..#(uniqueCount * k)] int;
            
            // Fill unique matrices array
            for i in 0..<uniqueCount {
                var (origIdx, binary) = matricesToProcess[i];
                var origOffset = origIdx * (k * k);
                var newOffset = i * (k * k);
                
                // Copy matrix from original batch to unique batch
                for j in 0..<(k * k) {
                    uniqueMatrices[newOffset + j] = batchedMatrices[origOffset + j];
                }
                
                if logLevel == LogLevel.DEBUG {
                    writeln("  Processing matrix ", i, " (original index ", origIdx, ") with binary ", binary);
                }
            }
            
            // Process only unique matrices with Nauty
            var status = c_nautyClassify(uniqueMatrices, k, uniqueResults, 1, 0, uniqueCount);
            if logLevel == LogLevel.DEBUG {
                writeln("  Nauty processing complete with status: ", status);
            }
            
            // Copy results back to original results array and calculate canonical patterns
            for i in 0..<uniqueCount {
                var (origIdx, originalBinary) = matricesToProcess[i];
                var origOffset = origIdx * k;
                var newOffset = i * k;
                
                // Copy results
                for j in 0..<k {
                    batchedResults[origOffset + j] = uniqueResults[newOffset + j];
                }
                
                // Extract nauty results for this matrix
                var nautyLabels: [0..<k] int;
                for j in 0..<k {
                    nautyLabels[j] = uniqueResults[newOffset + j];
                }
                
                // Get adjacency matrix for this motif
                var adjMatrixStart = origIdx * (k * k);
                var adjMatrix: [0..#(k*k)] int;
                for j in 0..#(k*k) {
                    adjMatrix[j] = batchedMatrices[adjMatrixStart + j];
                }
                
                // Generate canonical pattern using the consistent approach
                var canonicalPattern = generateNautyPattern(adjMatrix, nautyLabels, k);
                
                // Add mapping from original binary to canonical pattern
                if !patternToOriginalMapping.contains(canonicalPattern) {
                    patternToOriginalMapping[canonicalPattern] = new list(uint(64));
                }
                patternToOriginalMapping[canonicalPattern].pushBack(originalBinary);
                
                if logLevel == LogLevel.DEBUG {
                    writeln("  Matrix ", i, " (original index ", origIdx, ") with binary ", originalBinary);
                    writeln("    is mapped to canonical pattern: ", canonicalPattern);
                    write("    with nauty labels: ");
                    for j in 0..<k {
                        write(nautyLabels[j], " ");
                    }
                    writeln();
                }
            }
        }
        
        // Count motifs for each canonical pattern
        for i in 0..<numMotifs {
            // Get the binary representation for this motif
            var matrixBinary: uint(64) = 0;
            var baseIdx = i * k;
            for row in 0..<k {
                for col in 0..<k {
                    if row != col && batchedMatrices[i * (k * k) + row * k + col] == 1 {
                        matrixBinary |= 1:uint(64) << (row * k + col);
                    }
                }
            }
            
            // If we've seen this exact matrix before, we need to find its canonical form
            var canonicalPattern: uint(64);
            if seenIndices.contains(i) {
                // Find which canonical pattern this binary maps to
                var found = false;
                for canonKey in patternToOriginalMapping.keys() {
                    var originals = patternToOriginalMapping[canonKey];
                    for original in originals {
                        if original == matrixBinary {
                            canonicalPattern = canonKey;
                            found = true;
                            break;
                        }
                    }
                    if found then break;
                }
            } else {
                // Get adjacency matrix for this motif
                var adjMatrixStart = i * (k * k);
                var adjMatrix: [0..#(k*k)] int;
                for j in 0..#(k*k) {
                    adjMatrix[j] = batchedMatrices[adjMatrixStart + j];
                }
                
                // Extract nauty results for this matrix
                var nautyLabels: [0..<k] int;
                for j in 0..<k {
                    nautyLabels[j] = batchedResults[i * k + j];
                }
                
                // Generate canonical pattern using the consistent approach
                canonicalPattern = generateNautyPattern(adjMatrix, nautyLabels, k);
            }
            
            // Update counts for this canonical pattern
            if !canonicalPatternMap.contains(canonicalPattern) {
                canonicalPatternMap[canonicalPattern] = 0;
            }
            canonicalPatternMap[canonicalPattern] += 1;
        }
        
        // Print detailed pattern information
        writeln("\nPattern summary for node ", targetNode, ":");
        writeln("  Total motifs found: ", numMotifs);
        writeln("  Unique canonical patterns: ", canonicalPatternMap.size);
        
        if canonicalPatternMap.size > 0 {
            writeln("\nPattern details:");
            var patternList: [1..canonicalPatternMap.size] (uint(64), int);
            var idx = 1;
            for pattern in canonicalPatternMap.keys() {
                patternList[idx] = (pattern, canonicalPatternMap[pattern]);
                idx += 1;
            }
            
            // Sort by frequency (highest first)
            sort(patternList, comparator=new PatternComparator());
            
            for (pattern, count) in patternList {
                writeln("  Canonical pattern ", pattern, ": ", count, " occurrences");
                
                // Show which original pattern(s) mapped to this canonical form
                if patternToOriginalMapping.contains(pattern) {
                    write("    Original patterns: ");
                    var first = true;
                    for original in patternToOriginalMapping[pattern] {
                        if !first then write(", ");
                        write(original);
                        first = false;
                    }
                    writeln();
                }
            }
        }
        
        writeln("====================================\n");
    }
    
    writeln("Completed processing all target nodes");
}

// Call this function with an array of nodes to process in parallel
// Example: EnumerateForMultipleNodes([1, 5, 10, 50], n, motifSize, maxDeg);
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
        // Gathers unique valid neighbors for the current level.
        proc initChildSet(ref state: KavoshState, root: int, level: int) throws {
            if logLevel == LogLevel.DEBUG {
                writeln("====== initChildSet called for level ", level, " and root ", root, " ======");
            }

            // Initialize count for this level to 0
            state.setChildSet(level, 0, 0);
            const parentsCount = state.getSubgraph(level-1, 0);

            // For each vertex chosen at the previous level, get its neighbors
            for p in 1..parentsCount {
                const parent = state.getSubgraph(level-1, p);
                
                for neighbor in nodeNeighbours[parent] {
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

            if logLevel == LogLevel.DEBUG {
                writeln("initChildSet: Found ", state.getChildSet(level, 0), " valid children at level ", level);
                write("Children: ");
                for i in 1..state.getChildSet(level, 0) {
                    write(state.getChildSet(level, i), " ");
                }
                writeln();
            }
        }// End of initChildSet

        proc prepareNaugtyArguments(ref state: KavoshState) throws {
            if logLevel == LogLevel.DEBUG {
                writeln("===== prepareNaugtyArguments called =====");
            }

            // Step 1: Build array of chosen vertices
            var chosenVerts: [1..state.k] int;
            var idx = 1;
            
            // Gather vertices level by level
            for level in 0..<state.k {
                const vertCount = state.getSubgraph(level, 0);  // Get count for this level
                for pos in 1..vertCount {
                    if idx > state.k {
                        halt("Error: More vertices than expected");
                    }
                    chosenVerts[idx] = state.getSubgraph(level, pos);
                    idx += 1;
                }
            }

            if idx - 1 != state.k {
                halt("Error: Didn't find exactly k vertices");
            }

            // Step 2: Create adjacency matrix
            // Use 1D array for k x k matrix, initialized to 0
            var adjMatrix: [0..#(state.k * state.k)] int = 0;

            // Step 3: Fill adjacency matrix
            // For each pair of vertices, check if edge exists
            for i in 0..#state.k {
                for j in 0..#state.k {
                    if i != j {  // Skip self-loops
                        var u = chosenVerts[i+1];  // +1 because chosenVerts is 1-based
                        var w = chosenVerts[j+1];
                        var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                        if eid != -1 {
                            adjMatrix[i * state.k + j] = 1;
                        }
                    }
                }
            }

            if logLevel == LogLevel.DEBUG {
                // Print detailed debug information
                writeln("\nChosen vertices:");
                for i in 1..state.k {
                    writeln("Position ", i-1, " -> Vertex ", chosenVerts[i]);
                }

                writeln("\nAdjacency Matrix (2D visualization):");
                for i in 0..#state.k {
                    for j in 0..#state.k {
                        write(adjMatrix[i * state.k + j], " ");
                    }
                    writeln();
                }
            }

            return (adjMatrix, chosenVerts);
        }// End of prepareNaugtyArguments

 
        // Explores subgraphs containing the root vertex,
        // expanding level by level until remainedToVisit = 0 (Base case - which means we have chosen k vertices).
        proc Explore(ref state: KavoshState, root: int, level: int, remainedToVisit: int) throws {
            if logLevel == LogLevel.DEBUG {
                writeln("===== Explore called =====");
                writeln("Current root: ", root, " level: ", level, " remainedToVisit: ", remainedToVisit);
                writeln("Visited Vertices: ", state.visited);
                writeln("Current partial subgraph level by level:");
                for l in 0..<level {
                    write("Level ", l, " (count=", state.getSubgraph(l, 0), "): ");
                    for x in 1..state.getSubgraph(l, 0) {
                        write(state.getSubgraph(l, x), " ");
                    }
                    writeln();
                }
                writeln("==========================");
            }

            // Base case: all k vertices chosen, now we have found a motif
            if remainedToVisit == 0 {
                // Extract the chosen vertices
                var chosenVerts: [1..state.k] int;
                var idx = 1;
                
                // Gather vertices level by level
                for level in 0..<state.k {
                    const vertCount = state.getSubgraph(level, 0);
                    for pos in 1..vertCount {
                        chosenVerts[idx] = state.getSubgraph(level, pos);
                            // Add to the list in the state

                        // if chosenVerts[idx] == 608 && root == 258{
                        //     writeln("FOUND VERTEX 608 about to be added in Explore base case!");
                        //     writeln("Root: ", root, ", level: ", level, ", pos: ", pos);
                        //     writeln("Current localsubgraphCount: ", state.localsubgraphCount);
                        // }
                        state.motifVertices.pushBack(chosenVerts[idx]);

                        idx += 1;

                    }
                }
                state.localsubgraphCount += 1;
                
                return;
            }



            // Get children for this level
            initChildSet(state, root, level);
            const childCount = state.getChildSet(level, 0);

            // Try all possible selection sizes at this level, from 1 to remainedToVisit
            for selSize in 1..remainedToVisit {
                if childCount < selSize {
                    // Not enough children to form this selection
                    if logLevel == LogLevel.DEBUG {
                        writeln("Not enough children (", childCount, ") to select ", selSize, " vertices at level ", level);
                    }
                    // Unmark visited children before returning
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

                if logLevel == LogLevel.DEBUG {
                    writeln("Exploring with initial selection of size ", selSize, " at level ", level);
                    write("Selected vertices: ");
                    for i in 1..selSize {
                        write(state.getSubgraph(level, i), " ");
                    }
                    writeln("we will Recurse with chosen selection");
                    writeln();
                }

                // Recurse with chosen selection
                Explore(state, root, level+1, remainedToVisit - selSize);

                // Generate other combinations using revolve-door algorithm
                ForwardGenerator(childCount, selSize, root, level, remainedToVisit, selSize, state);
            }

            // Cleanup: Unmark visited children before going up
            for i in 1..childCount {
                state.visited.remove(state.getChildSet(level, i));
            }
            state.setSubgraph(level, 0, 0);
        }// End of Explore



        // I read this for implementing revolving door 
        // https://encyclopediaofmath.org/wiki/Gray_code#Combinations.2C_partitions.2C_permutations.2C_and_other_objects.

        // swapping: Used by revolve-door Gray code generation to swap two elements
        // and then immediately Explore with the new combination.
        proc swapping(i: int, j: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws {
            if logLevel == LogLevel.DEBUG {
                writeln("swapping called: swapping indices ", i, " and ", j, " at level ", level);
                writeln("Before swapping: indexMap[level,i] = ", state.getIndexMap(level, i), 
                        " indexMap[level,j] = ", state.getIndexMap(level, j));
            }

            state.setIndexMap(level, i, state.getIndexMap(level, j));
            state.setSubgraph(level, state.getIndexMap(level, i), state.getChildSet(level, i));

            if logLevel == LogLevel.DEBUG {
                writeln("After swapping: subgraph[level,indexMap[level,i]] = childSet[level,i] = ", 
                        state.getChildSet(level, i));
                writeln("Now calling Explore after swapping");
            }

            Explore(state, root, level+1, remainedToVisit - m);
        }// End of swapping

        // ForwardGenerator(GEN): Part of revolve-door combination Forward Generator 
        proc ForwardGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws {
            if logLevel == LogLevel.DEBUG {
                writeln("ForwardGenerator called with n=", n, " k=", k, " level=", level, 
                        " remainedToVisit=", remainedToVisit, " m=", m);
            }

            if k > 0 && k < n {
                ForwardGenerator(n-1, k, root, level, remainedToVisit, m, state);

                if k == 1 {
                    if logLevel == LogLevel.DEBUG {
                        writeln("ForwardGenerator: k=1 case, calling swapping(n, n-1) => swapping(", 
                                n, ", ", n-1, ")");
                    }
                    swapping(n, n-1, root, level, remainedToVisit, m, state);
                } else {
                    if logLevel == LogLevel.DEBUG {
                        writeln("GEN: k>1 case, calling swapping(n, k-1) => swapping(", n, ", ", k-1, ")");
                    }
                    swapping(n, k-1, root, level, remainedToVisit, m, state);
                }

                reverseGenerator(n-1, k-1, root, level, remainedToVisit, m, state);
            }
        }// End of ForwardGenerator

        // reverseGenerator(NEG): Another part of revolve-door combination generation logic
        proc reverseGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws {
            if logLevel == LogLevel.DEBUG {
                writeln("reverseGenerator called with n=", n, " k=", k, " level=", level, 
                        " remainedToVisit=", remainedToVisit, " m=", m);
            }

            if k > 0 && k < n {
                ForwardGenerator(n-1, k-1, root, level, remainedToVisit, m, state);

                if k == 1 {
                    if logLevel == LogLevel.DEBUG {
                        writeln("reverseGenerator: k=1 case, calling swapping(n-1, n) => swapping(", 
                                n-1, ", ", n, ")");
                    }
                    swapping(n-1, n, root, level, remainedToVisit, m, state);
                } else {
                    if logLevel == LogLevel.DEBUG {
                        writeln("reverseGenerator: k>1 case, calling swapping(k-1, n) => swapping(", 
                                k-1, ", ", n, ")");
                    }
                    swapping(k-1, n, root, level, remainedToVisit, m, state);
                }

                reverseGenerator(n-1, k, root, level, remainedToVisit, m, state);
            }
        }// End of reverseGenerator



        proc patternToAdjMatrix(pattern: uint(64), k: int) throws {

            if logLevel == LogLevel.DEBUG {
                writeln("===== patternToAdjMatrix called =====");
                writeln("Input pattern: ", pattern);
                writeln("k value: ", k);
            }

            var adjMatrix: [0..#(k * k)] int = 0;
            var edgeCount = 0;
            var pos = 0;
            
            // First pass to count edges
            for i in 0..#k {
                for j in 0..#k {
                    if i != j {  // Skip self-loops but still increment pos
                        if (pattern & (1:uint(64) << pos)) != 0 {
                            adjMatrix[i * k + j] = 1;
                            edgeCount += 1;
                        }
                    }
                    pos += 1;
                }
            }

            return (adjMatrix);
        }// End of patternToAdjMatrix


        /* This function takes a set of patterns (represented as uint64) and motif size,
        runs Nauty on each pattern to find canonical forms, and returns:
        1. A set of unique motif classes
        2. A flat array containing all adjacency matrices of the unique motifs
        */
        proc verifyPatterns(globalMotifSet: set(uint(64)), globalCounts: map(uint(64), int), motifSize: int) throws {
            var uniqueMotifClasses: set(uint(64));
            var uniqueMotifCounts: map(uint(64), int);
            var motifCount = 0;
            
            // Local counters for this verification run----------TEMP
    var localMatricesProcessed = 0;
    var localCacheHits = 0;
    var localNautyCalls = 0;

            writeln("\n=== Starting Pattern Verification ===");
            //writeln(globalMotifSet.size, " patterns found before verification");
            //writeln(globalMotifSet, " are ");
            
            var motifArr: [0..#(globalMotifSet.size * motifSize * motifSize)] int;
            
            // Process each pattern found
            for pattern in globalMotifSet {
                if pattern == 0 {
                    writeln("Ignoring broken pattern");
                    continue;
                }

                // Convert pattern to adjacency matrix
                var adjMatrix = patternToAdjMatrix(pattern, motifSize);
                var results: [0..<motifSize] int;
                
                var performCheck = 1;
                var verbose = 0;
                if logLevel == LogLevel.DEBUG { verbose = 1; }

                // Run Nauty on the adjacency matrix - just once!
                var status = c_nautyClassify(adjMatrix, motifSize, results, performCheck, verbose, 1);
                
                if status != 0 {
                    writeln("Warning: Nauty failed with status ", status, " for pattern ", pattern);
                    continue;
                }

                // Check if Nauty returned canonical form equal to [0,1,2]
                var isCanonical = true;
                for i in 0..<motifSize {
                    if results[i] != i {
                        isCanonical = false;
                        break;
                    }
                }
                
                var canonicalPattern: uint(64);
                var canonicalMatrix: [0..#(motifSize * motifSize)] int;
                
                if isCanonical {
                    // If already canonical, use original pattern
                    canonicalPattern = pattern;
                    canonicalMatrix = adjMatrix;
                    if logLevel == LogLevel.DEBUG {
                        writeln("Pattern ", pattern, " is already canonical");
                    }
                } else {
                    // Generate canonical pattern directly from Nauty labels
                    canonicalPattern = generateNautyPattern(adjMatrix, results, motifSize);
                    writeln("canonicalPattern: ", canonicalPattern);
                    canonicalMatrix = patternToAdjMatrix(canonicalPattern, motifSize);
                    writeln("canonicalMatrix: ", canonicalMatrix);

                    if logLevel == LogLevel.DEBUG {
                        writeln("Pattern ", pattern, " mapped to canonical form ", canonicalPattern);
                    }
                }
                
                // Add the pattern and update counts
                if !uniqueMotifCounts.contains(canonicalPattern) {
                    uniqueMotifCounts[canonicalPattern] = 0;
                }
                uniqueMotifCounts[canonicalPattern] += globalCounts[pattern];
                uniqueMotifClasses.add(canonicalPattern);
                
                // Add matrix to motifArr
                var startIdx = motifCount * motifSize * motifSize;
                for i in 0..#(motifSize * motifSize) {
                    motifArr[startIdx + i] = canonicalMatrix[i];
                }
                motifCount += 1;
            }

            // Create final arrays
            var finalMotifArr: [0..#(motifCount * motifSize * motifSize)] int;
            var finalCountArr: [0..#motifCount] int;
            
            writeln("\n=== Verification Results ===");
            writeln("Started with total patterns: ", globalMotifSet.size);
            writeln("Found unique canonical patterns: ", uniqueMotifClasses.size);
            // writeln("\nCanonical patterns and their counts:");
            //  for pattern in uniqueMotifClasses {
            //      writeln("  Pattern ", pattern, ": ", uniqueMotifCounts[pattern], " occurrences");
            // }
            // writeln("===========================\n");
            
            var idx = 0;
            for pattern in uniqueMotifClasses {
                finalCountArr[idx] = uniqueMotifCounts[pattern];
                idx += 1;
            }
            
            for i in 0..#(motifCount * motifSize * motifSize) {
                finalMotifArr[i] = motifArr[i];
            }

            return (uniqueMotifClasses, finalMotifArr, finalCountArr);
        }


proc generateNautyPattern(adjMatrix: [] int, nautyLabels: [] int, motifSize: int): uint(64) {
    var pattern: uint(64) = 0;
    var pos = 0;
    
    // Look at each possible edge position in the canonical form
    for i in 0..<motifSize {
        for j in 0..<motifSize {
            if i != j {  // Skip self-loops
                // Get the position in the input matrix based on nauty labels
                var row = nautyLabels[i];
                var col = nautyLabels[j];
                
                // Check if there's an edge in the original matrix at these positions
                if row < motifSize && col < motifSize && adjMatrix[row * motifSize + col] == 1 {
                    // Set bit for this edge in canonical pattern
                    pattern |= 1:uint(64) << pos;
                }
            }
            pos += 1;
        }
    }
    
    return pattern;
}

       ///////////////////////////////Main Code/////////////////////////////////////////////////


        // Enumerate: Iterates over all vertices as potential roots
        // and calls Explore to find all subgraphs of size k containing that root.
 proc Enumerate(n: int, k: int, maxDeg: int) throws {
    forall v in 0..<n-k+1 with (ref globalMotifSet, ref totalCount, ref seenMatrices) {
        var state = new KavoshState(n, k, maxDeg);
        
        // Initialize root vertex in subgraph
        state.setSubgraph(0, 0, 1);
        state.setSubgraph(0, 1, v);
        state.visited.clear();
        state.visited.add(v);
        
        // Find all motifs for this root
        Explore(state, v, 1, state.k - 1);

        // Calculate how many complete motifs we found
        const numMotifs = state.localsubgraphCount;
        const totalVertices = state.motifVertices.size;
        
        // Skip if no motifs found
        if numMotifs == 0 || totalVertices == 0 {
            continue;
        }

        // Now classify all motifs found from this root
        var localPatterns: set(uint(64), parSafe=false);
        
        // Get the motif vertices as an array
        var motifVerticesArray = state.motifVertices.toArray();

        // Create arrays for batch processing
        var batchedMatrices: [0..#(numMotifs * k * k)] int = 0;
        
        // Track which matrices need to be processed
        var matricesToProcess: list((int, uint(64)));  // (index, binary) pairs for new matrices
        var seenIndices: domain(int, parSafe=false);  // Indices of matrices we've seen before
        
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
                        var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                        if eid != -1 {
                            batchedMatrices[i * (k * k) + row * k + col] = 1;
                            
                            // Update binary representation - set bit at position (row * k + col)
                            matrixBinary |= 1:uint(64) << (row * k + col);
                        }
                    }
                }
            }
    //writeln("matrixBinary: ", matrixBinary);
            // Check if we've seen this matrix before (for caching purposes)
            if seenMatrices.contains(matrixBinary) {
                // We've seen this pattern before, skip Nauty processing
                seenIndices.add(i);
                if logLevel == LogLevel.DEBUG {
                    writeln("  Matrix binary ", matrixBinary, " already seen - skipping Nauty");
                }
            } else {
                // New pattern, add to seen matrices and process
                seenMatrices.add(matrixBinary);
                matricesToProcess.pushBack((i, matrixBinary));
                if logLevel == LogLevel.DEBUG {
                    writeln("  New matrix binary ", matrixBinary, " - will be processed");
                }
            }
        }

        // Process only unseen matrices with Nauty
        if matricesToProcess.size > 0 {
            // Create smaller batch arrays for just the unseen matrices
            var uniqueCount = matricesToProcess.size;
            var uniqueMatrices: [0..#(uniqueCount * k * k)] int = 0;
            var uniqueResults: [0..#(uniqueCount * k)] int;
            
            if logLevel == LogLevel.DEBUG {
                writeln("Processing batch of ", uniqueCount, " matrices for root ", v);
            }
            
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
            
            // Process results directly to get canonical patterns
            for i in 0..<uniqueCount {
                var (origIdx, _) = matricesToProcess[i];
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
                
                // Always generate canonical pattern using generateNautyPattern
                var canonicalPattern = generateNautyPattern(adjMatrix, nautyLabels, k);
                
                if logLevel == LogLevel.DEBUG {
                    // Check if the matrix was already in canonical form
                    var isCanonical = true;
                    for j in 0..<k {
                        if nautyLabels[j] != j {
                            isCanonical = false;
                            break;
                        }
                    }
                    
                    if isCanonical {
                        writeln("  Matrix already in canonical form");
                    } else {
                        writeln("  Canonicalized matrix");
                    }
                    
                    writeln("  Generated canonical pattern: ", canonicalPattern);
                }
                
                // Add canonical pattern to local patterns
                localPatterns.add(canonicalPattern);
            }
        }

        // Count all motifs
        totalCount.add(numMotifs);
        
        // Add local patterns to global set
        globalMotifSet += localPatterns;
        
        if logLevel == LogLevel.DEBUG || (v % 1000 == 0) {
            writeln("Root ", v, ": Found ", numMotifs, " motifs, ", 
                    localPatterns.size, " unique patterns");
        }
    }
    
    // Set the final results
    globalMotifCount.write(totalCount.read());
    
    // Print statistics
    writeln("\nEnumerate Execution Statistics:");
    writeln("  Total motifs found: ", totalCount.read());
    writeln("  Total unique patterns found: ", globalMotifSet.size);
    writeln("  Total unique matrices seen: ", seenMatrices.size);
    
    writeln("\nEnumerate: finished enumeration");
}
    var timer:stopwatch;



    writeln("**********************************************************************");
    writeln("**********************************************************************");
        writeln("Graph loaded:");
        writeln("Number of nodes: ", g1.n_vertices);
        writeln("Number of edges: ", g1.n_edges);
        writeln("Number of cores (max task parallelism): ", here.maxTaskPar);



        writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
        writeln("Maximum degree: ", maxDeg);
        // Complete enumeration

     var timer0:stopwatch;
// timer0.start();
// Enumerate(g1.n_vertices, motifSize, maxDeg);
// timer0.stop();
// writeln("@@@@@@@@@@@@@@@@@@@@@@@@@Enumerate Time: ", timer0.elapsed());
//         writeln(" globalMotifSet Size = ", globalMotifSet.size);
//         writeln(" globalMotifCount = ", globalMotifCount.read());

//         writeln("**********************************************************************");
//         writeln("**********************************************************************");

timer0.restart();

EnumerateForMultipleNodes([1, 5, 10, 50], n, motifSize, maxDeg);
timer0.stop();
writeln("@@@@@@@@@@@@@@@@@@@@@@@@@EnumerateForNode Time: ", timer0.elapsed());


EnumerateForNode(10, g1.n_vertices, motifSize, maxDeg);



for elem in globalMotifSet { // Could track actual counts if needed
  globalMotifMap[elem] = 1;
}

var (uniqueMotifClasses, finalMotifArr, motifCounts) = 
     verifyPatterns(globalMotifSet, globalMotifMap, motifSize);
// writeln("After verification: Found ", uniqueMotifClasses.size, " unique canonical patterns: ", uniqueMotifClasses);
 writeln("After verification: Found ", uniqueMotifClasses.size);

            //var uniqueMotifClasses: set(uint(64));
            var uniqueMotifCounts: map(uint(64), int);
            var motifCount = 0;

        var tempArr: [0..0] int;
        //var finalMotifArr:[0..0] int;
        var srcPerMotif = makeDistArray(2*2, int);
        var dstPerMotif = makeDistArray(2*2, int);

        srcPerMotif[srcPerMotif.domain.low] = uniqueMotifClasses.size; //after verification
        srcPerMotif[srcPerMotif.domain.low +1] = globalMotifSet.size;   // before verification
        srcPerMotif[srcPerMotif.domain.low +2] = globalMotifCount.read(); // all motifs
        srcPerMotif[srcPerMotif.domain.low +3] = uniqueMotifCounts.size;     // this is naive approach to return pattern 200 has 134 instances
        
        return (srcPerMotif, finalMotifArr, tempArr, tempArr);
    }// End of runMotifCounting

}// End of MotifCounting Module