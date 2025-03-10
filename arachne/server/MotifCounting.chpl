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
        var localmotifClasses: set(uint(64), parSafe=false);
        // New: Add map to track counts for each pattern  //Added to support PIPELINE idea!
        //var localClassCounts: map(uint(64), int, parSafe=false);
    
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
        var nodeNeighbours: [0..<n] domain(int);

        forall v in 0..<n with (ref nodeDegree) {
            var neighbours: domain(int, parSafe=true);

            const NeiIn = dstRG1[segRG1[v]..<segRG1[v+1]];
            const NeiOut = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

            neighbours += NeiIn;
            neighbours += NeiOut;

            nodeDegree[v] = neighbours.size;
            // Collect all neighbors (both in and out) 
            nodeNeighbours[v] = neighbours;
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
    
    //var nautyCache: map(uint(64), [0..<k] int, parSafe=true);


    var globalMotifSet: set(uint(64), parSafe=true);
    var totalCount: atomic int;
totalCount.write(0);

// global set to track seen matrix binary representations
    var seenMatrices: set(uint(64), parSafe=true);

        var Sampling: bool = false;
        if doSampling == 1 then Sampling = true;
    
        var doMOtifDetail: bool = true;

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
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


       proc generatePatternDirect(ref chosenVerts: [] int, ref nautyLabels: [] int, k: int): uint(64) throws {
            var pattern: uint(64) = 0;
            var pos = 0;
            if logLevel == LogLevel.DEBUG {
                writeln("  In generatePatternDirect:");
                writeln("    chosenVerts domain: ", chosenVerts.domain);
                writeln("    nautyLabels domain: ", nautyLabels.domain);
            }            
            // Generate pattern directly from vertex pairs
            for i in 0..#k {
                for j in 0..#k {
                    if i != j {
                        // Add boundary checking
                        if nautyLabels[i] < 0 || nautyLabels[i] >= k {
                            writeln("    ERROR: Invalid nauty label at i=", i, ": ", nautyLabels[i]);
                            continue;
                        }
                        if nautyLabels[j] < 0 || nautyLabels[j] >= k {
                            writeln("    ERROR: Invalid nauty label at j=", j, ": ", nautyLabels[j]);
                            continue;
                        }
                        
                        // Verify indices are within bounds for chosenVerts
                        var idx1 = nautyLabels[i] + 1;
                        var idx2 = nautyLabels[j] + 1;
                        
                        if idx1 < chosenVerts.domain.low || idx1 > chosenVerts.domain.high {
                            writeln("    ERROR: Index ", idx1, " out of bounds for chosenVerts (", chosenVerts.domain, ")");
                            continue;
                        }
                        if idx2 < chosenVerts.domain.low || idx2 > chosenVerts.domain.high {
                            writeln("    ERROR: Index ", idx2, " out of bounds for chosenVerts (", chosenVerts.domain, ")");
                            continue;
                        }
                        
                        // Get vertices based on nauty labels
                        var u = chosenVerts[idx1];
                        var w = chosenVerts[idx2];
                        
                        //writeln("    Checking edge between vertices ", u, " and ", w);
                        
                        // Check for edge and set bit
                        var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                        if eid != -1 {
                            //writeln("    Edge found, setting bit at position ", pos);
                            pattern |= 1:uint(64) << pos;
                        }
                    }
                    pos += 1; // Increment position even when i == j to maintain ordering
                }
            }

            //writeln("    Generated pattern: ", pattern);
            return pattern;
        }

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
// Base case in Explore function: all k vertices chosen
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

            state.motifVertices.pushBack(chosenVerts[idx]);

            idx += 1;

        }
    }
    state.localsubgraphCount += 1;
    
    return;
}



                // var (adjMatrix, chosenVerts) = prepareNaugtyArguments(state);
                // var results: [0..<state.k] int = 0..<state.k;

                // var performCheck: int = 1; // Set to 1 to perform nauty_check, 0 to skip // DECIDE to add as input argument
                // var verbose = 0;

                // if logLevel == LogLevel.DEBUG { verbose = 1; } // Set to 1 to enable verbose logging for C++ side

                // //var status = c_nautyClassify(adjMatrix, motifSize, results, performCheck, verbose);
                // //Lets by pass the nauty
                // var status: int = 0;
                // var reults:[0..2] int= [0,1,2];

                // if logLevel == LogLevel.DEBUG {
                //     writeln("for subgraph = ",adjMatrix, "Nauty returned: ",
                //                             results, " we are in the way to Classify!", "status = ", status);
                // }

                // // Handle potential errors
                // if status != 0 {
                //     writeln("Error: c_nautyClassify failed with status ", status);
                // }

                // var pattern = generatePatternDirect(chosenVerts, results, state);
        
                // // Add to the set of patterns
                // state.localmotifClasses.add(pattern);
                
            //     return;
            // }

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
            
            writeln("\n=== Starting Pattern Verification ===");
            // writeln(globalMotifSet.size, " patterns found before verification: ");
            // writeln("Total patterns found before verification: ", globalMotifSet);
            // writeln("globalCounts: ", globalCounts);
            // writeln("globalCounts.size: ", globalCounts.size);

            // writeln("Pattern counts before verification:");
            // for pattern in globalCounts.keys() {
            //     writeln("Pattern ", pattern, ": ", globalCounts[pattern], " occurrences");
            // }
            // writeln("=====================================\n");
            
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
                if logLevel == LogLevel.DEBUG { verbose = 1; } // Set to 1 to enable verbose logging

                // Run Nauty on the adjacency matrix
                var status = c_nautyClassify(adjMatrix, motifSize, results, performCheck, verbose);
                
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
                
                var matrixToAdd: [0..#(motifSize * motifSize)] int;
                var patternToAdd: uint(64);
                
                if isCanonical { // If canonical, add original pattern and matrix
                    patternToAdd = pattern;
                    matrixToAdd = adjMatrix;
                    writeln("Pattern ", pattern, " is canonical");
                } else {
                    // Generate new pattern from Nauty's labeling
                    var nautyPattern = generateNautyPattern(adjMatrix, results, motifSize);
                    patternToAdd = nautyPattern;
                    matrixToAdd = patternToAdjMatrix(nautyPattern, motifSize);
                    writeln("Pattern ", pattern, " is not canonical, mapped to ", nautyPattern);
                }
                
                // Add the pattern and update counts
                if !uniqueMotifCounts.contains(patternToAdd) {
                    uniqueMotifCounts[patternToAdd] = 0;
                }
                uniqueMotifCounts[patternToAdd] += globalCounts[pattern];
                uniqueMotifClasses.add(patternToAdd);
                
                // Add matrix to motifArr
                var startIdx = motifCount * motifSize * motifSize;
                for i in 0..#(motifSize * motifSize) {
                    motifArr[startIdx + i] = matrixToAdd[i];
                }
                motifCount += 1;
            }

            // Create final arrays
            var finalMotifArr: [0..#(motifCount * motifSize * motifSize)] int;
            var finalCountArr: [0..#motifCount] int;
            
            writeln("\n=== Verification Results ===");
            writeln("Started with total patterns: ", globalMotifSet.size);
            writeln("Found unique canonical patterns: ", uniqueMotifClasses.size);
            writeln("Filtered out non-canonical patterns: ", globalMotifSet.size - uniqueMotifClasses.size);
            writeln("\nCanonical patterns and their counts:");
            // for pattern in uniqueMotifClasses {
            //     writeln("  Pattern ", pattern, ": ", uniqueMotifCounts[pattern], " occurrences");
            // }
            writeln("===========================\n");
            
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

        // New function to create pattern from adjMatrix and Nauty labeling
        proc generateNautyPattern(adjMatrix: [] int, nautyLabels: [] int, motifSize: int): uint(64) {
            var pattern: uint(64) = 0;
            var pos = 0;
            
            // Look at each possible edge in the new ordering
            for i in 0..#motifSize {
                for j in 0..#motifSize {
                    if i != j {
                        // Check if edge exists after applying Nauty's labeling
                        var src = nautyLabels[i];
                        var dst = nautyLabels[j];
                        if adjMatrix[src * motifSize + dst] == 1 {
                            pattern |= 1:uint(64) << pos;
                        }
                    }
                    pos += 1;
                }
            }
            return pattern;
        }
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
proc verifyPatternsNode(nodePatterns: set(uint(64)), nodeMotifCount: int, motifSize: int) throws {
    var uniqueMotifClasses: set(uint(64));
    var uniqueMotifCounts: map(uint(64), int);
    var motifCount = 0;
    
    writeln("\n=== Starting Node-Specific Pattern Verification ===");
    
    var motifArr: [0..#(nodePatterns.size * motifSize * motifSize)] int;
    
    // Create a simple count map (each pattern occurs at least once)
    var nodeCounts: map(uint(64), int);
    for pattern in nodePatterns {
        nodeCounts[pattern] = 1;
    }
    
    // Process each pattern found
    for pattern in nodePatterns {
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

        // Run Nauty on the adjacency matrix
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
        
        var patternToAdd: uint(64);
        var matrixToAdd: [0..#(motifSize * motifSize)] int;
        
        if isCanonical {
            // If canonical, add original pattern and matrix
            patternToAdd = pattern;
            matrixToAdd = adjMatrix;
            writeln("Pattern ", pattern, " is canonical");
        } else {
            // Generate new pattern from Nauty's labeling
            var nautyPattern = generateNautyPattern(adjMatrix, results, motifSize);
            
            // Create new adjacency matrix for this pattern
            var newAdjMatrix = patternToAdjMatrix(nautyPattern, motifSize);
            var newResults: [0..<motifSize] int;
            
            // Try again with new matrix to ensure canonical form
            status = c_nautyClassify(newAdjMatrix, motifSize, newResults, performCheck, verbose, 1);
            
            if status != 0 {
                writeln("Warning: Nauty failed with status ", status, " for derived pattern ", nautyPattern);
                continue;
            }
            
            // Check if new results are canonical
            var newIsCanonical = true;
            for i in 0..<motifSize {
                if newResults[i] != i {
                    newIsCanonical = false;
                    break;
                }
            }
            
            if newIsCanonical {
                patternToAdd = nautyPattern;
                matrixToAdd = newAdjMatrix;
                writeln("Pattern ", pattern, " mapped to canonical form ", nautyPattern);
            } else {
                // We need to go deeper - generate another level
                var finalPattern = generateNautyPattern(newAdjMatrix, newResults, motifSize);
                var finalMatrix = patternToAdjMatrix(finalPattern, motifSize);
                
                // Final check
                var finalResults: [0..<motifSize] int;
                status = c_nautyClassify(finalMatrix, motifSize, finalResults, performCheck, verbose, 1);
                
                // At this point, we should just accept whatever we get
                patternToAdd = finalPattern;
                matrixToAdd = finalMatrix;
                
                writeln("Pattern ", pattern, " -> ", nautyPattern, " -> ", finalPattern, 
                        " (final canonical: ", isCanonicalLabeling(finalResults), ")");
            }
        }
        
        // Add the pattern and update counts
        if !uniqueMotifCounts.contains(patternToAdd) {
            uniqueMotifCounts[patternToAdd] = 0;
        }
        uniqueMotifCounts[patternToAdd] += nodeCounts[pattern];
        uniqueMotifClasses.add(patternToAdd);
        
        // Add matrix to motifArr
        var startIdx = motifCount * motifSize * motifSize;
        for i in 0..#(motifSize * motifSize) {
            motifArr[startIdx + i] = matrixToAdd[i];
        }
        motifCount += 1;
    }

    // Create final arrays
    var finalMotifArr: [0..#(motifCount * motifSize * motifSize)] int;
    var finalCountArr: [0..#motifCount] int;
    
    writeln("\n=== Node-Specific Verification Results ===");
    writeln("Started with total patterns: ", nodePatterns.size);
    writeln("Found unique canonical patterns: ", uniqueMotifClasses.size);
    writeln("Filtered out non-canonical patterns: ", nodePatterns.size - uniqueMotifClasses.size);
    writeln("\nCanonical patterns and their counts:");
    for pattern in uniqueMotifClasses {
        writeln("  Pattern ", pattern, ": ", uniqueMotifCounts[pattern], " occurrences");
    }
    writeln("===========================\n");
    
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

// Helper function to check if results are canonical [0,1,2,...]
proc isCanonicalLabeling(results: [] int): bool {
    for i in 0..<results.size {
        if results[i] != i {
            return false;
        }
    }
    return true;
}
/* Find all motifs containing a specific node */
proc findMotifsContainingNode(targetNode: int, n: int, k: int, maxDeg: int,
                            ref nodeNeighbours: [] domain(int)) throws {
    writeln("Finding all motifs containing node ", targetNode);
    var timer = new stopwatch();
    timer.start();
    
    // Step 1: Find the k-hop neighborhood around the target node
    var neighborhood = computeKHopNeighborhood(targetNode, k-1, nodeNeighbours);
    timer.stop();
    
    writeln("Found ", neighborhood.size, " nodes within ", k-1, " hops of node ", targetNode);
    writeln("Neighborhood calculation time: ", timer.elapsed(), " seconds");
    
    // Create result collections
    var motifPatterns: set(uint(64), parSafe=true);
    var motifCount: atomic int;
    var seenMatrices: set(uint(64), parSafe=true);
    
    // Step 2: Process motifs from each neighbor as root
    timer.clear();
    timer.start();
    
    // Process nodes in parallel with a balanced distribution
    forall root in neighborhood with (ref motifPatterns, ref motifCount, ref seenMatrices) {
        var localState = new KavoshState(n, k, maxDeg);
        
        // Initialize with this root
        localState.setSubgraph(0, 0, 1);
        localState.setSubgraph(0, 1, root);
        localState.visited.clear();
        localState.visited.add(root);
        
        // Explore, but keep track of whether the target node is included
        ExploreWithTarget(localState, root, 1, k-1, targetNode, neighborhood);
        
        // Skip if no valid motifs found
        if localState.localsubgraphCount == 0 then continue;
        
        // Process motifs found with this root
        processMotifs(localState, motifPatterns, motifCount, seenMatrices);
    }
    
    timer.stop();
    writeln("Found ", motifCount.read(), " motifs containing node ", targetNode);
    writeln("These motifs belong to ", motifPatterns.size, " unique patterns");
    writeln("Pattern: ", motifPatterns);
    writeln("Motif exploration time: ", timer.elapsed(), " seconds");
    
    return (motifPatterns, motifCount.read());
}

/* Compute the k-hop neighborhood of a node */
proc computeKHopNeighborhood(startNode: int, k: int, 
                           ref nodeNeighbours: [] domain(int)): domain(int, parSafe=true) {
    // Initialize sets
    var neighborhood: domain(int, parSafe=true);
    var currentFrontier: domain(int, parSafe=true);
    var nextFrontier: domain(int, parSafe=true);
    
    // Start with the target node
    neighborhood.add(startNode);
    currentFrontier.add(startNode);
    
    // Use breadth-first search for k hops
    for hop in 1..k {
        nextFrontier.clear();
        
        // For each node in current frontier
        for node in currentFrontier {
            // Add all unvisited neighbors (both in and out)
            for neighbor in nodeNeighbours[node] {
                if !neighborhood.contains(neighbor) {
                    neighborhood.add(neighbor);
                    nextFrontier.add(neighbor);
                }
            }
            
            // For incoming edges, we need to check all potential nodes
            // This can be optimized if you have direct access to incoming edges
            for potentialInNode in 0..<nodeNeighbours.domain.high+1 {
                if nodeNeighbours[potentialInNode].contains(node) && 
                   !neighborhood.contains(potentialInNode) {
                    neighborhood.add(potentialInNode);
                    nextFrontier.add(potentialInNode);
                }
            }
        }
        
        // If no new nodes added, we can stop early
        if nextFrontier.size == 0 then break;
        
        // Update frontier for next hop
        currentFrontier = nextFrontier;
    }
    
    return neighborhood;
}
proc ForwardGeneratorWithTarget(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, 
                               ref state: KavoshState, targetNode: int, neighborhood: domain(int, parSafe=true)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("ForwardGeneratorWithTarget called with n=", n, " k=", k, " level=", level, 
                " remainedToVisit=", remainedToVisit, " m=", m);
    }

    if k > 0 && k < n {
        ForwardGeneratorWithTarget(n-1, k, root, level, remainedToVisit, m, state, targetNode, neighborhood);

        if k == 1 {
            if logLevel == LogLevel.DEBUG {
                writeln("ForwardGeneratorWithTarget: k=1 case, calling swappingWithTarget");
            }
            swappingWithTarget(n, n-1, root, level, remainedToVisit, m, state, targetNode, neighborhood);
        } else {
            if logLevel == LogLevel.DEBUG {
                writeln("ForwardGeneratorWithTarget: k>1 case, calling swappingWithTarget");
            }
            swappingWithTarget(n, k-1, root, level, remainedToVisit, m, state, targetNode, neighborhood);
        }

        reverseGeneratorWithTarget(n-1, k-1, root, level, remainedToVisit, m, state, targetNode, neighborhood);
    }
}

proc swappingWithTarget(i: int, j: int, root: int, level: int, remainedToVisit: int, m: int, 
                        ref state: KavoshState, targetNode: int, neighborhood: domain(int, parSafe=true)) throws {
    // Same as original swapping but calls ExploreWithTarget
    state.setIndexMap(level, i, state.getIndexMap(level, j));
    state.setSubgraph(level, state.getIndexMap(level, i), state.getChildSet(level, i));

    ExploreWithTarget(state, root, level+1, remainedToVisit - m, targetNode, neighborhood);
}

proc reverseGeneratorWithTarget(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, 
                               ref state: KavoshState, targetNode: int, neighborhood: domain(int, parSafe=true)) throws {
    if k > 0 && k < n {
        ForwardGeneratorWithTarget(n-1, k-1, root, level, remainedToVisit, m, state, targetNode, neighborhood);

        if k == 1 {
            swappingWithTarget(n-1, n, root, level, remainedToVisit, m, state, targetNode, neighborhood);
        } else {
            swappingWithTarget(k-1, n, root, level, remainedToVisit, m, state, targetNode, neighborhood);
        }

        reverseGeneratorWithTarget(n-1, k, root, level, remainedToVisit, m, state, targetNode, neighborhood);
    }
}
/* Modified Explore that only keeps motifs containing the target node */
proc ExploreWithTarget(ref state: KavoshState, root: int, level: int, 
                      remainedToVisit: int, targetNode: int,
                      neighborhood: domain(int, parSafe=true)) throws {
    // Base case: all k vertices chosen
    if remainedToVisit == 0 {
        // Check if current subgraph contains the target node
        var containsTarget = false;
        
        // First check if root is the target
        if root == targetNode {
            containsTarget = true;
        } else {
            // Check all vertices in the subgraph
            for l in 0..<state.k {
                for p in 1..state.getSubgraph(l, 0) {
                    if state.getSubgraph(l, p) == targetNode {
                        containsTarget = true;
                        break;
                    }
                }
                if containsTarget then break;
            }
        }
        
        // Only process this motif if it contains the target
        if containsTarget {
            // Add to flat list for batch processing
            for l in 0..<state.k {
                for p in 1..state.getSubgraph(l, 0) {
                    state.motifVertices.pushBack(state.getSubgraph(l, p));
                }
            }
            state.localsubgraphCount += 1;
        }
        
        return;
    }
    
    // Only initialize children within the neighborhood for efficiency
    initChildSetFiltered(state, root, level, neighborhood);
    const childCount = state.getChildSet(level, 0);
    
    // Rest of the function similar to regular Explore
    // Try all possible selection sizes at this level
    for selSize in 1..remainedToVisit {
        if childCount < selSize {
            // Not enough children for this selection
            for i in 1..childCount {
                state.visited.remove(state.getChildSet(level, i));
            }
            return;
        }
        
        // Initial selection
        state.setSubgraph(level, 0, selSize);
        for i in 1..selSize {
            state.setSubgraph(level, i, state.getChildSet(level, i));
            state.setIndexMap(level, i, i);
        }
        
        // Recurse with this selection
        ExploreWithTarget(state, root, level+1, remainedToVisit - selSize, targetNode, neighborhood);
        
        // Generate other combinations
        ForwardGeneratorWithTarget(childCount, selSize, root, level, remainedToVisit, selSize, state, targetNode, neighborhood);
    }
    
    // Cleanup
    for i in 1..childCount {
        state.visited.remove(state.getChildSet(level, i));
    }
    state.setSubgraph(level, 0, 0);
}

/* Filtered version of initChildSet that only considers nodes in the neighborhood */
proc initChildSetFiltered(ref state: KavoshState, root: int, level: int, 
                        neighborhood: domain(int, parSafe=true)) throws {
    // Initialize count to 0
    state.setChildSet(level, 0, 0);
    const parentsCount = state.getSubgraph(level-1, 0);
    
    // For each chosen parent
    for p in 1..parentsCount {
        const parent = state.getSubgraph(level-1, p);
        
        // Check each neighbor
        for neighbor in nodeNeighbours[parent] {
            // Must be greater than root, not visited, and in neighborhood
            if neighbor > root && !state.visited.contains(neighbor) && 
               neighborhood.contains(neighbor) {
                const currentCount = state.getChildSet(level, 0) + 1;
                state.setChildSet(level, 0, currentCount);
                state.setChildSet(level, currentCount, neighbor);
                state.visited.add(neighbor);
            }
        }
    }
}

/* Optimized batch processing of motifs */
/* Optimized batch processing of motifs */
proc processMotifs(ref state: KavoshState, ref globalSet: set(uint(64), parSafe=true),
                  ref globalCount: atomic int, ref seenMatrices: set(uint(64), parSafe=true)) throws {
    // Skip if no motifs found
    if state.localsubgraphCount == 0 then return;
    
    const numMotifs = state.localsubgraphCount;
    const k = state.k;
    
    writeln("=== Processing ", numMotifs, " motifs with k=", k, " ===");
    
    // Convert list to array for easier processing
    var vertices = state.motifVertices.toArray();
    writeln("Total vertices in list: ", vertices.size, " (expected: ", numMotifs * k, ")");
    
    // Arrays for batch processing
    var batchedMatrices: [0..#(numMotifs * k * k)] int = 0;
    var batchedResults: [0..#(numMotifs * k)] int;
    
    // Track which matrices need Nauty processing
    var matricesToProcess: list((int, uint(64)));
    var seenIndices: domain(int, parSafe=false);
    var localPatterns: set(uint(64), parSafe=false);
    
    // Fill matrices and detect duplicates
    for i in 0..<numMotifs {
        var baseIdx = i * k;
        var matrixBinary: uint(64) = 0;
        
        writeln("\nProcessing motif #", i, ":");
        writeln("Vertices: ", [j in 0..<k] vertices[baseIdx + j]);
        
        // Create adjacency matrix
        writeln("Building adjacency matrix:");
        for row in 0..<k {
            for col in 0..<k {
                if row != col {
                    var u = vertices[baseIdx + row];
                    var w = vertices[baseIdx + col];
                    
                    // Use the same edge detection as in generatePatternDirect
                    var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                    var hasEdge = (eid != -1);
                    
                    if hasEdge {
                        batchedMatrices[i * (k * k) + row * k + col] = 1;
                        matrixBinary |= 1:uint(64) << (row * k + col);
                        writeln("  Edge ", u, " -> ", w, ": Yes (eid=", eid, ")");
                    } else {
                        writeln("  Edge ", u, " -> ", w, ": No");
                    }
                }
            }
        }
        
        writeln("Matrix in row format:");
        for row in 0..<k {
            write("  ");
            for col in 0..<k {
                write(batchedMatrices[i * (k * k) + row * k + col], " ");
            }
            writeln();
        }
        
        writeln("Binary representation: ", matrixBinary);
        
        // Check if we've seen this matrix before
        if seenMatrices.contains(matrixBinary) {
            writeln("  Matrix already seen - skipping Nauty classification");
            seenIndices.add(i);
        } else {
            writeln("  New matrix - will be classified by Nauty");
            seenMatrices.add(matrixBinary);
            matricesToProcess.pushBack((i, matrixBinary));
        }
    }
    
    writeln("\nFound ", matricesToProcess.size, " unique matrices out of ", numMotifs, " total");
    
    // Process only unique matrices with Nauty
    if matricesToProcess.size > 0 {
        var uniqueCount = matricesToProcess.size;
        var uniqueMatrices: [0..#(uniqueCount * k * k)] int = 0;
        var uniqueResults: [0..#(uniqueCount * k)] int;
        
        writeln("Preparing matrices for Nauty processing...");
        
        // Fill unique matrices array
        for i in 0..<uniqueCount {
            var (origIdx, binary) = matricesToProcess[i];
            var origOffset = origIdx * (k * k);
            var newOffset = i * (k * k);
            
            writeln("  Matrix #", i, " (original idx: ", origIdx, ", binary: ", binary, ")");
            
            for j in 0..<(k * k) {
                uniqueMatrices[newOffset + j] = batchedMatrices[origOffset + j];
            }
            
            writeln("  Matrix visualization:");
            for row in 0..<k {
                write("    ");
                for col in 0..<k {
                    write(uniqueMatrices[newOffset + row * k + col], " ");
                }
                writeln();
            }
        }
        
        // Process with Nauty
        writeln("Calling Nauty with ", uniqueCount, " matrices...");
        var status = c_nautyClassify(uniqueMatrices, k, uniqueResults, 1, 0, uniqueCount);
        writeln("Nauty status: ", status);
        
        // Copy results back
        for i in 0..<uniqueCount {
            var (origIdx, _) = matricesToProcess[i];
            var origOffset = origIdx * k;
            var newOffset = i * k;
            
            writeln("  Results for matrix #", i, " (original idx: ", origIdx, "):");
            write("    Nauty labels: ");
            for j in 0..<k {
                batchedResults[origOffset + j] = uniqueResults[newOffset + j];
                write(uniqueResults[newOffset + j], " ");
            }
            writeln();
        }
    }
    
    // Process results for each motif
    writeln("\nGenerating patterns from Nauty results:");
    for i in 0..<numMotifs {
        // Count all motifs
        globalCount.add(1);
        
        // Skip pattern generation for seen matrices
        if seenIndices.contains(i) {
            writeln("  Motif #", i, ": Skipping (duplicate matrix)");
            continue;
        }
        
        // Get vertices for this motif
        var baseIdx = i * k;
        var motifVertices: [1..k] int;
        for j in 0..<k {
            motifVertices[j+1] = vertices[baseIdx + j];
        }
        
        // Extract Nauty results
        var nautyResults: [0..<k] int;
        for j in 0..<k {
            nautyResults[j] = batchedResults[i * k + j];
        }
        
        writeln("  Motif #", i, ":");
        writeln("    Vertices: ", motifVertices);
        writeln("    Nauty labels: ", nautyResults);
        
        // Generate pattern and add to set
        var pattern = generatePatternDirect(motifVertices, nautyResults, k);
        localPatterns.add(pattern);
        
        writeln("    Generated pattern: ", pattern);
    }
    
    writeln("\nFound ", localPatterns.size, " unique patterns:");
    writeln("Local patterns: ", localPatterns);
    
    // Add local patterns to global set
    globalSet += localPatterns;
    writeln("Updated global set to: ", globalSet);
    writeln("=== Processing complete ===\n");
}
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////




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
        
        // Verify we have the expected number of vertices
        if totalVertices != numMotifs * k {
            writeln("WARNING: Unexpected number of vertices. Expected ", numMotifs * k, 
                    " but got ", totalVertices, ". Skipping this root.");
            continue;
        }
        
        // Now classify all motifs found from this root
        var localPatterns: set(uint(64), parSafe=false);
        
        // Get the motif vertices as an array
        var motifVerticesArray = state.motifVertices.toArray();
        
        // Create arrays for batch processing
        var batchedMatrices: [0..#(numMotifs * k * k)] int = 0;
        var batchedResults: [0..#(numMotifs * k)] int;
        
        // Track which matrices need to be processed
        var matricesToProcess: list((int, uint(64)));  // (index, binary) pairs for new matrices
        var seenIndices: domain(int, parSafe=false);  // Indices of matrices we've seen before
        
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
                        var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                        if eid != -1 {
                            batchedMatrices[i * (k * k) + row * k + col] = 1;
                            
                            // Update binary representation - set bit at position (row * k + col)
                            matrixBinary |= 1:uint(64) << (row * k + col);
                        }
                    }
                }
            }
            
            // Check if we've seen this matrix before
            if seenMatrices.contains(matrixBinary) {
                // We've seen this pattern before, skip Nauty processing
                seenIndices.add(i);
            } else {
                // New pattern, add to seen matrices and process
                seenMatrices.add(matrixBinary);
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
            
            // Copy results back to original results array
            for i in 0..<uniqueCount {
                var (origIdx, _) = matricesToProcess[i];
                var origOffset = origIdx * k;
                var newOffset = i * k;
                
                // Copy results
                for j in 0..<k {
                    batchedResults[origOffset + j] = uniqueResults[newOffset + j];
                }
            }
        }
        
        // Process results for each motif
        for i in 0..<numMotifs {
            // Skip processing motifs that were seen before
            if seenIndices.contains(i) {
                // We still need to count these motifs
                totalCount.add(1);
                continue;
            }
            
            // Get vertices for this motif
            var baseIdx = i * k;
            var vertices: [1..k] int;
            for j in 0..<k {
                vertices[j+1] = motifVerticesArray[baseIdx + j];
            }
            
            // Extract results for this motif
            var nautyResults: [0..<k] int;
            for j in 0..<k {
                nautyResults[j] = batchedResults[i * k + j];
            }
            
            // Generate pattern
            var pattern = generatePatternDirect(vertices, nautyResults, k);
            localPatterns.add(pattern);
            
            // Count this motif
            totalCount.add(1);
        }
        
        // Add local patterns to global set
        globalMotifSet += localPatterns;
    }
    
    // Set the final results
    globalMotifCount.write(totalCount.read());
    
    writeln("Enumerate: finished enumeration");
    writeln("Total motifs found: ", globalMotifCount.read());
    writeln("Unique patterns found: ", globalMotifSet.size);
    writeln("Unique matrices seen (pre-Nauty): ", seenMatrices.size);
}
    var timer:stopwatch;

   var targetNode: int = 100;
    if targetNode >= 0 && targetNode < n {
        // Find motifs containing the specific node
        var (nodePatterns, nodeMotifCount) = findMotifsContainingNode(
            targetNode, n, motifSize, maxDeg, nodeNeighbours);
        
        writeln("-----------------------------------------------------------------------");
        writeln("Found ", nodeMotifCount, " motifs containing node ", targetNode);
        writeln("These motifs belong to ", nodePatterns.size, " unique pattern classes");
        writeln("-----------------------------------------------------------------------");
        // // Use the new verification function specifically for node patterns
        var (uniqueMotifClasses, finalMotifArr, motifCounts) = 
             verifyPatternsNode(nodePatterns, nodeMotifCount, motifSize);
            

    }  

    writeln("**********************************************************************");
    writeln("**********************************************************************");
        writeln("Graph loaded:");
        writeln("Number of nodes: ", g1.n_vertices);
        writeln("Number of edges: ", g1.n_edges);
        writeln("Number of cores (max task parallelism): ", here.maxTaskPar);



        writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
        writeln("Maximum degree: ", maxDeg);
        // Complete enumeration
        Enumerate(g1.n_vertices, motifSize, maxDeg);
        writeln(" globalMotifSet = ", globalMotifSet);
        writeln(" globalMotifCount = ", globalMotifCount.read());

        writeln("**********************************************************************");
        writeln("**********************************************************************");

for elem in globalMotifSet { // Could track actual counts if needed
  globalMotifMap[elem] = 1;
}

    //var (uniqueMotifClasses, finalMotifArr, motifCounts) = verifyPatterns(globalMotifSet, globalMotifMap, motifSize);
            var uniqueMotifClasses: set(uint(64));
            var uniqueMotifCounts: map(uint(64), int);
            var motifCount = 0;

        var tempArr: [0..0] int;
        var finalMotifArr:[0..0] int;
        var srcPerMotif = makeDistArray(2*2, int);
        var dstPerMotif = makeDistArray(2*2, int);

        srcPerMotif[srcPerMotif.domain.low] = uniqueMotifClasses.size; //after verification
        srcPerMotif[srcPerMotif.domain.low +1] = globalMotifSet.size;   // before verification
        srcPerMotif[srcPerMotif.domain.low +2] = globalMotifCount.read(); // all motifs
        srcPerMotif[srcPerMotif.domain.low +3] = uniqueMotifCounts.size;     // this is naive approach to return pattern 200 has 134 instances
        
        return (srcPerMotif, finalMotifArr, tempArr, tempArr);
    }// End of runMotifCounting

}// End of MotifCounting Module