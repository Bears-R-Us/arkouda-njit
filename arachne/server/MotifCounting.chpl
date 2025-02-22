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
    
    /* New ASWS-specific records and classes */
    record ASWSConfig {
        var n: int;              // Graph size
        var k: int;              // Motif size
        var initialWavefrontSize: int;
        var hubPercentile: real;
        var minSamplesPerStratum: int;
        
        proc init(n: int, k: int) {
            this.n = n;
            this.k = k;
            this.initialWavefrontSize = min(100, n); // Start small
            this.hubPercentile = 0.9;                // Top 10% as hubs
            this.minSamplesPerStratum = 30;          // Statistical minimum
            init this;
        }
    }
    
    /* Manages the wavefront sampling state */
    class WavefrontState {
        var ASconfig: ASWSConfig;
        var wavefront: domain(int, parSafe=true);
        var hubSet: domain(int, parSafe=true);
        var sampledVertices: domain(int, parSafe=true);
        var fingerprints: [0..#ASconfig.n] real;
        var timer: stopwatch;
        
        proc init(ASconfig: ASWSConfig) {
            this.ASconfig = ASconfig;
            this.wavefront = {1..0};
            this.hubSet = {1..0};
            this.sampledVertices = {1..0};
            var a1: [0..#ASconfig.n] real;
            this.fingerprints = a1;
            this.timer = new stopwatch();
            init this;
        }
    }



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
        var localClassCounts: map(uint(64), int, parSafe=false);

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
            // Initialize the new map
            this.localClassCounts = new map(uint(64), int, parSafe=false);
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
        verbose: int(64)
    ) : int(64);
  

    proc runMotifCounting(g1: SegGraph,  
              // sizeLimit: string, in timeLimit: int, in printProgressInterval: int,
               motifSize: int, in printProgressInterval: int,
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

// To Oliver: I know that it seems CRAZY but information in globalMotifCount + globalMotifSet == globalMotifMap
// for inknown reason I couldnt remove globalMotifCount and globalMotifSet. I got so many errors

        // All motif counting and classify variables
        var globalMotifCount: atomic int;
        var globalMotifSet: set(uint(64), parSafe=true);
        // Initiate it to 0
        globalMotifCount.write(0);
        // A global map to track pattern counts across all threads
        var globalMotifMap: map(uint(64), int);
        var syncVar: sync bool;

        var doSampling: bool = true;
        var doMOtifDetail: bool = true;
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   /* Identifies hub vertices based on degree */
proc identifyHubs(ref state: WavefrontState, nodeDegree: [] int) {
    writeln("\n=== Starting Hub Identification ===");
    writeln("- Graph size: ", state.ASconfig.n);
    writeln("- Hub percentile: ", state.ASconfig.hubPercentile);
    
    state.timer.start();
    
    // Create a copy for sorting
    var sortedDegrees = nodeDegree;
    sort(sortedDegrees, new ReverseComparator());
    
    writeln("- Degree distribution:");
    writeln("  * Max degree: ", sortedDegrees[0]);
    writeln("  * Median degree: ", sortedDegrees[sortedDegrees.size/2]);
    writeln("  * Min degree: ", sortedDegrees[sortedDegrees.size-1]);
    
    // Calculate hub threshold
    var hubIndex = (state.ASconfig.n * (1.0 - state.ASconfig.hubPercentile)): int;
    var hubThreshold = sortedDegrees[hubIndex];
    
    writeln("- Hub threshold: ", hubThreshold);
    
    // Identify hubs
    var hubCount = 0;
    ref hubSetRef = state.hubSet;  // Get reference before forall
    
    forall v in 0..#state.ASconfig.n with (ref hubSetRef, + reduce hubCount) {
        if nodeDegree[v] >= hubThreshold {
            hubSetRef.add(v);
            hubCount += 1;
        }
    }

    state.timer.stop();
    
    writeln("=== Hub Identification Complete ===");
    writeln("- Identified ", hubCount, " hubs");
    writeln("- Time taken: ", state.timer.elapsed(), " seconds");
    writeln();
}

    /* Initializes the wavefront with strategic vertices */
    proc initializeWavefront(ref state: WavefrontState, nodeDegree: [] int) {
            writeln("\n=== Initializing Wavefront ===");
            writeln("- Target size: ", state.ASconfig.initialWavefrontSize);
        
        
        state.timer.clear();
        state.timer.start();
        
        // Always include hubs in initial wavefront
        state.wavefront = state.hubSet;
        
            writeln("- Added ", state.hubSet.size, " hubs to wavefront");
                
        // Add more vertices if needed
        if state.wavefront.size < state.ASconfig.initialWavefrontSize {
            var remainingNeeded = state.ASconfig.initialWavefrontSize - state.wavefront.size;
            
                writeln("- Selecting ", remainingNeeded, " additional vertices");
            
            
            // Select additional vertices based on degree diversity
            var rng = new randomStream(real);
            var degreeBins: [0..4] domain(int, parSafe=true); // 5 degree ranges
            
            // Categorize non-hub vertices by degree
            var maxDeg = max reduce nodeDegree;
            forall v in 0..#state.ASconfig.n with (ref degreeBins) {
                if !state.hubSet.contains(v) {
                    var bin = (nodeDegree[v] * 5 / maxDeg): int;
                    bin = min(4, bin); // Ensure within bounds
                    degreeBins[bin].add(v);
                }
            }
            
            // Select proportionally from each bin
            var addedCount = 0;
            for bin in 0..4 {
                var toSelect = (remainingNeeded / 5): int;
                if degreeBins[bin].size > 0 {
                    for v in degreeBins[bin] {
                        if addedCount >= remainingNeeded then break;
                        if rng.next() < 0.5 { // Randomize selection
                            state.wavefront.add(v);
                            addedCount += 1;
                        }
                    }
                }
            }
        }
        
        state.timer.stop();
        
            writeln("=== Wavefront Initialization Complete ===");
            writeln("- Final wavefront size: ", state.wavefront.size);
            writeln("- Time taken: ", state.timer.elapsed(), " seconds");
            writeln();
    }

 /* Computes structural fingerprints for vertices */
proc computeFingerprints(ref state: WavefrontState, 
                       ref nodeNeighbours: [] domain(int),
                       ref nodeDegree: [] int) {
    writeln("\n=== Computing Structural Fingerprints ===");
    
    state.timer.clear();
    state.timer.start();
    
    // Get references before forall
    ref fingerprintsRef = state.fingerprints;
    ref wavefrontRef = state.wavefront;
    
    // For prototype: simple fingerprint based on degree and local clustering
    forall v in wavefrontRef with (ref fingerprintsRef) {
        // Compute local clustering coefficient
        var neighborEdges = 0;
        var possibleEdges = 0;
        
        for u in nodeNeighbours[v] {
            for w in nodeNeighbours[v] {
                if u != w {
                    possibleEdges += 1;
                    if nodeNeighbours[u].contains(w) {
                        neighborEdges += 1;
                    }
                }
            }
        }
        
        var clustering = if possibleEdges > 0 then neighborEdges:real / possibleEdges:real 
                       else 0.0;
        
        // Combine degree and clustering for fingerprint
        fingerprintsRef[v] = nodeDegree[v]:real / max(1, max reduce nodeDegree) +
                              clustering;
                              
        writeln("  Vertex ", v, ":");
        writeln("    - Degree: ", nodeDegree[v]);
        writeln("    - Clustering: ", clustering);
        writeln("    - Fingerprint: ", fingerprintsRef[v]);
    }
    
    state.timer.stop();
    
    writeln("=== Fingerprint Computation Complete ===");
    writeln("- Processed ", wavefrontRef.size, " vertices");
    writeln("- Time taken: ", state.timer.elapsed(), " seconds");
    writeln();
}
    /* Expands the wavefront based on structural diversity */
    proc expandWavefront(ref state: WavefrontState,
                        ref nodeNeighbours: [] domain(int)) {
            writeln("\n=== Expanding Wavefront ===");
            writeln("- Current size: ", state.wavefront.size);
        
        
        state.timer.clear();
        state.timer.start();
        
        var candidateSet: domain(int, parSafe=true);
        var expansionSize = state.wavefront.size; // Double the size each time
        
        // Collect neighbors of current wavefront
        forall v in state.wavefront with (ref candidateSet) {
            for u in nodeNeighbours[v] {
                if !state.wavefront.contains(u) && !state.sampledVertices.contains(u) {
                    candidateSet.add(u);
                }
            }
        }
        
            writeln("- Found ", candidateSet.size, " candidate vertices");
        
        
        // Select diverse candidates based on fingerprints
        if candidateSet.size > 0 {
            var selectedCount = 0;
            var lastFingerprint = -1.0;
            
            // Sort candidates by fingerprint difference
            var candidateArray: [0..#candidateSet.size] (real, int);
            var idx = 0;
            for v in candidateSet {
                candidateArray[idx] = (state.fingerprints[v], v);
                idx += 1;
            }
            sort(candidateArray);
            
            // Select vertices with diverse fingerprints
            for (fp, v) in candidateArray {
                if selectedCount >= expansionSize then break;
                if lastFingerprint < 0.0 || abs(fp - lastFingerprint) > 0.1 {
                    state.wavefront.add(v);
                    state.sampledVertices.add(v);
                    lastFingerprint = fp;
                    selectedCount += 1;
                }
            }
        }
        
        state.timer.stop();
        
            writeln("=== Wavefront Expansion Complete ===");
            writeln("- New wavefront size: ", state.wavefront.size);
            writeln("- Total sampled vertices: ", state.sampledVertices.size);
            writeln("- Time taken: ", state.timer.elapsed(), " seconds");
            writeln();
        
    }

    /* Processes current wavefront to find motifs */
    proc processWavefront(ref state: WavefrontState,
                         ref globalMotifCount: atomic int,
                         ref globalMotifSet: set(uint(64))) throws{
            writeln("\n=== Processing Wavefront for Motifs ===");
            writeln("- Vertices to process: ", state.wavefront.size);
        
        
        state.timer.clear();
        state.timer.start();
        
        // // Create state for motif exploration
        // var kState = new KavoshState(state.ASconfig.n, state.ASconfig.k, max reduce nodeDegree);
        
        // Process each vertex in wavefront
        forall v in state.wavefront with (ref globalMotifSet, ref globalMotifCount) {
            // Create a new KavoshState for this thread/vertex
            var localKavoshState = new KavoshState(state.ASconfig.n, state.ASconfig.k, max reduce nodeDegree);
  
            // Initialize for this vertex
            localKavoshState.setSubgraph(0, 0, 1);      // Set count to 1
            localKavoshState.setSubgraph(0, 1, v);      // Set the vertex
            localKavoshState.visited.clear();           // Clear visited for next vertex
            localKavoshState.visited.add(v);
            
            // Explore motifs from this vertex
            Explore(localKavoshState, v, 1, state.ASconfig.k - 1);
            
            // Update global counts
            globalMotifCount.add(localKavoshState.localsubgraphCount);
            globalMotifSet += localKavoshState.localmotifClasses;
            
                writeln("  Processed vertex ", v, ":");
                writeln("    - Found ", localKavoshState.localsubgraphCount, " motifs");
                writeln("    - New patterns: ", localKavoshState.localmotifClasses.size);
            
        }
        
        state.timer.stop();
        
            writeln("=== Wavefront Processing Complete ===");
            writeln("- Total motifs found: ", globalMotifCount.read());
            writeln("- Unique patterns: ", globalMotifSet.size);
            writeln("- Unique patterns: ", globalMotifSet);
            writeln("- Time taken: ", state.timer.elapsed(), " seconds");
            writeln();
        
    }

    /* Main ASWS sampling procedure */
    proc runASWS(n: int, k: int,
                 ref nodeDegree: [] int,
                 ref nodeNeighbours: [] domain(int),
                 ref globalMotifCount: atomic int,
                 ref globalMotifSet: set(uint(64))) throws{
        
        writeln("\n========== Starting ASWS Sampling ==========");
        
        // Initialize configuration
        var ASconfig = new ASWSConfig(n, k);
        var state = new WavefrontState(ASconfig);
        var totalTimer: stopwatch;
        totalTimer.start();
        
        // Step 1: Identify hubs
        identifyHubs(state, nodeDegree);
        
        // Step 2: Initialize wavefront
        initializeWavefront(state, nodeDegree);
        
        // Main sampling loop
        var iteration = 0;
        const maxIterations = 5;  // For prototype, we can adjust this
        
        while iteration < maxIterations {
            writeln("\nIteration ", iteration + 1, " of ", maxIterations);
            
            // Update fingerprints
            computeFingerprints(state, nodeNeighbours, nodeDegree);
            
            // Process current wavefront
            processWavefront(state, globalMotifCount, globalMotifSet);
            
            // Expand wavefront
            expandWavefront(state, nodeNeighbours);
            
            iteration += 1;
        }
        
        totalTimer.stop();
        
        writeln("\n========== ASWS Sampling Complete ==========");
        writeln("Final Statistics:");
        writeln("- Total vertices sampled: ", state.sampledVertices.size);
        writeln("- Final wavefront size: ", state.wavefront.size);
        writeln("- Total motifs found: ", globalMotifCount.read());
        writeln("- Unique patterns discovered: ", globalMotifSet.size);
        writeln("- Total time: ", totalTimer.elapsed(), " seconds");
        writeln("============================================\n");
    }

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


        proc generatePatternDirect(ref chosenVerts: [] int, ref nautyLabels: [] int, ref state: KavoshState): uint(64) throws {
            var pattern: uint(64) = 0;
            var pos = 0;

            // Generate pattern directly from vertex pairs
            for i in 0..#state.k {
                for j in 0..#state.k {
                    if i != j {
                        // Get vertices based on nauty labels
                        var u = chosenVerts[nautyLabels[i] + 1];
                        var w = chosenVerts[nautyLabels[j] + 1];
                        
                        // Check for edge and set bit
                        var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                        if eid != -1 {
                            pattern |= 1:uint(64) << pos;
                        }
                    }
                    pos += 1; // Increment position even when i == j to maintain ordering
                }
            }

            if logLevel == LogLevel.DEBUG {
                writeln("Generated pattern= ", pattern, " Nauty labels: ", nautyLabels, " Original chosenVerts: ", nodeMapGraphG1[chosenVerts]);
            }
            return pattern;
        }// End of generatePatternDirect

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
                state.localsubgraphCount += 1;

                if logLevel == LogLevel.DEBUG {
                    writeln("Found complete subgraph #", state.localsubgraphCount);
                    for l in 0..<state.k {
                        write("Level ", l, ": ");
                        for x in 1..state.getSubgraph(l, 0) {
                            write(state.getSubgraph(l, x), " ");
                        }
                        writeln();
                    }
                    writeln("Now we make adjMatrix to pass to Naugty");
                }

                var (adjMatrix, chosenVerts) = prepareNaugtyArguments(state);
                var results: [0..<state.k] int = 0..<state.k;

                var performCheck: int = 1; // Set to 1 to perform nauty_check, 0 to skip // DECIDE to add as input argument
                var verbose = 0;

                if logLevel == LogLevel.DEBUG { verbose = 1; } // Set to 1 to enable verbose logging for C++ side

                var status = c_nautyClassify(adjMatrix, motifSize, results, performCheck, verbose);

                if logLevel == LogLevel.DEBUG {
                    writeln("for subgraph = ",adjMatrix, "Nauty returned: ",
                                            results, " we are in the way to Classify!", "status = ", status);
                }

                // Handle potential errors
                if status != 0 {
                    writeln("Error: c_nautyClassify failed with status ", status);
                }

                var pattern = generatePatternDirect(chosenVerts, results, state);
        
                // Add to the set of patterns
                state.localmotifClasses.add(pattern);
                
                // Update local count for this pattern
                if state.localClassCounts.contains(pattern) {
                    state.localClassCounts[pattern] += 1;
                } else {
                    state.localClassCounts[pattern] = 1;
                }
        
                
                if logLevel == LogLevel.DEBUG {
                    //writeln("state.localmotifClasses: ", state.localmotifClasses);
                    writeln("Pattern ", pattern, " count updated to ", state.localClassCounts[pattern]);
                }
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
            
            writeln("\n=== Starting Pattern Verification ===");
            writeln(globalMotifSet.size, " patterns found before verification: ");
            writeln("Total patterns found before verification: ", globalMotifSet);
            writeln("globalCounts: ", globalCounts);
            writeln("globalCounts.size: ", globalCounts.size);

            writeln("Pattern counts before verification:");
            for pattern in globalCounts.keys() {
                writeln("Pattern ", pattern, ": ", globalCounts[pattern], " occurrences");
            }
            writeln("=====================================\n");
            
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


        ///////////////////////////////Main Code/////////////////////////////////////////////////


        // Enumerate: Iterates over all vertices as potential roots
        // and calls Explore to find all subgraphs of size k containing that root.
        proc Enumerate(n: int, k: int, maxDeg: int) throws {
            if logLevel == LogLevel.DEBUG {
                writeln("==============Enumerate called============");
            }

            // forall v in 0..<n with (ref globalMotifSet, ref globalMotifCount) {
            forall v in 0..<n-k+1 with (ref globalMotifSet, ref globalMotifCount, ref globalMotifMap) {
                if logLevel == LogLevel.DEBUG {
                    writeln("Root = ", v, " (", v+1, "/", n, ")");
                }

                var state = new KavoshState(n, k, maxDeg);

                // Initialize root vertex in subgraph
                state.setSubgraph(0, 0, 1);      // Set count to 1
                state.setSubgraph(0, 1, v);      // Set the vertex
                
                // Initialize visited for root vertex
                state.visited.clear();           // Clear visited for next vertex
                state.visited.add(v);

                // Start exploration from level 1 with k-1 vertices remaining to visit
                Explore(state, v, 1, state.k - 1);

                if logLevel == LogLevel.DEBUG {
                    writeln("Total Number of motifs: ", state.localsubgraphCount);
                    writeln("Number of Non-isomorphic Classes: ", state.localmotifClasses);
                    writeln();
                }

                // Update global counters and merge local counts
                globalMotifCount.add(state.localsubgraphCount);
                globalMotifSet += state.localmotifClasses;

                // Merge local counts into global counts
                syncVar.writeEF(true);  // acquire lock
                writeln("Thread merging patterns. Local patterns found: ", state.localClassCounts.size);

                for pattern in state.localClassCounts.keys() {
                    writeln("  Merging pattern: ", pattern, " count: ", state.localClassCounts[pattern]);

                    if !globalMotifMap.contains(pattern) {
                        globalMotifMap[pattern] = 0;
                    }
                    globalMotifMap[pattern] += state.localClassCounts[pattern];
                }
                syncVar.readFE();  // release lock
            }

            if logLevel == LogLevel.DEBUG {
                writeln("Enumerate: finished enumeration");
                writeln("Total motifs found: ", globalMotifCount.read());
                writeln("Unique patterns found: ", globalMotifSet.size);
                writeln("Pattern counts:");
                for pattern in globalMotifMap.keys() {
                    writeln("Pattern ", pattern, ": ", globalMotifMap[pattern]);
                }
            }
        }// End of Enumerate

    var timer:stopwatch;

    writeln("**********************************************************************");
    writeln("**********************************************************************");
    if doSampling {
        writeln("Using Adaptive Structural Wavefront Sampling");
        runASWS(g1.n_vertices, motifSize, nodeDegree, 
                   nodeNeighbours, globalMotifCount, globalMotifSet);

for elem in globalMotifSet {
  globalMotifMap[elem] = 1;
}
     

    } else {
        writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
        writeln("Maximum degree: ", maxDeg);
        // Complete enumeration
        Enumerate(g1.n_vertices, motifSize, maxDeg);
        writeln(" globalMotifSet = ", globalMotifSet);
        writeln(" globalMotifMap = ", globalMotifMap);

        }
        writeln("**********************************************************************");
        writeln("**********************************************************************");


    var (uniqueMotifClasses, finalMotifArr, motifCounts) = verifyPatterns(globalMotifSet, globalMotifMap, motifSize);

        var tempArr: [0..0] int;
        var srcPerMotif = makeDistArray(2*2, int);
        var dstPerMotif = makeDistArray(2*2, int);

        srcPerMotif[srcPerMotif.domain.low] = uniqueMotifClasses.size; //after verification
        srcPerMotif[srcPerMotif.domain.low +1] = globalMotifSet.size;   // before verification
        srcPerMotif[srcPerMotif.domain.low +2] = globalMotifCount.read(); // all motifs
        srcPerMotif[srcPerMotif.domain.low +3] = motifCounts.size;     // this is naive approach to return pattern 200 has 134 instances
        
        return (srcPerMotif, finalMotifArr, tempArr, tempArr);
    }// End of runMotifCounting

}// End of MotifCounting Module