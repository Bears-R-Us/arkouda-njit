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

    /* Calculate minimum required sample size based on graph properties */
    proc calculateRequiredSampleSize(n: int, k: int, maxDeg: int): int {
        const baseSize = max(
            30,  // Minimum for statistical significance
            (log2(n) * ((maxDeg: real) ** (k-1: real))): int

        );
        
        // Adjust for graph size
        const adjustedSize = min(
            baseSize,
            n / 10  // Cap at 10% of graph size
        );
        
        writeln("Sample size calculation:");
        writeln("- Base size: ", baseSize);
        writeln("- Adjusted size: ", adjustedSize);
        
        return adjustedSize;
    } 
    /* Manages the wavefront sampling state */
    class WavefrontState {
        var ASconfig: ASWSConfig;
        var wavefront: domain(int, parSafe=true);     // All selected vertices
        var newVertices: domain(int, parSafe=true);   // Only new vertices for this iteration
        var hubSet: domain(int, parSafe=true);
        var processedVertices: domain(int, parSafe=true); // All processed vertices
        var fingerprints: [0..#ASconfig.n] real;
        var timer: stopwatch;

        // Statistical tracking
        var minRequiredSize: int;
        var currentConfidence: real;
        var patternDiscoveryRate: [0..10] (int, int); // Circular buffer tracking pattern discovery. (patterns, samples) at each check point
        var rateIndex: atomic int;

        // Pattern discovery completeness
        var theoreticalTotalPatterns: int;    // Estimated total possible patterns
        var missProbability: atomic real;      // Current probability of missing patterns
        var coverageMetrics: [0..2] atomic real; // [structural, hub, pattern] coverage
        
        // Structural role tracking
        var roleDistribution: [0..3] atomic int;  // [hub, bridge, peripheral, other]
        var patternsByRole: [0..3] map(uint(64), atomic int); // Patterns found per role

        // Role classification
        var vertexRoles: [0..#ASconfig.n] int;  // 0:hub, 1:bridge, 2:peripheral
        var rolePatternCounts: [0..2] map(uint(64), atomic int);  // Patterns per role
        
        // Error bounds tracking
        var patternConfidenceIntervals: map(uint(64), (real, real));  // (lower, upper) bounds
        var significanceLevel: real;  // For statistical tests
        
        // Pattern stability
        var patternHistory: [0..4] set(uint(64));  // Last 5 pattern sets
        var stabilityScore: atomic real;
        var convergenceMetrics: [0..2] atomic real;  // [pattern, role, structural] convergence

        proc init(ASconfig: ASWSConfig, maxDeg: int) {
            this.ASconfig = ASconfig;
            this.wavefront = {1..0};
            this.newVertices = {1..0};
            this.hubSet = {1..0};
            this.processedVertices = {1..0};
            var a1: [0..#ASconfig.n] real;
            this.fingerprints = a1;
            this.timer = new stopwatch();
            this.minRequiredSize = calculateRequiredSampleSize(ASconfig.n, ASconfig.k, maxDeg);
            this.currentConfidence = 0.0;
            this.patternDiscoveryRate = [0..10]((0, 0));
            var a2: atomic int;
            this.rateIndex = a2;

            // Calculate theoretical patterns before init this
            const rawCount = 2**(ASconfig.k*(ASconfig.k-1));
            var factorial_result: bigint; // This is cool I never know LOL
            fac(factorial_result, ASconfig.k);  
            this.theoreticalTotalPatterns = (rawCount:real / factorial_result:real):int;


            // Initialize atomic variables
            var miss: atomic real;
            this.missProbability = miss;
            var metrics: [0..2] atomic real;
            this.coverageMetrics = metrics;
            var roles: [0..3] atomic int;
            this.roleDistribution = roles;
            
            // Initialize pattern maps
            this.patternsByRole = [i in 0..3] new map(uint(64), atomic int);

            init this;

            // Post-initialization settings
            this.missProbability.write(1.0);
            forall i in 0..2 do this.coverageMetrics[i].write(0.0);
            forall i in 0..3 do this.roleDistribution[i].write(0);
        }

/* Role Classification and Tracking */
proc classifyVertexRoles(ref nodeDegree: [] int, ref nodeNeighbours: [] domain(int)) {
    writeln("\n=== Classifying Vertex Roles ===");
    const maxDeg = max reduce nodeDegree;
    const avgDeg = (+ reduce nodeDegree) / nodeDegree.size;
    
    forall v in 0..#ASconfig.n {
        // Calculate clustering coefficient
        var neighbors = nodeNeighbours[v];
        var edgeCount = 0;
        var possibleEdges = neighbors.size * (neighbors.size - 1);
        
        if possibleEdges > 0 {
            for u in neighbors {
                for w in neighbors {
                    if u != w && nodeNeighbours[u].contains(w) {
                        edgeCount += 1;
                    }
                }
            }
        }
        
        var clustering = if possibleEdges > 0 
                        then edgeCount:real / possibleEdges:real 
                        else 0.0;
        
        // Classify role
        if nodeDegree[v] >= maxDeg * 0.7 {
            vertexRoles[v] = 0;  // Hub
        } else if clustering > 0.5 && nodeDegree[v] > avgDeg {
            vertexRoles[v] = 1;  // Bridge
        } else {
            vertexRoles[v] = 2;  // Peripheral
        }
    }
    
    // Print role distribution
    var roleCounts: [0..2] atomic int;
    forall v in 0..#ASconfig.n with (ref roleCounts) {
        roleCounts[vertexRoles[v]].add(1);
    }
    
    writeln("Role distribution:");
    writeln("- Hubs: ", roleCounts[0].read());
    writeln("- Bridges: ", roleCounts[1].read());
    writeln("- Peripheral: ", roleCounts[2].read());
}

/* Error Bounds Calculation */
proc updateErrorBounds(patterns: set(uint(64))) {
    // Calculate confidence intervals for each pattern
    const z = 1.96;  // 95% confidence level
    const n = processedVertices.size;
    
    for pattern in patterns {
        var count = if rolePatternCounts[0].contains(pattern) then
                     (+ reduce [role in 0..2] rolePatternCounts[role][pattern].read())
                   else 0;
        
        // Calculate standard error
        var p = count:real / n:real;
        var stderr = sqrt((p * (1.0 - p)) / n);
        
        // Update confidence intervals
        patternConfidenceIntervals[pattern] = (
            max(0.0, p - z * stderr),
            min(1.0, p + z * stderr)
        );
    }
}

/* Pattern Stability Analysis */
proc updatePatternStability(patterns: set(uint(64))) {
    // Shift history
    for i in 1..4 {
        patternHistory[i-1] = patternHistory[i];
    }
    patternHistory[4] = patterns;
    
    // Calculate stability metrics
    if processedVertices.size > minRequiredSize {
        var patternStability = calculatePatternStability();
        var roleStability = calculateRoleStability();
        var structuralStability = calculateStructuralStability();
        
        convergenceMetrics[0].write(patternStability);
        convergenceMetrics[1].write(roleStability);
        convergenceMetrics[2].write(structuralStability);
        
        stabilityScore.write((patternStability + roleStability + structuralStability) / 3.0);
    }
}



proc calculateRoleStability(): real {
    var stability: [0..2] real;
    
    // Calculate stability for each role
    for role in 0..2 {
        var patternCounts = rolePatternCounts[role];
        var totalPatterns = + reduce [p in patternCounts.keys()] patternCounts[p].read();
        if totalPatterns > 0 {
            stability[role] = min(1.0, totalPatterns:real / theoreticalTotalPatterns:real);
        }
    }
    
    return (+ reduce stability) / 3.0;
}

proc calculateStructuralStability(): real {
    // Measure how well we've covered different structural regions
    var coverage = coverageMetrics[0].read();
    var hubCoverage = coverageMetrics[1].read();
    var patternCoverage = coverageMetrics[2].read();
    
    return (coverage + hubCoverage + patternCoverage) / 3.0;
}

/* Enhanced Pattern Discovery Completeness Check */
proc hasCompletePatternDiscovery(): bool {
    // Check all theoretical guarantees
    const hasStability = stabilityScore.read() > 0.9;
    const hasCoverage = (+ reduce [m in convergenceMetrics] m.read()) / 3.0 > 0.95;
    const lowError = missProbability.read() < 0.05;
    
    writeln("\n=== Pattern Discovery Completeness Check ===");
    writeln("- Pattern Stability: ", stabilityScore.read());
    writeln("- Coverage Score: ", (+ reduce [m in convergenceMetrics] m.read()) / 3.0);
    writeln("- Miss Probability: ", missProbability.read());
    
    return hasStability && hasCoverage && lowError;
}

        // Calculate theoretical upper bound on possible patterns
        proc calculateTheoreticalPatterns(k: int, maxDeg: int): int {
            const rawCount = 2**(k*(k-1));
            var factorial_result: bigint;
            fac(factorial_result, k);
            return (rawCount:real / factorial_result.toReal():real):int;
        }

        /* Track pattern discovery progress */
        proc updatePatternStats(numPatterns: int) {
            const idx = rateIndex.fetchAdd(1) % 11;  // Circular buffer
            patternDiscoveryRate[idx] = (numPatterns, wavefront.size);
            
            // Calculate discovery rate
            if idx > 0 {
                const prevPatterns = patternDiscoveryRate[(idx-1) % 11][0];
                const newPatterns = numPatterns - prevPatterns;
                
                if newPatterns > 0 {
                    writeln("Pattern discovery update:");
                    writeln("- New patterns found: ", newPatterns);
                    writeln("- Current sample size: ", wavefront.size);
                    writeln("- Discovery rate: ", (newPatterns:real / wavefront.size:real));
                }
            }
        }

        /* Check if sampling is adequate */
        proc isSamplingAdequate(): bool {
            // Basic size check
            if wavefront.size < minRequiredSize {
                return false;
            }
            
            // Check pattern discovery rate
            const idx = rateIndex.read() % 11;
            if idx > 2 {  // Need at least 3 points to check rate
                const rate1 = patternDiscoveryRate[(idx-1) % 11][0] - patternDiscoveryRate[(idx-2) % 11][0];
                const rate2 = patternDiscoveryRate[idx][0] - patternDiscoveryRate[(idx-1) % 11][0];
                
                // If discovery rate drops significantly, might be adequate
                if rate2 < rate1 / 2 {
                    return true;
                }
            }
            
            return false;
        }

        /* Calculate current confidence level */
        proc updateConfidence() {
            const coverage = wavefront.size:real / ASconfig.n:real;
            const patternStability = calculatePatternStability();
            
            // Combine coverage and stability for confidence
            currentConfidence = min(
                coverage * patternStability,
                0.95  // Cap at 95%
            );
            
            writeln("Confidence update:");
            writeln("- Coverage: ", coverage);
            writeln("- Pattern stability: ", patternStability);
            writeln("- Current confidence: ", currentConfidence);
        }

        /* Helper to calculate pattern stability */
        proc calculatePatternStability(): real {
            var stability = 0.0;
            const latest = patternHistory[4];
            
            // Compare with previous pattern sets
            for i in 0..3 {
                if patternHistory[i].size > 0 {
                    var intersection = latest & patternHistory[i];
                    var p_union = latest | patternHistory[i];
                    stability += intersection.size:real / p_union.size:real;
                }
            }
            
            return stability / 4.0;
        }
        // Update pattern discovery metrics
        proc updatePatternDiscoveryMetrics(newPatterns: set(uint(64))) {
            // Update miss probability based on Theorem 1
            const coverage = (newPatterns.size:real / theoreticalTotalPatterns:real);
            const newMissProb = (1.0 - coverage) * 
                            exp(-processedVertices.size:real / (ASconfig.k * wavefront.size));
            missProbability.write(newMissProb);

            // Update structural coverage
            updateStructuralCoverage(newPatterns.size);

            if logLevel == LogLevel.DEBUG {
                writeln("\n=== Pattern Discovery Metrics Update ===");
                writeln("- Coverage: ", coverage);
                writeln("- Miss Probability: ", newMissProb);
                writeln("- Processed Vertices: ", processedVertices.size);
                writeln("=====================================\n");
            }
        }

        // Calculate structural coverage based on vertex roles
        proc updateStructuralCoverage(numPatterns: int) {
            // Structural coverage (based on processed vertices)
            const structuralCoverage = min(1.0, 
                processedVertices.size:real / ASconfig.n:real);
            
            // Hub coverage (based on hub participation)
            const hubCoverage = if hubSet.size > 0 
                then min(1.0, (processedVertices.size:real / hubSet.size:real))
                else 0.0;
            
            // Pattern coverage (based on found vs theoretical patterns)
            const patternCoverage = min(1.0, 
                numPatterns:real / theoreticalTotalPatterns:real);
            
            coverageMetrics[0].write(structuralCoverage);
            coverageMetrics[1].write(hubCoverage);
            coverageMetrics[2].write(patternCoverage);
        }

        // Check if we have sufficient pattern discovery guarantees
        proc hasPatternDiscoveryGuarantees(epsilon: real = 0.05): bool {
            // Three conditions must be met:
            // 1. Low probability of missing patterns
            // 2. Good overall coverage
            // 3. Sufficient hub representation
            
            const missProb = missProbability.read();
            const avgCoverage = (+ reduce [m in coverageMetrics] m.read()) / 3.0;
            const hubCoverage = coverageMetrics[1].read();
            
            return missProb <= epsilon && 
                avgCoverage >= 0.95 && 
                hubCoverage >= 0.9;
        }

        // Print detailed coverage statistics
        proc printCoverageStats() {
            writeln("\n=== Pattern Discovery Completeness Stats ===");
            writeln("Theoretical total patterns: ", theoreticalTotalPatterns);
            writeln("Current miss probability: ", missProbability.read());
            writeln("Coverage metrics:");
            writeln("  - Structural coverage: ", coverageMetrics[0].read());
            writeln("  - Hub coverage: ", coverageMetrics[1].read());
            writeln("  - Pattern coverage: ", coverageMetrics[2].read());
            writeln("Role distribution:");
            for i in 0..3 {
                writeln("  - Role ", i, ": ", roleDistribution[i].read(), " vertices");
            }
            writeln("========================================\n");
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
        //var localClassCounts: map(uint(64), int, parSafe=false);

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
        verbose: int(64)
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
        var globalMotifSet: set(uint(64), parSafe=true);
        // Initiate it to 0
        globalMotifCount.write(0);
        // A global map to track pattern counts across all threads
        var globalMotifMap: map(uint(64), int);
        //var syncVar: sync bool;

        var Sampling: bool = false;
        if doSampling == 1 then Sampling = true;
    
        var doMOtifDetail: bool = true;
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////



   /* Identifies hub vertices based on degree */
proc identifyHubs(ref state: WavefrontState, nodeDegree: [] int) {
    if logLevel == LogLevel.DEBUG {
        writeln("\n=== Starting Hub Identification ===");
        writeln("- Graph size: ", state.ASconfig.n);
        writeln("- Hub percentile: ", state.ASconfig.hubPercentile);
    }    
    state.timer.start();
    
    // Create a copy for sorting
    var sortedDegrees = nodeDegree;
    sort(sortedDegrees, new ReverseComparator());
    
    // Calculate hub threshold
    var hubIndex = (state.ASconfig.n * (1.0 - state.ASconfig.hubPercentile)): int;
    var hubThreshold = sortedDegrees[hubIndex];
    
    
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
    writeln("- Degree distribution:");
    writeln("  * Max degree: ", sortedDegrees[0]);
    writeln("  * Median degree: ", sortedDegrees[sortedDegrees.size/2]);
    writeln("  * Min degree: ", sortedDegrees[sortedDegrees.size-1]);
    writeln("- Hub threshold: ", hubThreshold);
    writeln("- Identified ", hubCount, " hubs");
    writeln("- hubSet.size: ", state.hubSet.size);
    writeln("- Time taken: ", state.timer.elapsed(), " seconds");
    writeln();
}

/* Calculates optimal initial sample size based on graph properties */
proc calculateInitialSize(n: int, k: int, hubCount: int, nodeDegree: [] int): int {
    // Get degree statistics
    const maxDeg = max reduce nodeDegree;
    const avgDeg = (+ reduce nodeDegree) / n;
    
    // Base size considering graph properties
    const baseSize = ((log2(n) * k * avgDeg):real / maxDeg:real):int;
    
    // Consider hub count in calculation
    const sizeFromHubs = max(hubCount, hubCount * 2);
    
    // Take maximum of calculated sizes with bounds
    const initialSize = max(
        30,  // Minimum statistical significance
        max(
            baseSize,
            sizeFromHubs
        )
    );

    // Apply upper bound
    return min(initialSize, n / 5);  // Cap at 20% of graph size
}

    /* Initializes the wavefront with strategic vertices */
    proc initializeWavefront(ref state: WavefrontState, nodeDegree: [] int) {
        if logLevel == LogLevel.DEBUG {
            writeln("\n=== Initializing Wavefront ===");
        }
        // Calculate dynamic initial size
        const initialSize = calculateInitialSize(
            state.ASconfig.n, 
            state.ASconfig.k,
            state.hubSet.size,
            nodeDegree
        );
        
        writeln("- Calculated initial size: ", initialSize);
        writeln("- Based on:");
        writeln("  * Graph size: ", state.ASconfig.n);
        writeln("  * Motif size: ", state.ASconfig.k);
        writeln("  * Hub count: ", state.hubSet.size);
        writeln("  * Max degree: ", max reduce nodeDegree);
        writeln("  * Avg degree: ", (+ reduce nodeDegree) / state.ASconfig.n);
        
        state.timer.clear();
        state.timer.start();
        
        // First, add all hubs
        state.wavefront = state.hubSet;
        state.newVertices = state.hubSet; // Initially, all hubs are new
        const hubCount = state.hubSet.size;
        writeln("- Added ", hubCount, " hubs to wavefront");
        
        if state.wavefront.size < initialSize {
            const remainingNeeded = initialSize - state.wavefront.size;
            writeln("- Selecting ", remainingNeeded, " additional vertices");
            
            // Create degree ranges for diverse selection
            var maxDeg = max reduce nodeDegree;
            var degreeBins: [0..4] domain(int, parSafe=true);
            
            // Categorize non-hub vertices by degree
            forall v in 0..#state.ASconfig.n with (ref degreeBins) {
                if !state.hubSet.contains(v) {
                    var bin = (nodeDegree[v] * 5 / maxDeg): int;
                    bin = min(4, bin);
                    degreeBins[bin].add(v);
                }
            }
            
            // Select from each bin
            var rng = new randomStream(real);
            const perBin = (remainingNeeded / 5): int;
            
            for bin in 0..4 {
                var selected = 0;
                for v in degreeBins[bin] {
                    if selected >= perBin then break;
                    if rng.next() < 0.5 {
                        state.wavefront.add(v);
                        state.newVertices.add(v);
                        selected += 1;
                    }
                }
            }
        }
        
        state.timer.stop();
        writeln("=== Initial Wavefront Statistics ===");
        writeln("- Target size: ", initialSize);
        writeln("- Actual size: ", state.wavefront.size);
        writeln("- New vertices: ", state.newVertices.size);
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
    
    ref fingerprintsRef = state.fingerprints;
    ref wavefrontRef = state.wavefront;
    
    const maxDeg = max reduce nodeDegree;
    
    forall v in wavefrontRef with (ref fingerprintsRef) {
        var degree = nodeDegree[v];
        var possibleEdges = degree * (degree - 1);
        
        // Compute enhanced fingerprint
        var fp = 0.0;
        
        // Normalized degree contribution (40%)
        fp += (degree:real / maxDeg:real) * 0.4;
        
        // Local clustering contribution (30%)
        var clustering = if possibleEdges > 0 then degree:real / possibleEdges:real else 0.0;
        fp += clustering * 0.3;
        
        // Neighbor diversity contribution (30%)
        var neighborDegreeSum = 0.0;
        var neighborCount = 0;
        for u in nodeNeighbours[v] {
            neighborDegreeSum += nodeDegree[u]:real / maxDeg:real;
            neighborCount += 1;
        }
        var neighborDiversity = if neighborCount > 0 then neighborDegreeSum / neighborCount else 0.0;
        fp += neighborDiversity * 0.3;
        
        fingerprintsRef[v] = fp;
    }
    
    state.timer.stop();
    writeln("=== Fingerprint Computation Complete ===");
    writeln("- Processed ", wavefrontRef.size, " vertices");
    writeln("- Time taken: ", state.timer.elapsed(), " seconds");
    writeln();
}

/* Expands the wavefront based on structural diversity */
proc expandWavefront(ref state: WavefrontState,
                    ref nodeNeighbours: [] domain(int),
                    ref nodeDegree: [] int) {
    const currentSize = state.wavefront.size;
    writeln("\n=== Expanding Wavefront ===");
    writeln("- Current wavefront size: ", currentSize);
    
    state.timer.clear();
    state.timer.start();
    
    // Clear previous new vertices
    state.newVertices.clear();
    
    // Calculate adaptive expansion size
    const remainingVertices = state.ASconfig.n - currentSize;
    const expansionSize = max(
        min(
            (currentSize * 0.2): int,    // 20% growth
            remainingVertices / 4         // Don't exceed 25% of remaining vertices
        ),
        min(
            50,                          // Minimum meaningful expansion
            remainingVertices            // Don't exceed available vertices
        )
    );
    
    writeln("- Target expansion size: ", expansionSize);
    
    // Collect candidates
    var hubNeighbors: domain(int, parSafe=true);
    var otherCandidates: domain(int, parSafe=true);
    
    // Collect neighbors more strategically
    forall hub in state.hubSet with (ref hubNeighbors) {
        for neighbor in nodeNeighbours[hub] {
            if !state.wavefront.contains(neighbor) && 
               !state.processedVertices.contains(neighbor) {
                hubNeighbors.add(neighbor);
            }
        }
    }
    
    forall v in state.wavefront with (ref otherCandidates) {
        for neighbor in nodeNeighbours[v] {
            if !state.wavefront.contains(neighbor) && 
               !state.processedVertices.contains(neighbor) &&
               !hubNeighbors.contains(neighbor) {
                otherCandidates.add(neighbor);
            }
        }
    }
    
    // Enhanced vertex selection
    proc selectDiverse(candidates: domain(int, parSafe=true), count: int) {
        if candidates.size == 0 then return;
        
        var targetPerRange = max(1, count / 10);
        var rangeSelections: [0..9] atomic int;
        
        // Create candidate array with scores
        var candidateScores: [0..#candidates.size] (real, real, int); // (fingerprint, score, vertex)
        var idx = 0;
        
        // Score candidates
        for v in candidates {
            var fp = state.fingerprints[v];
            var score = 0.0;
            
            // Base score from fingerprint
            score += fp * 0.4;
            
            // Structural diversity score
            score += (nodeDegree[v]:real / (max reduce nodeDegree):real) * 0.3;
            
            // Distance from existing samples
            var minDistance = max(real);
            for u in state.processedVertices {
                var fpDist = abs(fp - state.fingerprints[u]);
                minDistance = min(minDistance, fpDist);
            }
            score += minDistance * 0.3;
            
            candidateScores[idx] = (fp, score, v);
            idx += 1;
        }
        
        // Sort by score
        sort(candidateScores, comparator=new ReverseComparator());
        
        // First pass: fill ranges evenly
        var selectedCount = 0;
        for (fp, score, v) in candidateScores {
            if selectedCount >= count then break;
            
            var fprange = min(9, (fp * 10):int);
            if rangeSelections[fprange].read() < targetPerRange {
                state.wavefront.add(v);
                state.newVertices.add(v);
                rangeSelections[fprange].add(1);
                selectedCount += 1;
            }
        }
        
        // Second pass: fill remaining slots
        if selectedCount < count {
            for (fp, score, v) in candidateScores {
                if selectedCount >= count then break;
                if !state.wavefront.contains(v) {
                    state.wavefront.add(v);
                    state.newVertices.add(v);
                    selectedCount += 1;
                }
            }
        }
        
        writeln("  Selected ", selectedCount, " diverse vertices");
        writeln("  Range coverage:");
        for i in 0..9 {
            writeln("    Range ", i, ": ", rangeSelections[i].read(), " vertices");
        }
    }
    
    // Balanced selection from different sources
    var hubNeighborTarget = (expansionSize * 0.4): int;
    var diverseTarget = (expansionSize * 0.4): int;
    var randomTarget = expansionSize - hubNeighborTarget - diverseTarget;
    
    selectDiverse(hubNeighbors, hubNeighborTarget);
    selectDiverse(otherCandidates, diverseTarget);
    
    // Random selection with minimal constraints
    if randomTarget > 0 {
        var rng = new randomStream(real);
        var remainingCandidates = otherCandidates - state.newVertices;
        var selectedRandom = 0;
        
        for v in remainingCandidates {
            if selectedRandom >= randomTarget then break;
            if rng.next() < 0.3 { // Increased selection probability
                state.wavefront.add(v);
                state.newVertices.add(v);
                selectedRandom += 1;
            }
        }
        writeln("  Added ", selectedRandom, " random vertices");
    }
    
    state.timer.stop();
    writeln("=== Wavefront Expansion Complete ===");
    writeln("- Previous size: ", currentSize);
    writeln("- New wavefront size: ", state.wavefront.size);
    writeln("- Newly added vertices: ", state.newVertices.size);
    writeln("- Time taken: ", state.timer.elapsed(), " seconds");
    writeln();
}



    /* Main ASWS sampling procedure which Processes current wavefront to find motifs */

proc processWavefront(ref state: WavefrontState,
                     ref globalMotifCount: atomic int,
                     ref globalMotifSet: set(uint(64))) throws {
    
    writeln("\n=== Processing New Vertices ===");
    writeln("- Total vertices in wavefront: ", state.wavefront.size);
    writeln("- Processing new vertices: ", state.newVertices.size);
    
    state.timer.clear();
    state.timer.start();
    
    // Only process new vertices
    forall v in state.newVertices with (ref globalMotifSet, ref globalMotifCount) {
        var localKavoshState = new KavoshState(state.ASconfig.n, state.ASconfig.k, max reduce nodeDegree);
        
        // Initialize for this vertex
        localKavoshState.setSubgraph(0, 0, 1);
        localKavoshState.setSubgraph(0, 1, v);
        localKavoshState.visited.clear();
        localKavoshState.visited.add(v);
        
        // Explore motifs from this vertex
        Explore(localKavoshState, v, 1, state.ASconfig.k - 1);
        
        // Update global counts
        globalMotifCount.add(localKavoshState.localsubgraphCount);
        globalMotifSet += localKavoshState.localmotifClasses;
        if logLevel == LogLevel.DEBUG {
            writeln("  Processed vertex ", v, ":");
            writeln("    - Found ", localKavoshState.localsubgraphCount, " motifs");
            writeln("    - New patterns: ", localKavoshState.localmotifClasses.size);
        }
    }
    
    // Mark these vertices as processed
    state.processedVertices += state.newVertices;
    
    // Update pattern discovery metrics
    state.updatePatternDiscoveryMetrics(globalMotifSet);
    
    state.timer.stop();
    writeln("=== Wavefront Processing Complete ===");
    writeln("- Total motifs found: ", globalMotifCount.read());
    writeln("- Unique patterns: ", globalMotifSet.size);
    writeln("- Processed Vertices: ", state.processedVertices.size);
    writeln("- Time taken: ", state.timer.elapsed(), " seconds");
    
    // Print pattern discovery stats if debug or significant change
    if logLevel == LogLevel.DEBUG || state.hasPatternDiscoveryGuarantees() {
        state.printCoverageStats();
    }
    
    writeln();
}

/* Main ASWS sampling procedure */
proc runASWS(n: int, k: int,
             ref nodeDegree: [] int,
             ref nodeNeighbours: [] domain(int),
             ref globalMotifCount: atomic int,
             ref globalMotifSet: set(uint(64))) throws {
    
    writeln("\n========== Starting ASWS Sampling ==========");
    
    // Initialize configuration
    var ASconfig = new ASWSConfig(n, k);
    var maxDeg = max reduce nodeDegree;
    var state = new WavefrontState(ASconfig, maxDeg);
    var totalTimer: stopwatch;
    totalTimer.start();
    
    // Step 1: Identify hubs
    identifyHubs(state, nodeDegree);
    
    // Step 2: Initialize wavefront
    initializeWavefront(state, nodeDegree);
    
    // Main sampling loop
    var iteration = 0;
    const maxIterations = 5;  // For prototype, we can adjust this
    
    while (!state.isSamplingAdequate() && iteration < maxIterations && !state.hasPatternDiscoveryGuarantees()) {
        writeln("\nIteration ", iteration + 1, " of ", maxIterations);
        
        // Update fingerprints
        computeFingerprints(state, nodeNeighbours, nodeDegree);
        
        // Process current wavefront
        processWavefront(state, globalMotifCount, globalMotifSet);
        
        // Expand wavefront
        expandWavefront(state, nodeNeighbours, nodeDegree);

        // Update statistics
        state.updatePatternStats(globalMotifSet.size);
        state.updateConfidence();
        
        iteration += 1;
    }
    
    totalTimer.stop();
    
    writeln("\n========== ASWS Sampling Complete ==========");
    writeln("Final Statistics:");
    writeln("- Total vertices sampled: ", state.wavefront.size);
    writeln("- Total motifs found: ", globalMotifCount.read());
    writeln("- Unique patterns discovered: ", globalMotifSet.size);
    writeln("- Pattern discovery guarantees met: ", state.hasPatternDiscoveryGuarantees());
    writeln("- Total time: ", totalTimer.elapsed(), " seconds");
    
    // Final pattern discovery stats
    state.printCoverageStats();
    
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
                
                // // Update local count for this pattern
                // if state.localClassCounts.contains(pattern) {
                //     state.localClassCounts[pattern] += 1;
                // } else {
                //     state.localClassCounts[pattern] = 1;
                // }
        
                
                // if logLevel == LogLevel.DEBUG {
                //     //writeln("state.localmotifClasses: ", state.localmotifClasses);
                //     writeln("Pattern ", pattern, " count updated to ", state.localClassCounts[pattern]);
                // }
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
            //forall v in 0..<n-k+1 with (ref globalMotifSet, ref globalMotifCount, ref globalMotifMap) {
            forall v in 0..<n-k+1 with (ref globalMotifSet, ref globalMotifCount) {
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

                // // Merge local counts into global counts
                // syncVar.writeEF(true);  // acquire lock
                // if logLevel == LogLevel.DEBUG {
                //     writeln("Thread merging patterns. Local patterns found: ", state.localClassCounts.size);
                // }

                // for pattern in state.localClassCounts.keys() {
                //     writeln("  Merging pattern: ", pattern, " count: ", state.localClassCounts[pattern]);

                //     if !globalMotifMap.contains(pattern) {
                //         globalMotifMap[pattern] = 0;
                //     }
                //     globalMotifMap[pattern] += state.localClassCounts[pattern];
                // }
                // syncVar.readFE();  // release lock
            }

            if logLevel == LogLevel.DEBUG {
                writeln("Enumerate: finished enumeration");
                writeln("Total motifs found: ", globalMotifCount.read());
                writeln("Unique patterns found: ", globalMotifSet.size);
                // writeln("Pattern counts:");
                // for pattern in globalMotifMap.keys() {
                //     writeln("Pattern ", pattern, ": ", globalMotifMap[pattern]);
                // }
            }
        }// End of Enumerate

    var timer:stopwatch;

    writeln("**********************************************************************");
    writeln("**********************************************************************");
        writeln("Graph loaded:");
        writeln("Number of nodes: ", g1.n_vertices);
        writeln("Number of edges: ", g1.n_edges);
        writeln("Number of cores (max task parallelism): ", here.maxTaskPar);

    if Sampling {
        writeln("Using Adaptive Structural Wavefront Sampling");


        runASWS(g1.n_vertices, motifSize, nodeDegree, 
                   nodeNeighbours, globalMotifCount, globalMotifSet);


     

    } else {
        writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
        writeln("Maximum degree: ", maxDeg);
        // Complete enumeration
        Enumerate(g1.n_vertices, motifSize, maxDeg);
        writeln(" globalMotifSet = ", globalMotifSet);
        writeln(" globalMotifCount = ", globalMotifCount.read());

        }
        writeln("**********************************************************************");
        writeln("**********************************************************************");

for elem in globalMotifSet {
  globalMotifMap[elem] = 1;
}

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