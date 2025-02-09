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

/*
 * Statistics tracking for each stratum
 */
record StratumStatistics {
    var count: atomic int;
    var sum: atomic real;
    var sumSquares: atomic real;
    var maxValue: atomic real;
    
    proc updateStats(motifCount: int, classCount: int, scaleFactor: real) {
        count.add(1);
        sum.add(motifCount:real);
        sumSquares.add(motifCount:real * motifCount:real);
        
        var current = maxValue.read();
        while motifCount:real > current {
            maxValue.compareAndSwap(current, motifCount:real);
            current = maxValue.read();
        }
    }
    
    proc getMean(): real {
        const c = count.read();
        if c == 0 then return 0.0;
        return sum.read() / c;
    }
    
    proc getVariance(): real {
        const c = count.read();
        if c <= 1 then return 0.0;
        const mean = getMean();
        return (sumSquares.read() - c * mean * mean) / (c - 1);
    }
    
    proc getStandardError(): real {
        const c = count.read();
        if c == 0 then return 0.0;
        return sqrt(getVariance() / c);
    }
}
/* 
 * Configuration record for sampling parameters
 * Allows users to customize all aspects of the sampling process
 */
record SamplingConfig {
    /* Statistical parameters */
    var confidenceLevel: real = 0.95;    // Confidence level (e.g., 0.95 for 95%)
    var marginOfError: real = 0.1;       // Desired margin of error (e.g., 0.1 for ±10%)
    var pilotFraction: real = 0.05;     // Fraction of vertices to sample in pilot (e.g., 0.02 for 2%)
                                        // Just a hunch for now. It should be adjusted based on tests
                                        // For small graphs (< 1000 nodes): 0.02-0.05
                                        // For medium graphs (1000-100K nodes): 0.01-0.02
                                        // For large graphs (>100K nodes): 0.001-0.01
    
    /* Stratification parameters */
    var numStrata: int = 3;              // Number of strata to use
    var strategyType: string = "degree"; // Stratification strategy: "degree", "community", or "uniform"
    var minSampleSize: int = 30;         // Minimum samples per stratum for statistical validity
    
    /* Error handling parameters */
    var minStratumSize: int = 100;       // Minimum stratum size for valid sampling
    var maxRetries: int = 3;             // Maximum retries for failed sampling attempts
    
    /* Validation */
    proc isValid() {
        if confidenceLevel <= 0.0 || confidenceLevel >= 1.0 then return false;
        if marginOfError <= 0.0 || marginOfError >= 1.0 then return false;
        if pilotFraction <= 0.0 || pilotFraction >= 1.0 then return false;
        if numStrata < 1 then return false;
        if minSampleSize < 1 then return false;
        if minStratumSize < minSampleSize then return false;
        if maxRetries < 1 then return false;
        return true;
    }
}

/*
 * Enhanced Sampling State class
 * Manages the state of the sampling process including stratification and variance estimation
 */
class SamplingState {
    var Sconfig: SamplingConfig;
    var strata: [0..#Sconfig.numStrata] Stratum;
    var D: domain(1);                   // Domain for atomic array
    var localVariance: [D] atomic real; // Atomic array using domain
    var samplingErrors: domain(int);
    
    /* Sampling statistics */
    var totalSampledVertices: atomic int;
    var successfulSamples: atomic int;
    var failedSamples: atomic int;
    
    proc init(Sconfig: SamplingConfig) {
        this.Sconfig = Sconfig;
        this.strata = [i in 0..#Sconfig.numStrata] new Stratum(i);
        this.D = {0..#Sconfig.numStrata};
        init this;
        
        // Initialize atomic values
        forall l in localVariance do l.write(0.0);
        
        // Initialize other atomics
        this.totalSampledVertices.write(0);
        this.successfulSamples.write(0);
        this.failedSamples.write(0);
        
        this.samplingErrors = {1..0};
    }
    
    /* Rest of the methods remain the same */
    proc recordError(stratumId: int): bool {
        this.failedSamples.add(1);
        if this.samplingErrors.contains(stratumId) {
            var currentRetries = this.samplingErrors.size;
            return currentRetries < this.Sconfig.maxRetries;
        }
        this.samplingErrors.add(stratumId);
        return true;
    }
    
    proc validateResults(): (bool, string) {
        var totalSamples = this.successfulSamples.read();
        if totalSamples < Sconfig.minSampleSize {
            return (false, "Insufficient total samples: " + totalSamples:string + 
                " < minimum required: " + Sconfig.minSampleSize:string);
        }
        
        var hasError = false;
        var errorMsg: string;
        forall stratum in strata with (ref errorMsg, ref hasError) {
            if stratum.sampleSize.read() < Sconfig.minSampleSize {
                hasError = true;
                errorMsg += "Stratum " + stratum.id:string + " has insufficient samples. ";
            }
        }
        if hasError then return (false, errorMsg);
        
        var failureRate = (this.failedSamples.read():real / 
                        (this.successfulSamples.read() + this.failedSamples.read()));
        if failureRate > 0.1 {  // More than 10% failure rate
            return (false, "High sampling failure rate: " + (failureRate*100):string + "%");
        }
        
        return (true, "");
    }
}

/*
 * Enhanced Stratum record with additional error checking and statistics
 */
record Stratum {
    var id: int;
    var size: atomic int;
    var sampleSize: atomic int;
    var vertices: domain(int, parSafe=true);
    var validSamples: atomic int;
    var samplingErrors: atomic int;
    
    /*
     * Checks if the stratum is valid for sampling
     * Returns: (bool, string) tuple - (isValid, error message)
     */
    proc isValid(Sconfig: SamplingConfig): (bool, string) {
        if size.read() < Sconfig.minStratumSize {
            return (false, "Stratum " + id:string + " size (" + size.read():string + 
                   ") below minimum required (" + Sconfig.minStratumSize:string + ")");
        }
        if vertices.size < Sconfig.minSampleSize {
            return (false, "Insufficient vertices in stratum " + id:string + 
                   " for minimum sample size");
        }
        return (true, "");
    }
}
/*
 * Stratifies the graph based on the chosen strategy
 * Returns: A new SamplingState instance or throws on invalid configuration
 */
proc stratifyGraph(n: int, ref nodeDegree: [] int, Sconfig: SamplingConfig) throws {
    if !Sconfig.isValid() {
        throw new Error("Invalid sampling configuration");
    }
    
    var samplingState = new owned SamplingState(Sconfig);
    
    select Sconfig.strategyType {
        when "degree" {
            stratifyByDegree(n, nodeDegree, samplingState);
        }
        // when "community" {
        //     stratifyByCommunity(n, nodeDegree, samplingState);
        // }
        when "uniform" {
            stratifyUniformly(n, samplingState);
        }
        otherwise {
            throw new Error("Unknown stratification strategy: " + Sconfig.strategyType);
        }
    }
    
    // Validate strata
    for stratum in samplingState.strata {
        var (isValid, errorMsg) = stratum.isValid(Sconfig);
        if !isValid {
            writeln("Warning: ", errorMsg);
            if !samplingState.recordError(stratum.id) {
                throw new Error("Max retries exceeded for stratum " + stratum.id:string);
            }
        }
    }
    
    return samplingState;
}

    class KavoshState {
        var n: int;
        var k: int;
        var maxDeg: int;
        var visited: domain(int, parSafe=false);

        // Convert 2D arrays to 1D
        // For subgraph: original was [0..<k, 0..<k+1]
        var subgraph: [0..#(k * (k+1))] int;  

        // For childSet: original was [0..<k, 0..(maxDeg*k)+1]
        var childSet: [0..#(k * ((maxDeg*k)+2))] int;

        // For indexMap: original was [0..<k, 0..(maxDeg*k)+1]
        var indexMap: [0..#(k * ((maxDeg*k)+2))] int;

        var localsubgraphCount: int;
        var localmotifClasses: set(uint(64), parSafe=false);

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
        }
    }// End of KavoshState


    // C header and object files.
    require "NautyProject/bin/nautyClassify.o",
            "NautyProject/include/nautyClassify.h",
            //"NautyProject/include/nauty.h",
            "NautyProject/bin/nauty.o",
            "NautyProject/bin/naugraph.o",
            "NautyProject/bin/nautil.o";   
    
    extern proc c_nautyClassify(
    subgraph: [] int, 
    subgraphSize: int, 
    results:[] int,
    performCheck: int,
    verbose: int
    ) : int;
  

  // proc runMotifCounting(g1: SegGraph, g2: SegGraph, semanticCheckType: string, 
  proc runMotifCounting(g1: SegGraph, motifSize: int, printProgressInterval: int,
                     algType: string, returnIsosAs: string, st: borrowed SymTab
                     ) throws {

var useSampling: bool = true;
var Sconfig: SamplingConfig; 
writeln("\n useSampling is TRUE. we do sampling");

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
      var neighbours: domain(int, parSafe=false);

      const NeiIn = dstRG1[segRG1[v]..<segRG1[v+1]];
      const NeiOut = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

      neighbours += NeiIn;
      neighbours += NeiOut;

      nodeDegree[v] = neighbours.size;
      // Collect all neighbors (both in and out) in a domain
      nodeNeighbours[v] = neighbours;
    }
    var maxDeg = max reduce nodeDegree;

//////////////////////////////////////////////////////////////////////////

/*
 * Stratifies vertices based on their degrees
 * Divides vertices into strata based on degree ranges
 */
proc stratifyByDegree(n: int, ref nodeDegree: [] int, ref samplingState: SamplingState) {
    // Calculate degree boundaries for stratification
    var sortedDegrees = nodeDegree;
    sort(sortedDegrees);
    var strataBoundaries: [0..#(samplingState.Sconfig.numStrata-1)] int;
    
    // Calculate boundaries for each stratum
    for i in 0..#(samplingState.Sconfig.numStrata-1) {
        var idx = ((i + 1) * n / samplingState.Sconfig.numStrata): int;
        strataBoundaries[i] = sortedDegrees[idx];
    }
    
    // Assign vertices to strata based on their degrees
    forall v in 0..<n {
        var stratumId = samplingState.Sconfig.numStrata - 1;  // Default to highest stratum
        for i in 0..#(samplingState.Sconfig.numStrata-1) {
            if nodeDegree[v] <= strataBoundaries[i] {
                stratumId = i;
                break;
            }
        }
        
        // Add vertex to appropriate stratum
        samplingState.strata[stratumId].vertices.add(v);
        samplingState.strata[stratumId].size.add(1);
    }
    
    // Set initial sample sizes based on pilot fraction
    forall stratum in samplingState.strata {
        var initialSize = (stratum.size.read() * samplingState.Sconfig.pilotFraction): int;
        stratum.sampleSize.write(max(initialSize, samplingState.Sconfig.minSampleSize));
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Degree-based stratification completed:");
        for i in 0..#samplingState.Sconfig.numStrata {
            writeln("Stratum ", i, ":");
            writeln("  Size: ", samplingState.strata[i].size.read());
            writeln("  Sample size: ", samplingState.strata[i].sampleSize.read());
            if i < samplingState.Sconfig.numStrata-1 {
                writeln("  Degree boundary: <= ", strataBoundaries[i]);
            }
        }
    }
}

/*
 * Stratifies vertices uniformly
 * Divides vertices into equal-sized strata regardless of their properties
 */
proc stratifyUniformly(n: int, ref samplingState: SamplingState) {
    var verticesPerStratum = (n / samplingState.Sconfig.numStrata): int;
    var remainingVertices = n % samplingState.Sconfig.numStrata;
    
    // Distribute vertices evenly across strata
    forall v in 0..<n {
        var stratumId = v / verticesPerStratum;
        if stratumId >= samplingState.Sconfig.numStrata {
            stratumId = samplingState.Sconfig.numStrata - 1;
        }
        
        // Add vertex to stratum
        samplingState.strata[stratumId].vertices.add(v);
        samplingState.strata[stratumId].size.add(1);
    }
    
    // Set initial sample sizes based on pilot fraction
    forall stratum in samplingState.strata {
        var initialSize = (stratum.size.read() * samplingState.Sconfig.pilotFraction): int;
        stratum.sampleSize.write(max(initialSize, samplingState.Sconfig.minSampleSize));
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Uniform stratification completed:");
        for i in 0..#samplingState.Sconfig.numStrata {
            writeln("Stratum ", i, ":");
            writeln("  Size: ", samplingState.strata[i].size.read());
            writeln("  Sample size: ", samplingState.strata[i].sampleSize.read());
        }
    }
}

/*
 * Calculates optimal sample sizes for all strata based on Neyman allocation
 * Parameters:
 * - samplingState: The state object containing strata information
 * - totalBudget: Total number of samples to allocate across strata
 * Returns: Array of optimal sample sizes for each stratum
 */
proc calculateOptimalSampleSize(samplingState: borrowed SamplingState, 
                              totalBudget: int): [] int {
    var numStrata = samplingState.Sconfig.numStrata;
    var optimalSizes: [0..#numStrata] int;
    var totalWeight = 0.0;
    
    // Calculate Neyman allocation weights (Nh * Sh)
    forall stratum in samplingState.strata with (+ reduce totalWeight) {
        var strataSize = stratum.size.read();
        var variance = samplingState.localVariance[stratum.id].read();
        var weight = strataSize * sqrt(variance);
        totalWeight += weight;
    }
    
    // Calculate optimal sizes using Neyman allocation
    forall (stratum, size) in zip(samplingState.strata, optimalSizes) {
        var strataSize = stratum.size.read();
        var variance = samplingState.localVariance[stratum.id].read();
        var weight = strataSize * sqrt(variance);
        
        // Calculate size based on weight proportion
        if totalWeight > 0 {
            size = (totalBudget * (weight / totalWeight)): int;
        } else {
            // If no variance information yet, allocate proportionally to stratum size
            size = (totalBudget * (strataSize:real / samplingState.totalSampledVertices.read())): int;
        }
        
        // Ensure minimum and maximum constraints
        size = max(size, samplingState.Sconfig.minSampleSize);
        size = min(size, strataSize);
    }
    
    // Adjust to match total budget if necessary
    var totalAllocated = + reduce optimalSizes;
    if totalAllocated > totalBudget {
        var scale = totalBudget:real / totalAllocated;
        forall size in optimalSizes {
            size = (size:real * scale): int;
            size = max(size, samplingState.Sconfig.minSampleSize);
        }
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Calculated optimal sample sizes:");
        for i in 0..#numStrata {
            writeln("  Stratum ", i, ": ", optimalSizes[i]);
        }
    }
    
    return optimalSizes;
}

/*
 * Calculates initial sample budget based on pilot results
 */
proc calculateInitialSampleBudget(samplingState: borrowed SamplingState): int {
    var totalVertices = + reduce [s in samplingState.strata] s.size.read();
    var avgVariance = (+ reduce [i in samplingState.D] samplingState.localVariance[i].read()) / 
                     samplingState.Sconfig.numStrata;
    
    // Use standard sample size formula with finite population correction
    var z = getZScore(samplingState.Sconfig.confidenceLevel);
    var e = samplingState.Sconfig.marginOfError;
    
    var numerator = (z * z * avgVariance * totalVertices);
    var denominator = (e * e * (totalVertices - 1) + z * z * avgVariance);
    
    var initialBudget = max((numerator / denominator): int, 
                           samplingState.Sconfig.minSampleSize * samplingState.Sconfig.numStrata);
    
    if logLevel == LogLevel.DEBUG {
        writeln("Calculated initial sample budget: ", initialBudget);
        writeln("  Based on:");
        writeln("    Total vertices: ", totalVertices);
        writeln("    Average variance: ", avgVariance);
        writeln("    Confidence level (z): ", z);
        writeln("    Margin of error: ", e);
    }
    
    return initialBudget;
}

/*
 * Calculates recent variance for a stratum based on observed motif classes
 * This is used to update variance estimates during sampling
 */
proc calculateRecentVariance(ref stratum: Stratum, 
                           samplingState: borrowed SamplingState): real {
    const windowSize = max(samplingState.Sconfig.minSampleSize, 
                         stratum.validSamples.read() / 2);
    
    if stratum.validSamples.read() < windowSize then return 0.0;
    
    // Calculate variance based on recent samples
    var mean = stratum.validSamples.read():real / windowSize;
    var variance = max(mean * (1.0 - mean), 0.0);  // Using binomial variance as estimate
    
    // Add small constant to avoid zero variance
    const minVariance = 0.0001;
    return max(variance, minVariance);
}
/*
 * Updates variance estimates based on recent samples
 */
proc updateVarianceEstimates(ref samplingState: SamplingState) {
    forall stratum in samplingState.strata {
        if stratum.validSamples.read() > 0 {
            // Calculate new variance based on recent samples
            // This is a simplified version - you might want to use a moving window
            var newVariance = calculateRecentVariance(stratum, samplingState);
            samplingState.localVariance[stratum.id].write(newVariance);
        }
    }
}

/*
 * Adjusts sample sizes for all strata
 */
proc adjustSampleSizes(ref samplingState: SamplingState, newSizes: [] int) {
    forall (stratum, newSize) in zip(samplingState.strata, newSizes) {
        var currentSize = stratum.sampleSize.read();
        var size = min(max(newSize, samplingState.Sconfig.minSampleSize), 
                      stratum.size.read());
        
        if size != currentSize {
            stratum.sampleSize.write(size);
            if logLevel == LogLevel.DEBUG {
                writeln("Adjusted sample size for stratum ", stratum.id, 
                       " from ", currentSize, " to ", size);
            }
        }
    }
}
/*
 * Safely calculate scale factor avoiding overflow
 */
proc calculateScaleFactor(strataSize: int, sampleSize: int): real {
    if sampleSize == 0 then return 0.0;
    
    // Use logarithmic approach for large numbers
    if strataSize > 1000000 {
        const logScale = log10(strataSize:real) - log10(sampleSize:real);
        return exp(logScale * log(10));
    }
    
    return strataSize:real / sampleSize:real;
}

/*
 * Calculate standard error for a stratum
 */
proc calculateStratumError(strataSize: int, sampleSize: int, sampleVariance: real): real {
    const finitePopulationCorrection = ((strataSize:real - sampleSize:real) / strataSize:real);
    return sqrt((sampleVariance / sampleSize:real) * finitePopulationCorrection);
}
/*
 * Samples a single vertex and explores its motifs
 * Parameters:
 * - v: The vertex to sample
 * - samplingState: Global sampling state
 * - stratum: The stratum containing the vertex
 * - motifSize: Size of motifs to find
 * - maxDeg: Maximum degree in the graph
 * - globalMotifCount: Reference to global motif counter
 * - globalClasses: Reference to global classes set
 */
/*
 * Modified sampleVertex to handle task intents and overflow
 */
proc sampleVertex(v: int,
                 samplingState: borrowed SamplingState,
                 const ref stratum: Stratum, // Changed from 'ref' to 'const ref'
                 motifSize: int,
                 maxDeg: int,
                 ref globalMotifCount: atomic int,
                 ref globalClasses: set(uint(64), parSafe=true),
                 ref localStats: StratumStatistics) throws{
    
    // Create new KavoshState for this vertex
    var state = new KavoshState(g1.n_vertices, motifSize, maxDeg);
    
    // Initialize root vertex
    state.setSubgraph(0, 0, 1);
    state.setSubgraph(0, 1, v);
    state.visited.clear();
    state.visited.add(v);
    
    // Explore from this vertex
    Explore(state, v, 1, motifSize - 1);
    
    // Calculate scale factor safely
    const scaleFactor = calculateScaleFactor(stratum.size.read(), stratum.sampleSize.read());
    
    // Update local statistics
    localStats.updateStats(state.localsubgraphCount, state.localmotifClasses.size, scaleFactor);
    
    // Update global statistics safely using atomic operations
    if scaleFactor > 0.0 {
        const scaledCount = (state.localsubgraphCount:real * scaleFactor):int;
        if scaledCount >= 0 { // Sanity check for overflow
            globalMotifCount.add(scaledCount);
        } else {
            if logLevel == LogLevel.DEBUG {
                writeln("Warning: Overflow detected in scaled count for vertex ", v);
            }
        }
    }
    
    // Update global classes atomically
    globalClasses += state.localmotifClasses;
    
    if logLevel == LogLevel.DEBUG {
        writeln("Sampled vertex ", v, " in stratum ", stratum.id);
        writeln("  Found ", state.localsubgraphCount, " motifs");
        writeln("  Found ", state.localmotifClasses.size, " unique classes");
        writeln("  Scale factor: ", scaleFactor);
    }
}

/*
 * Modified runSamplingBatch to handle atomic updates correctly
 */
proc runSamplingBatch(ref samplingState: SamplingState,
                     motifSize: int,
                     maxDeg: int,
                     ref globalMotifCount: atomic int,
                     ref globalClasses: set(uint(64), parSafe=true)) throws{
    const batchSize = 100;
    
    // Process each stratum
    forall stratumIdx in 0..#samplingState.Sconfig.numStrata 
         with (ref globalClasses, ref globalMotifCount) {
        
        ref s = samplingState.strata[stratumIdx];  // Get reference to the stratum
        var targetSize = s.sampleSize.read();
        var currentCount = s.validSamples.read();
        
        if currentCount >= targetSize then continue;
        
        var batchTarget = min(batchSize, targetSize - currentCount);
        var sampledInBatch: atomic int;
        var stratumStats = new StratumStatistics();
        
        // Sample vertices within the stratum
        forall v in s.vertices with (ref sampledInBatch, 
                                   ref globalClasses, 
                                   ref globalMotifCount,
                                   ref stratumStats,
                                   var rng = new randomStream(real)) {
            if sampledInBatch.read() >= batchTarget then continue;
            
            if rng.getNext() <= (batchTarget:real / s.size.read()) {
                sampleVertex(v, samplingState, s, motifSize, maxDeg, 
                           globalMotifCount, globalClasses, stratumStats);
                sampledInBatch.add(1);
                
                // Update sampling state statistics
                samplingState.strata[stratumIdx].validSamples.add(1);
                samplingState.totalSampledVertices.add(1);
                samplingState.successfulSamples.add(1);
            }
        }
        
        // Update variance estimate for the stratum
        if stratumStats.count.read() > 0 {
            samplingState.localVariance[stratumIdx].write(stratumStats.getVariance());
        }
    }
}
/*
 * Checks if sampling is complete across all strata
 */
proc isSamplingComplete(ref samplingState: SamplingState): bool {
    var complete = true;
    forall stratum in samplingState.strata with (& reduce complete) {
        complete &= stratum.validSamples.read() >= stratum.sampleSize.read();
    }
    return complete;
}
/*
 * Checks if a set of boundaries is valid
 */
proc isValidBoundarySet(boundaries: [] int, nodeDegree: [] int): bool {
    // Check boundaries are strictly increasing
    for i in 1..#boundaries.size {
        if boundaries[i] <= boundaries[i-1] then return false;
    }
    
    // Check boundaries are within degree range
    var minDeg = min reduce nodeDegree;
    var maxDeg = max reduce nodeDegree;
    
    if boundaries[0] <= minDeg then return false;
    if boundaries[boundaries.size-1] >= maxDeg then return false;
    
    return true;
}

/*
 * Calculates total variance across all strata
 */
proc calculateTotalVariance(samplingState: borrowed SamplingState): real {
    var totalVariance = 0.0;
    var totalSamples = 0;
    
    forall stratum in samplingState.strata with (+ reduce totalVariance, 
                                               + reduce totalSamples) {
        if stratum.validSamples.read() > 0 {
            totalVariance += samplingState.localVariance[stratum.id].read() * 
                           stratum.validSamples.read();
            totalSamples += stratum.validSamples.read();
        }
    }
    
    return if totalSamples > 0 then totalVariance / totalSamples else 0.0;
}

/*
 * Simulates stratification with new boundaries to estimate variance
 */
proc simulateStratificationVariance(boundaries: [] int,
                                  samplingState: borrowed SamplingState,
                                  nodeDegree: [] int): real {
    var strataCounts: [0..#samplingState.Sconfig.numStrata] atomic int;
    var strataVariances: [0..#samplingState.Sconfig.numStrata] atomic real;
    
    // Simulate new stratification
    forall v in 0..#nodeDegree.size {
        var stratumId = getStratumIdForDegree(nodeDegree[v], boundaries);
        strataCounts[stratumId].add(1);
        
        // Use current variance as approximation
        var currentId = getStratumIdForDegree(nodeDegree[v], boundaries);
        strataVariances[stratumId].add(samplingState.localVariance[currentId].read());
    }
    
    // Calculate total variance for simulated stratification
    var totalVariance = 0.0;
    var totalCount = + reduce [c in strataCounts] c.read();
    
    forall i in 0..#samplingState.Sconfig.numStrata with (+ reduce totalVariance) {
        var count = strataCounts[i].read();
        if count > 0 {
            totalVariance += strataVariances[i].read() * (count:real / totalCount);
        }
    }
    
    return totalVariance;
}

/*
 * Gets stratum ID for a given degree based on boundaries
 */
proc getStratumIdForDegree(degree: int, boundaries: [] int): int {
    for i in 0..#boundaries.size {
        if degree <= boundaries[i] then return i;
    }
    return boundaries.size;
}

/*
 * Applies new stratification based on updated boundaries
 */
proc restratifyWithBoundaries(samplingState: borrowed SamplingState,
                            boundaries: [] int,
                            nodeDegree: [] int) {
    // Clear existing strata
    forall stratum in samplingState.strata {
        stratum.vertices.clear();
        stratum.size.write(0);
    }
    
    // Redistribute vertices
    forall v in 0..#nodeDegree.size {
        var stratumId = getStratumIdForDegree(nodeDegree[v], boundaries);
        samplingState.strata[stratumId].vertices.add(v);
        samplingState.strata[stratumId].size.add(1);
    }
    
    // Recalculate sample sizes
    var totalSamples = + reduce [s in samplingState.strata] s.validSamples.read();
    var newSizes = calculateOptimalSampleSize(samplingState, totalSamples);
    
    forall (stratum, size) in zip(samplingState.strata, newSizes) {
        stratum.sampleSize.write(size);
    }
}
/*
 * Adjusts strata boundaries based on observed motif patterns
 * Returns true if strata were adjusted, false otherwise
 */
proc adjustStrataBoundaries(samplingState: borrowed SamplingState, 
                          ref nodeDegree: [] int): bool {
    if samplingState.Sconfig.strategyType != "degree" then return false;
    
    // Get current boundaries
    var numBoundaries = samplingState.Sconfig.numStrata - 1;
    var currentBoundaries: [0..#numBoundaries] int;
    
    // Calculate current boundaries based on sorted degrees
    var sortedDegrees = nodeDegree;
    sort(sortedDegrees);
    
    for i in 0..#numBoundaries {
        var idx = ((i + 1) * nodeDegree.size / samplingState.Sconfig.numStrata): int;
        currentBoundaries[i] = sortedDegrees[idx];
    }
    
    // Try different boundary adjustments
    var bestVariance = calculateTotalVariance(samplingState);
    var newBoundaries = currentBoundaries;
    var adjusted = false;
    
    // Test moving each boundary up or down
    const adjustmentFraction = 0.05; // 5% adjustment
    for i in 0..#numBoundaries {
        var delta = max(1, (max reduce nodeDegree - min reduce nodeDegree) * adjustmentFraction): int;
        
        // Try both increasing and decreasing the boundary
        for d in [-delta, delta] {
            var testBoundaries = currentBoundaries;
            testBoundaries[i] += d;
            
            // Check if new boundaries are valid
            if isValidBoundarySet(testBoundaries, nodeDegree) {
                // Simulate new stratification
                var testVariance = simulateStratificationVariance(testBoundaries, 
                                                                samplingState, 
                                                                nodeDegree);
                
                // Update if better variance found
                if testVariance < bestVariance {
                    bestVariance = testVariance;
                    newBoundaries = testBoundaries;
                    adjusted = true;
                }
            }
        }
    }
    
    // Apply new boundaries if improvement found
    if adjusted {
        restratifyWithBoundaries(samplingState, newBoundaries, nodeDegree);
    }
    
    return adjusted;
}
/*
 * Executes the sampling-based motif counting process
 * Parameters:
 * - samplingState: The state object managing sampling configuration and results
 * - g1: The input graph
 * - motifSize: Size of motifs to count
 * - maxDeg: Maximum degree in the graph
 * - globalMotifCount: Reference to global motif counter
 * - globalClasses: Reference to global classes set
 */
/*
 * Enhanced runSamplingProcess with progress-based dynamic adjustments
 */
proc runSamplingProcess(ref samplingState: SamplingState, 
                       g1: SegGraph, 
                       motifSize: int, 
                       maxDeg: int,
                       ref globalMotifCount: atomic int,
                       ref globalClasses: set(uint(64), parSafe=true)) throws {
    
    const checkInterval = 1000; // Check for adjustments every 1000 samples
    const maxAdjustments = 5;   // Maximum number of adjustments allowed
    var adjustmentCount = 0;
    
    // Run initial pilot sampling
    runPilotSampling(samplingState, motifSize, maxDeg, globalClasses);
    
    // Initial sample size calculation based on pilot results
    var totalBudget = calculateInitialSampleBudget(samplingState);
    var sampleSizes = calculateOptimalSampleSize(samplingState, totalBudget);
    
    // Update initial sample sizes
    forall (stratum, size) in zip(samplingState.strata, sampleSizes) {
        stratum.sampleSize.write(size);
    }
    
    // Main sampling loop with dynamic adjustments
    while !isSamplingComplete(samplingState) {
        var currentSampleCount = samplingState.totalSampledVertices.read();
        
        // Check if it's time to consider adjustments
        if currentSampleCount % checkInterval == 0 && adjustmentCount < maxAdjustments {
            var shouldAdjust = shouldPerformAdjustment(samplingState);
            
            if shouldAdjust {
                // Update variance estimates
                updateVarianceEstimates(samplingState);
                
                // Try to adjust strata boundaries
                if adjustStrataBoundaries(samplingState, nodeDegree) {
                    // Recalculate sample sizes if boundaries changed
                    var newSizes = calculateOptimalSampleSize(samplingState, totalBudget);
                    adjustSampleSizes(samplingState, newSizes);
                    adjustmentCount += 1;
                    
                    if logLevel == LogLevel.DEBUG {
                        writeln("Performed adjustment #", adjustmentCount, 
                               " at sample count ", currentSampleCount);
                    }
                }
            }
        }
        
        // Run a batch of sampling
        runSamplingBatch(samplingState, motifSize, maxDeg, globalMotifCount, globalClasses);
    }
}

/*
 * Determines if an adjustment should be performed based on sampling progress
 */
proc shouldPerformAdjustment(samplingState: borrowed SamplingState): bool {
    // Check if we have enough new samples since last adjustment
    var totalSamples = samplingState.totalSampledVertices.read();
    if totalSamples < samplingState.Sconfig.minSampleSize * 2 then return false;
    
    // Calculate mean variance once outside the parallel loop
    var meanVar = calculateMeanVariance(samplingState);
    
    // Check if any stratum has high variance
    var hasHighVariance = false;
    forall stratum in samplingState.strata with (|| reduce hasHighVariance) {
        if stratum.validSamples.read() >= samplingState.Sconfig.minSampleSize {
            var variance = samplingState.localVariance[stratum.id].read();
            if variance > meanVar * 2 {
                hasHighVariance = true;
            }
        }
    }
    
    // Check if sampling rates are significantly different between strata
    var minRate = max(real);
    var maxRate = min(real);
    
    forall stratum in samplingState.strata with (min reduce minRate, max reduce maxRate) {
        if stratum.size.read() > 0 {
            var rate = stratum.validSamples.read():real / stratum.size.read();
            minRate = min(minRate, rate);
            maxRate = max(maxRate, rate);
        }
    }
    
    return hasHighVariance || (maxRate > minRate * 2);
}

/*
 * Calculates mean variance across all strata
 */
proc calculateMeanVariance(samplingState: borrowed SamplingState): real {
    var totalVariance = 0.0;
    var validStrataCount = 0;
    
    forall stratum in samplingState.strata with (+ reduce totalVariance, 
                                               + reduce validStrataCount) {
        if stratum.validSamples.read() >= samplingState.Sconfig.minSampleSize {
            totalVariance += samplingState.localVariance[stratum.id].read();
            validStrataCount += 1;
        }
    }
    
    return if validStrataCount > 0 then totalVariance / validStrataCount else 0.0;
}



/*
 * Runs initial pilot sampling to estimate variance
 */
proc runPilotSampling(ref samplingState: SamplingState, 
                     motifSize: int, 
                     maxDeg: int,
                     ref globalClasses: set(uint(64), parSafe=true)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Starting pilot sampling...");
    }

    forall s in samplingState.strata with (ref globalClasses) {
        var pilotSampleSize = (s.size.read() * samplingState.Sconfig.pilotFraction): int;
        pilotSampleSize = max(pilotSampleSize, samplingState.Sconfig.minSampleSize);
        
        var sampledCount: atomic int;
        var localClasses: set(uint(64), parSafe=false);
        
        forall v in s.vertices with (ref sampledCount, ref localClasses, var rng = new randomStream(real)) {
            // Only sample if we haven't reached our target
            if sampledCount.read() >= pilotSampleSize then continue;
            
            // Probabilistic sampling
            if rng.next() <= samplingState.Sconfig.pilotFraction {
                var state = new KavoshState(g1.n_vertices, motifSize, maxDeg);
                
                // Initialize root vertex
                state.setSubgraph(0, 0, 1);      // Set count to 1
                state.setSubgraph(0, 1, v);      // Set the vertex
                state.visited.clear();           
                state.visited.add(v);
                
                // Explore from this vertex
                Explore(state, v, 1, motifSize - 1);
                
                // Update counts
                sampledCount.add(1);
                samplingState.totalSampledVertices.add(1);
                samplingState.successfulSamples.add(1);
                
                // Update local classes and variance estimate
                localClasses += state.localmotifClasses;
                if state.localmotifClasses.size > 0 {
                    samplingState.localVariance[s.id].write(state.localmotifClasses.size:real);
                }
            }
        }
        
        // Update global classes atomically at the end of stratum processing
        globalClasses += localClasses;
    }
}
/*
 * Adjusts sample sizes based on pilot results
 */
proc adjustSampleSizes(ref samplingState: SamplingState) {
    if logLevel == LogLevel.DEBUG {
        writeln("Adjusting sample sizes based on pilot results...");
    }

    var totalSize = + reduce [s in samplingState.strata] s.size.read();
    var zScore = getZScore(samplingState.Sconfig.confidenceLevel);
    
    forall stratum in samplingState.strata {
        var variance = samplingState.localVariance[stratum.id].read();
        var newSize = (
            (zScore * sqrt(variance) * stratum.size.read()) /
            (samplingState.Sconfig.marginOfError * sqrt(totalSize))
        ): int;
        
        // Ensure we don't exceed stratum size and meet minimum requirements
        newSize = min(max(newSize, samplingState.Sconfig.minSampleSize), stratum.size.read());
        stratum.sampleSize.write(newSize);
    }
}

/*
 * Runs the main sampling process after pilot sampling
 */
proc runMainSampling(ref samplingState: SamplingState, 
                    motifSize: int, 
                    maxDeg: int,
                    ref globalMotifCount: atomic int,
                    ref globalClasses: set(uint(64), parSafe=true)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("Starting main sampling process...");
    }

    forall s in samplingState.strata with (ref globalClasses, ref globalMotifCount) {
        var targetSampleSize = s.sampleSize.read();
        var sampledCount: atomic int;
        var localClasses: set(uint(64), parSafe=false);
        var localMotifCount: atomic int;
        
        forall v in s.vertices with (ref sampledCount, ref localClasses, ref localMotifCount, ref s, 
                                   var rng = new randomStream(real)) {
            if sampledCount.read() >= targetSampleSize then continue;
            
            // Calculate sampling probability based on target sample size
            var samplingProb = (targetSampleSize: real) / s.size.read();
            
            if rng.getNext() <= samplingProb {
                var state = new KavoshState(g1.n_vertices, motifSize, maxDeg);
                
                // Initialize root vertex
                state.setSubgraph(0, 0, 1);
                state.setSubgraph(0, 1, v);
                state.visited.clear();
                state.visited.add(v);
                
                // Explore from this vertex
                Explore(state, v, 1, motifSize - 1);
                
                // Update local counts with scaling
                var scaleFactor = s.size.read() / targetSampleSize;
                localMotifCount.add(state.localsubgraphCount * scaleFactor);
                localClasses += state.localmotifClasses;
                
                // Update sampling statistics
                sampledCount.add(1);
                samplingState.totalSampledVertices.add(1);
                samplingState.successfulSamples.add(1);
                s.validSamples.add(1);
            }
        }
        
        // Update global counters atomically at the end of stratum processing
        globalMotifCount.add(localMotifCount.read());
        globalClasses += localClasses;
        
        if sampledCount.read() < targetSampleSize {
            s.samplingErrors.add(1);
            if !samplingState.recordError(s.id) {
                throw new Error("Failed to achieve target sample size for stratum " + 
                              s.id:string);
            }
        }
    }
}

/*
 * Helper function to get z-score for confidence level
 */
proc getZScore(confidenceLevel: real): real {
    select confidenceLevel {
        when 0.90 do return 1.645;
        when 0.95 do return 1.96;
        when 0.99 do return 2.576;
        otherwise do return 1.96;  // Default to 95% confidence
    }
}
//////////////////////////////////////////////////////////////////////////
    // All motif counting and classify variables
    var globalMotifCount: atomic int;
    var globalClasses: set(uint(64), parSafe=true);
    // Initiate it to 0
    globalMotifCount.write(0);

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
        if logLevel == LogLevel.DEBUG {
            writeln("===== generatePatternDirect called =====");
            writeln("Original chosenVerts: ", chosenVerts);
            writeln("Nauty labels: ", nautyLabels);
        }

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
            writeln("Generated pattern= ", pattern);
            writeln("\nEquivalent Adjacency Matrix (2D visualization):");
            for i in 0..#state.k {
                for j in 0..#state.k {
                    var bitPos = i * state.k + j;
                    write(if (pattern & (1:uint(64) << bitPos)) != 0 then 1 else 0, " ");
                }
                writeln();
            }
        }
        return pattern;
    }// End of generatePatternDirect

    // Explores subgraphs containing the root vertex,
    // expanding level by level until remainedToVisit = 0 (which means we have chosen k vertices).
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
            
            // var adjMatrix: [0..8] int = [1, 1, 1, 1, 1, 1, 1, 1, 1];
            // For test purpose assume naugty returned this
            var results: [0..<state.k] int = 0..<state.k;

            //var subgraphSize = motifSize;
            //var subgraph = adjMatrix;

            var performCheck: int = 0; // Set to 1 to perform nauty_check, 0 to skip // DECIDE
            var verbose: int = 0;      // Set to 1 to enable verbose logging  // DECIDE

            var status = c_nautyClassify(adjMatrix, motifSize, results, performCheck, verbose);

            if logLevel == LogLevel.DEBUG {
                writeln("for subgraph = ",adjMatrix, "Nauty returned: ",
                                         results, " we are in the way to Classify!", "status = ", status);
                                         
            }

            // Handle potential errors
            if status != 0 {
                writeln("Error: c_nautyClassify failed with status ", status);
                //return;
            }
            // // Print canonical labeling
            // writeln("Canonical Labeling:");
            // for i in 0..<subgraphSize {
            //     writeln("Node ", i, " -> ", results[i]);
            // }
            var nautyLabels = results;
            var pattern = generatePatternDirect(chosenVerts, nautyLabels, state);
            state.localmotifClasses.add(pattern);
            
            if logLevel == LogLevel.DEBUG {
                writeln("state.localmotifClasses: ", state.localmotifClasses);
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

//////////////////////////////Oliver: in case you needed!///////////////////////////////////////////////////
//////////////////////////////Check it, I didn't check it as much as other functions
///////////////////////////////////////////////////
proc patternToAdjMatrixAndEdges(pattern: uint(64), k: int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("===== patternToAdjMatrixAndEdges called =====");
        writeln("Input pattern: ", pattern);
        writeln("k value: ", k);
    }

    var adjMatrix: [0..#(k * k)] int = 0;
    var edgeCount = 0;
    
    // First pass to count edges
    for i in 0..#k {
        for j in 0..#k {
            var bitPos = i * k + j;
            if (pattern & (1:uint(64) << bitPos)) != 0 {
                adjMatrix[i * k + j] = 1;
                edgeCount += 1;
            }
        }
    }

    // Create arrays for edges
    var srcNodes: [0..#edgeCount] int;
    var dstNodes: [0..#edgeCount] int;
    var edgeIdx = 0;

    // Second pass to populate edge arrays
    for i in 0..#k {
        for j in 0..#k {
            if adjMatrix[i * k + j] == 1 {
                srcNodes[edgeIdx] = i;
                dstNodes[edgeIdx] = j;
                edgeIdx += 1;
            }
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nReconstructed Adjacency Matrix (2D visualization):");
        for i in 0..#k {
            for j in 0..#k {
                write(adjMatrix[i * k + j], " ");
            }
            writeln();
        }

        writeln("\nEdge List:");
        for i in 0..#edgeCount {
            writeln(srcNodes[i], " -> ", dstNodes[i]);
        }

        // Verify by converting back
        var verifyPattern: uint(64) = 0;
        var pos = 0;
        for i in 0..#k {
            for j in 0..#k {
                if adjMatrix[i * k + j] == 1 {
                    verifyPattern |= 1:uint(64) << pos;
                }
                pos += 1;
            }
        }
        writeln("\nVerification - pattern from reconstructed matrix: ", verifyPattern);
        writeln("Original pattern: ", pattern);
        writeln("Patterns match: ", verifyPattern == pattern);
        writeln();
    }

    return (adjMatrix, srcNodes, dstNodes);
}

/* Example usage:
var pattern: uint(64) = 123456;  // some pattern
var k = 3;  // size of matrix
var (adjMatrix, srcNodes, dstNodes) = patternToAdjMatrixAndEdges(pattern, k);
Also we can make it to accept set of classes then srcNodes and dstNodes will be for all classes and each class
seperated by a -1, So Harvard team can use it for Visualization purpose
*/
////////////////////////////////////////////////////////////////////////////////


    // Enumerate: Iterates over all vertices as potential roots
    // and calls Explore to find all subgraphs of size k containing that root.
    proc Enumerate(n: int, k: int, maxDeg: int) throws {
        if logLevel == LogLevel.DEBUG {
            writeln("Enumerate: starting enumeration over all vertices");
        }

        forall v in 0..<n with (ref globalClasses, ref globalMotifCount) {
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

            // Update global counters
            globalMotifCount.add(state.localsubgraphCount);
            globalClasses += state.localmotifClasses;
        }

        if logLevel == LogLevel.DEBUG {
            writeln("Enumerate: finished enumeration over all vertices");
            writeln("\nglobalMotifCount: ", globalMotifCount.read());
            writeln("\nglobalClasses: ", globalClasses);
            writeln("\nglobalClasses.size: ", globalClasses.size);
        }
    }// End of Enumerate



    if useSampling {
        writeln("Starting motif sampling with configuration:");
        writeln("  Confidence Level: ", Sconfig.confidenceLevel * 100, "%");
        writeln("  Margin of Error: ±", Sconfig.marginOfError * 100, "%");
        writeln("  Stratification Strategy: ", Sconfig.strategyType);
        writeln("  Number of Strata: ", Sconfig.numStrata);
        
        var samplingState = stratifyGraph(n, nodeDegree, Sconfig);
        
        // Run sampling and collect statistics
        try {
            runSamplingProcess(samplingState, g1, motifSize, maxDeg, globalMotifCount, globalClasses);
            
            var (isValid, errorMsg) = samplingState.validateResults();
            if !isValid {
                writeln("Warning: Sampling results may be unreliable - ", errorMsg);
                writeln("Falling back to full enumeration...");
                useSampling = false;
            } else {
                // Print sampling statistics
                writeln("\nSampling Statistics:");
                writeln("  Total Vertices Sampled: ", samplingState.totalSampledVertices.read());
                writeln("  Successful Samples: ", samplingState.successfulSamples.read());
                writeln("  Failed Samples: ", samplingState.failedSamples.read());
                
                for stratum in samplingState.strata {
                    writeln("\nStratum ", stratum.id, " Statistics:");
                    writeln("  Size: ", stratum.size.read());
                    writeln("  Samples: ", stratum.validSamples.read());
                    writeln("  Sampling Errors: ", stratum.samplingErrors.read());
                }
            }
        } catch e {
            writeln("Error during sampling: ", e.message());
            writeln("Falling back to full enumeration...");
            useSampling = false;
        }
    }

    // Only run full enumeration if sampling failed or wasn't used
    if !useSampling {
        writeln("Starting full enumeration with k=", k, " on a graph of ", n, " vertices.");
        writeln("Maximum degree: ", maxDeg);
        Enumerate(g1.n_vertices, motifSize, maxDeg);
    }
    // Oliver: Now you can make your src and dst based on Classes that I gathered in 
    // motifClasses and return them to users 
    // we should decide to keep or delete (allmotifs list)
    

    writeln("\nglobalMotifCount: ", globalMotifCount.read());
    writeln("\nglobalClasses: ", globalClasses);
    writeln("\nglobalClasses.size: ", globalClasses.size);

    writeln("**********************************************************************");

    // writeln("\nallmotifs List size: ", allmotifs.size);
    // writeln("\nNumber of found motif Classes: ", motifClasses.size);
    // // To read the final count:
    // writeln("\nallMotifCounts: ", allMotifCounts.read());
    var tempArr: [0..0] int;
    var srcPerMotif = makeDistArray(2*2, int);
    var dstPerMotif = makeDistArray(2*2, int);
    return (srcPerMotif, dstPerMotif, tempArr, tempArr);
  }// End of runMotifCounting

}// End of MotifCounting Module