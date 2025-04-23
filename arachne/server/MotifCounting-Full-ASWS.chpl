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
  var newVertices: domain(int, parSafe=true);     // Only new vertices for this iteration
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

  // Global motif counts map
  var globalMotifCounts: map(uint(64), atomic int);

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
    var factorial_result: bigint; 
    fac(factorial_result, ASconfig.k);  
    this.theoreticalTotalPatterns = (rawCount:real / factorial_result:real):int;

    // Initialize atomic variables
    var miss: atomic real;
    this.missProbability = miss;
          
    var coverageMetricsArr: [0..2] atomic real;
    this.coverageMetrics = coverageMetricsArr;

    var roles: [0..3] atomic int;
    this.roleDistribution = roles;
          
    // Initialize pattern maps in declaration order
    this.patternsByRole = [i in 0..3] new map(uint(64), atomic int);
    this.rolePatternCounts = [i in 0..2] new map(uint(64), atomic int);
    this.patternConfidenceIntervals = new map(uint(64), (real, real));
    this.significanceLevel = 0.05;  // Default significance level
    
    // Initialize pattern history with empty sets
    this.patternHistory = [i in 0..4] new set(uint(64));
    
    var stability: atomic real;
    this.stabilityScore = stability;

    var convergenceMetricsArr: [0..2] atomic real;
    this.convergenceMetrics = convergenceMetricsArr;
    
    // Initialize global motif counts map
    this.globalMotifCounts = new map(uint(64), atomic int);
    
    init this;

    // Post-initialization settings
    this.missProbability.write(1.0);
    forall i in 0..2 do this.coverageMetrics[i].write(0.0);
    forall i in 0..3 do this.roleDistribution[i].write(0);
    forall i in 0..2 do this.convergenceMetrics[i].write(0.0);
    this.stabilityScore.write(0.0);
  }
  

    /* Role Classification and Tracking */
    proc classifyVertexRoles(ref nodeDegree: [] int, ref nodeNeighbours: [] domain(int)) {
    writeln("\n=== Classifying Vertex Roles ===");
    const maxDeg = max reduce nodeDegree;
    const avgDeg = (+ reduce nodeDegree) / nodeDegree.size;

    // First, reset role distribution counts
    for i in 0..3 do this.roleDistribution[i].write(0);
    
    // Get reference to member variables before the forall loop
    ref roleDistRef = this.roleDistribution;
    ref vertexRolesRef = this.vertexRoles;
    const n = this.ASconfig.n;
    
    forall v in 0..#n with (ref roleDistRef) {
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
        vertexRolesRef[v] = 0;  // Hub
        roleDistRef[0].add(1);
        } else if clustering > 0.5 && nodeDegree[v] > avgDeg {
        vertexRolesRef[v] = 1;  // Bridge
        roleDistRef[1].add(1);
        } else {
        vertexRolesRef[v] = 2;  // Peripheral
        roleDistRef[2].add(1);
        }
    }

    // Print role distribution
    writeln("Role distribution:");
    writeln("- Hubs: ", this.roleDistribution[0].read());
    writeln("- Bridges: ", this.roleDistribution[1].read());
    writeln("- Peripheral: ", this.roleDistribution[2].read());
    }

    /* Error Bounds Calculation */
    proc updateErrorBounds(patterns: set(uint(64))) throws {
      // Calculate confidence intervals for each pattern
      const z = 1.96;  // 95% confidence level
      // 90% confidence level: z = 1.645
      // 95% confidence level: z = 1.96
      // 99% confidence level: z = 2.576
      const n = processedVertices.size;
      
      for pattern in patterns {
        var count = 0;
        
        // Sum up counts from each role where this pattern exists
        for role in 0..2 {
          if rolePatternCounts[role].contains(pattern) {
            count += rolePatternCounts[role][pattern].read();
          }
        }
        
        // Calculate standard error
        var p = if n > 0 then count:real / n:real else 0.0;
        var stderr = if n > 0 then sqrt((p * (1.0 - p)) / n) else 0.0;
        
        // Update confidence intervals
        patternConfidenceIntervals[pattern] = (
          max(0.0, p - z * stderr),
          min(1.0, p + z * stderr)
        );
      }
    }

    /* Pattern Stability Analysis */
    proc updatePatternStability(patterns: set(uint(64))) throws {
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
    
    proc calculateRoleStability(): real throws {
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
  // First update the convergence metrics
  this.updateConvergenceMetrics();
  
  // Three conditions must be met:
  // 1. Low probability of missing patterns (P_miss < 0.05)
  // 2. Good overall coverage (C(W) > 0.7)
  // 3. Hub coverage is satisfactory
  
  const missProb = this.missProbability.read();
  const avgCoverage = (+ reduce [m in this.coverageMetrics] m.read()) / 3.0;
  const hubCoverage = this.coverageMetrics[1].read();
  
  writeln("\n=== Pattern Discovery Guarantees Check ===");
  writeln("- Miss Probability: ", missProb, " (target < ", epsilon, ")");
  writeln("- Average Coverage: ", avgCoverage, " (target > 0.7)");
  writeln("- Hub Coverage: ", hubCoverage, " (target >= 0.9)");
  
  return missProb < epsilon &&
         avgCoverage >= 0.7 &&
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
 /* Complete updateConvergenceMetrics method for WavefrontState class */
proc updateConvergenceMetrics() {
  var alpha: [0..2] real;
  for role in 0..2 {
    var roleCount = this.roleDistribution[role].read();
    
    if roleCount > 0 {
      // Count vertices of this role in the wavefront
      var roleInWavefront = 0;
      for v in this.wavefront {
        if this.vertexRoles[v] == role {
          roleInWavefront += 1;
        }
      }
      
      // Calculate alpha_s = |W ∩ S_s| / |S_s|
      alpha[role] = roleInWavefront:real / roleCount:real;
    } else {
      alpha[role] = 1.0; // If no vertices of this role, set alpha to 1.0
    }
  }
  
  // Calculate beta_min (minimum stratum coverage efficiency)
  var betaMin = min reduce alpha;
  
  // Calculate miss probability using the theoretical formula
  var missProb = this.theoreticalTotalPatterns * exp(-betaMin * this.wavefront.size:real);
  this.missProbability.write(missProb);
  
  // Update coverage metrics
  var structuralCoverage = this.wavefront.size:real / this.ASconfig.n:real;
  
  // Calculate hub coverage properly
  var hubsInWavefront = 0;
  for hub in this.hubSet {
    if this.wavefront.contains(hub) {
      hubsInWavefront += 1;
    }
  }
  var hubCoverage = if this.hubSet.size > 0 then hubsInWavefront:real / this.hubSet.size:real else 0.0;
  
  // Calculate pattern coverage
  var patternCoverage = this.globalMotifCounts.size:real / this.theoreticalTotalPatterns:real;
  
  this.coverageMetrics[0].write(structuralCoverage);
  this.coverageMetrics[1].write(hubCoverage);
  this.coverageMetrics[2].write(patternCoverage);
  
  writeln("- Beta_min: ", betaMin, " Miss Prob: ", missProb);
  writeln("- Coverage: [Structural: ", structuralCoverage, 
          ", Hub: ", hubCoverage, 
          ", Pattern: ", patternCoverage, "]");
}
    //}
  } // End of WavefrontState class


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

    // Functions to initialize the KavoshState
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
  } // End of KavoshState class


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
                          algType: string, returnIsosAs: string, st: borrowed SymTab) throws {
    
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
      
      // First collect all fingerprints in an array for normalization
      var allFps: [0..#wavefrontRef.size] real;
      var fpCounter: atomic int;
      
      // First pass: compute raw scores
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
        
        // Store raw score
        fingerprintsRef[v] = fp;
        
        // Store for normalization
        const idx = fpCounter.fetchAdd(1);
        if idx < allFps.size {
          allFps[idx] = fp;
        }
      }
      
      // Second pass: normalize to ensure full range usage
      var fpCount = fpCounter.read();
      if fpCount > 0 {
        var minFp = min reduce allFps[0..#fpCount];
        var maxFp = max reduce allFps[0..#fpCount];
        var frange = maxFp - minFp;
        
        if frange > 0.0001 {  // Avoid division by near-zero
          forall v in wavefrontRef with (ref fingerprintsRef) {
            // Normalize to [0,0.99] range
            fingerprintsRef[v] = min(0.99, ((fingerprintsRef[v] - minFp) / frange));
          }
        }
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
proc processWavefrontWithSwapping(ref state: WavefrontState,
                                 ref globalMotifCount: atomic int,
                                 ref globalMotifSet: set(uint(64), parSafe=true),
                                 ref seenMatrices: set(uint(64), parSafe=true)) throws {
  
  writeln("\n=== Processing New Vertices ===");
  writeln("- Total vertices in wavefront: ", state.wavefront.size);
  writeln("- Processing new vertices: ", state.newVertices.size);
  
  state.timer.clear();
  state.timer.start();
  
  // Only process new vertices
  forall v in state.newVertices with (ref globalMotifSet, ref globalMotifCount, ref seenMatrices) {
    // Create thread-local copies of the neighbor data structures that will be modified
    var local_node_IN_Neighbours: [0..<state.ASconfig.n] domain(int);
    var local_node_OUT_Neighbours: [0..<state.ASconfig.n] domain(int);
    var local_nodeNeighbours: [0..<state.ASconfig.n] domain(int);
    
    // Flag array to track which nodes have modified neighbor lists
    var isModified: [0..<state.ASconfig.n] bool = false;
    
    // Initialize with empty domains
    for i in 0..<state.ASconfig.n {
      local_node_IN_Neighbours[i] = {1..0}; // Empty domain
      local_node_OUT_Neighbours[i] = {1..0}; // Empty domain
      local_nodeNeighbours[i] = {1..0}; // Empty domain
    }
    
    // Only swap node if targetNode is not 0
    if v != 0 {
      // Copy the neighbor sets for nodes 0 and v
      local_node_IN_Neighbours[0] = node_IN_Neighbours[v];
      local_node_OUT_Neighbours[0] = node_OUT_Neighbours[v];
      local_nodeNeighbours[0] = nodeNeighbours[v];
      
      local_node_IN_Neighbours[v] = node_IN_Neighbours[0];
      local_node_OUT_Neighbours[v] = node_OUT_Neighbours[0];
      local_nodeNeighbours[v] = nodeNeighbours[0];
      
      // Mark these nodes as modified
      isModified[0] = true;
      isModified[v] = true;
      
      // For all other nodes, we need to update references to 0 and v
      for u in 0..<state.ASconfig.n {
        if u == 0 || u == v {
          continue; // Already handled above
        }
        
        // Check if this node has 0 or v as a neighbor
        var hasReferencesToSwappedNodes = false;
        for neighbor in nodeNeighbours[u] {
          if neighbor == 0 || neighbor == v {
            hasReferencesToSwappedNodes = true;
            break;
          }
        }
        
        // Only modify nodes that reference 0 or v
        if hasReferencesToSwappedNodes {
          var new_in: domain(int, parSafe=true);
          var new_out: domain(int, parSafe=true);
          var new_all: domain(int, parSafe=true);
          
          // Update incoming neighbors
          for neighbor in node_IN_Neighbours[u] {
            if neighbor == 0 {
              new_in.add(v);
            } else if neighbor == v {
              new_in.add(0);
            } else {
              new_in.add(neighbor);
            }
          }
          
          // Update outgoing neighbors
          for neighbor in node_OUT_Neighbours[u] {
            if neighbor == 0 {
              new_out.add(v);
            } else if neighbor == v {
              new_out.add(0);
            } else {
              new_out.add(neighbor);
            }
          }
          
          // Update all neighbors
          new_all += new_in;
          new_all += new_out;
          
          // Store in local copies
          local_node_IN_Neighbours[u] = new_in;
          local_node_OUT_Neighbours[u] = new_out;
          local_nodeNeighbours[u] = new_all;
          
          // Mark as modified
          isModified[u] = true;
        }
      }
    }
    
    // Get vertex role
    const role = state.vertexRoles[v];
    
    // Create state for tracking results
    var localKavoshState = new KavoshState(state.ASconfig.n, state.ASconfig.k, max reduce nodeDegree);
    
    // Initialize with root 0 (which represents our target node after swapping)
    localKavoshState.setSubgraph(0, 0, 1);
    localKavoshState.setSubgraph(0, 1, 0);
    localKavoshState.visited.clear();
    localKavoshState.visited.add(0);
    
    // Run the local Explore function with the thread-local neighbor data
    localExplore(localKavoshState, 0, 1, state.ASconfig.k - 1, isModified, 
                local_nodeNeighbours, local_node_IN_Neighbours, local_node_OUT_Neighbours);
    
    // Calculate how many complete motifs we found
    const numMotifs = localKavoshState.localsubgraphCount;
    const totalVertices = localKavoshState.motifVertices.size;
    const k = state.ASconfig.k;
    
    //writeln("For root: ", v, " We Found ", numMotifs);
    
    // Skip if no motifs found
    if numMotifs == 0 || totalVertices == 0 {
      continue;
    }
    
    // Verify we have the expected number of vertices
    if totalVertices != numMotifs * k {
      writeln("WARNING: Unexpected number of vertices. Expected ", numMotifs * k, 
              " but got ", totalVertices, ". Skipping this vertex.");
      continue;
    }
    
    // Process the motifs found using the same approach as in EnumerateForMultipleNodes
    // ... (Rest of the processing logic from EnumerateForMultipleNodes)
    
    // Create arrays for batch processing
    var batchedMatrices: [0..#(numMotifs * k * k)] int = 0;
    var batchedResults: [0..#(numMotifs * k)] int;
    
    // Get the motif vertices as an array
    var motifVerticesArray = localKavoshState.motifVertices.toArray();
    
    // Track which matrices need to be processed
    var matricesToProcess: list((int, uint(64)));  // (index, binary) pairs for new matrices
    var seenIndices: domain(int, parSafe=false);  // Indices of matrices we've seen before
    var localPatterns: set(uint(64), parSafe=false);
    
    // Thread-local set of seen matrices for cache optimization
    var localSeenMatrices: set(uint(64), parSafe=false);
    
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
      
      // Check if we've seen this matrix before
      if localSeenMatrices.contains(matrixBinary) || seenMatrices.contains(matrixBinary) {
        // We've seen this pattern before, skip Nauty processing
        seenIndices.add(i);
      } else {
        // New pattern, add to seen matrices and process
        localSeenMatrices.add(matrixBinary);
        seenMatrices.add(matrixBinary);
        matricesToProcess.pushBack((i, matrixBinary));
      }
    }
    
    // Process only unseen matrices with Nauty (similar to EnumerateForMultipleNodes)
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
      }
      
      // Process only unique matrices with Nauty
      var batchSize = uniqueCount;
      var status = c_nautyClassify(uniqueMatrices, k, uniqueResults, 1, 0, batchSize);
      
      // Process results to get canonical patterns
      for i in 0..<uniqueCount {
        var (origIdx, originalBinary) = matricesToProcess[i];
        var resultOffset = i * k;
        
        // Extract nauty results for this matrix
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
        
        // Add canonical pattern to local patterns
        localPatterns.add(canonicalPattern);
        
        // Update role-specific pattern counts
        if role >= 0 && role <= 2 {
          if !state.rolePatternCounts[role].contains(canonicalPattern) {
            var newCount: atomic int;
            state.rolePatternCounts[role].add(canonicalPattern, newCount);
          }
          state.rolePatternCounts[role][canonicalPattern].add(1);
        }
        
        // Crucial fix: Update GLOBAL pattern counts
        if !state.globalMotifCounts.contains(canonicalPattern) {
          var newCount: atomic int;
          state.globalMotifCounts.add(canonicalPattern, newCount);
        }
        state.globalMotifCounts[canonicalPattern].add(1);
      }
    }
    
    // Process results for each motif to count frequencies correctly
    for i in 0..<numMotifs {
      // Count all motifs
      globalMotifCount.add(1);
      
      // For matrices we've seen before, we need to find which canonical pattern they map to
      if seenIndices.contains(i) {
        var baseIdx = i * k;
        var matrixBinary: uint(64) = 0;
        
        // Rebuild binary matrix
        for row in 0..<k {
          for col in 0..<k {
            if row != col && batchedMatrices[i * (k * k) + row * k + col] == 1 {
              matrixBinary |= 1:uint(64) << (row * k + col);
            }
          }
        }
        
        // Find the matching pattern in seenMatrices
        for pattern in globalMotifSet {
          var patternMatrix = patternToAdjMatrix(pattern, k);
          var patternBinary: uint(64) = 0;
          
          // Convert to binary for comparison
          var pos = 0;
          for row in 0..<k {
            for col in 0..<k {
              if row != col && patternMatrix[row * k + col] == 1 {
                patternBinary |= 1:uint(64) << pos;
              }
              pos += 1;
            }
          }
          
          if patternBinary == matrixBinary {
            // Update role-specific pattern counts
            if role >= 0 && role <= 2 {
              if !state.rolePatternCounts[role].contains(pattern) {
                var newCount: atomic int;
                state.rolePatternCounts[role].add(pattern, newCount);
              }
              state.rolePatternCounts[role][pattern].add(1);
            }
            
            // Update GLOBAL pattern counts
            if !state.globalMotifCounts.contains(pattern) {
              var newCount: atomic int;
              state.globalMotifCounts.add(pattern, newCount);
            }
            state.globalMotifCounts[pattern].add(1);
            
            break;
          }
        }
      }
    }
    
    // Add local patterns to global set
    globalMotifSet += localPatterns;
  }
  
  // Mark these vertices as processed
  state.processedVertices += state.newVertices;
  
  // Update all pattern discovery metrics
  state.updatePatternDiscoveryMetrics(globalMotifSet);
  
  // Update convergence metrics
  state.updateConvergenceMetrics();
  
  state.timer.stop();
  writeln("=== Wavefront Processing Complete ===");
  writeln("- Total motifs found: ", globalMotifCount.read());
  writeln("- Unique patterns: ", globalMotifSet.size);
  writeln("- Processed Vertices: ", state.processedVertices.size);
  writeln("- Pattern counts:");
  
  // Print the pattern counts from globalMotifCounts
  for pattern in state.globalMotifCounts.keys() {
    writeln("  Pattern ", pattern, ": ", state.globalMotifCounts[pattern].read());
  }
  
  writeln("- Time taken: ", state.timer.elapsed(), " seconds");
}

/* Function to calculate beta_min from state */
proc calculateBetaMin(ref state: WavefrontState): real {
  var alpha: [0..2] real;
  
  // Calculate stratum coverage efficiencies for each role
  for role in 0..2 {
    var roleCount = state.roleDistribution[role].read();
    
    if roleCount > 0 {
      // Count vertices of this role in the wavefront
      var roleInWavefront = 0;
      for v in state.wavefront {
        if state.vertexRoles[v] == role {
          roleInWavefront += 1;
        }
      }
      
      // Calculate alpha_s = |W ∩ S_s| / |S_s|
      alpha[role] = roleInWavefront:real / roleCount:real;
    } else {
      alpha[role] = 1.0; // If no vertices of this role, set alpha to 1.0
    }
  }
  
  // Debug information - commented out to reduce verbosity
  writeln("Role coverage efficiencies:");
  writeln("- Hub alpha: ", alpha[0]);
  writeln("- Bridge alpha: ", alpha[1]);
  writeln("- Peripheral alpha: ", alpha[2]);
  
  // beta_min = min_s alpha_s
  return min reduce alpha;
}




    /* Main ASWS sampling procedure which processes current wavefront to find motifs */
    proc runASWSWithSwapping(n: int, k: int,
                        ref nodeDegree: [] int,
                        ref nodeNeighbours: [] domain(int),
                        ref globalMotifCount: atomic int,
                        ref globalMotifSet: set(uint(64)),
                        ref seenMatrices: set(uint(64), parSafe=true)) throws {
  
  writeln("\n========== Starting ASWS Sampling with Node Swapping ==========");
  
  // Existing initialization code...
  var ASconfig = new ASWSConfig(n, k);
  var maxDeg = max reduce nodeDegree;
  var state = new WavefrontState(ASconfig, maxDeg);
  var totalTimer: stopwatch;
  totalTimer.start();
  
  // Steps 1-3: Identify hubs, classify roles, initialize wavefront
  identifyHubs(state, nodeDegree);
  state.classifyVertexRoles(nodeDegree, nodeNeighbours);
  initializeWavefrontWithHubsOnly(state, nodeDegree);
  
  // Calculate initial convergence metrics
  //state.updateConvergenceMetrics();
  
  // Main sampling loop
  var iteration = 0;
  var meetsGuarantees: bool;// = state.hasPatternDiscoveryGuarantees();
  
  while (!meetsGuarantees && iteration < 20) {
    writeln("\nIteration ", iteration + 1);
    
    // Update fingerprints
    computeFingerprints(state, nodeNeighbours, nodeDegree);
    
    // Use the NEW processing function that employs node swapping
    processWavefrontWithSwapping(state, globalMotifCount, globalMotifSet, seenMatrices);
    
    // Expand wavefront
    expandWavefrontTheoretical(state, nodeNeighbours, nodeDegree);
    
    // Update statistics and check convergence
    state.updatePatternStats(globalMotifSet.size);
    state.updateConvergenceMetrics();
    
    // Calculate optimal wavefront size
    var epsilon = 0.05;
    var wOpt = calculateOptimalWavefrontSize(state, epsilon);
    writeln("- Optimal wavefront size: ", wOpt);
    writeln("- Current wavefront size: ", state.wavefront.size);
    
    // Check if we meet the guarantees now
    meetsGuarantees = state.hasPatternDiscoveryGuarantees();
    
    // Safety stop
    if state.wavefront.size > n * 0.5 {
      writeln("WARNING: Stopping due to large sample size (>50% of graph)");
      break;
    }
    
    iteration += 1;
  }
  
  totalTimer.stop();
  
  // Final reporting with new scaling formula
  writeln("\n========== ASWS Sampling Complete ==========");
  writeln("Final Statistics:");
  writeln("- Total vertices sampled: ", state.wavefront.size);
  writeln("- Total motifs found: ", globalMotifCount.read());
  writeln("- Unique patterns discovered: ", globalMotifSet.size);
  
  // Final convergence metrics update
  state.updateConvergenceMetrics();
  
  // Scale frequency estimates using the MODIFIED SCALING FORMULA
  writeln("\n=== Estimated Global Frequencies ===");
  
  // NEW SCALING: Simply scale by proportion of vertices
  var scalingFactor = (n:real / state.wavefront.size:real);
  
  writeln("- Scaling factor (n / |W|): ", scalingFactor);
  writeln("Pattern\tSample Freq\tEstimated Total Freq");
  
  var totalEstimated = 0.0;
  for pattern in state.globalMotifCounts.keys() {
    var sampleFreq = state.globalMotifCounts[pattern].read();
    var estTotalFreq = sampleFreq:real * scalingFactor;
    writeln(pattern, "\t", sampleFreq, "\t", estTotalFreq:int);
    totalEstimated += estTotalFreq;
  }
  
  writeln("- Total estimated motifs: ", totalEstimated:int);
  writeln("- Pattern discovery guarantees met: ", meetsGuarantees);
  writeln("- Total time: ", totalTimer.elapsed(), " seconds");
  
  // Final pattern discovery stats
  state.printCoverageStats();
  
  writeln("============================================\n");
  
  return (state, globalMotifSet, globalMotifCount);
}

/* New calculateOptimalWavefrontSize function */
proc calculateOptimalWavefrontSize(ref state: WavefrontState, epsilon: real = 0.05): int {
  var betaMin = calculateBetaMin(state);
  
  // Protect against division by zero or very small beta_min
  if betaMin < 0.000001 {
    betaMin = 0.000001;
  }
  
  // Use safe calculation to prevent integer overflow
  var logTerm = log(1.0/epsilon);
  var nTerm = sqrt(state.ASconfig.n:real);
  var wOpt = (nTerm * sqrt(logTerm) / betaMin): int;
  writeln("wOpt: ", wOpt, " state.minRequiredSize: ", state.minRequiredSize, " state.ASconfig.n", state.ASconfig.n);
  // Ensure the result is reasonable
  wOpt = max(wOpt, state.minRequiredSize);
  wOpt = min(wOpt, state.ASconfig.n);
  
  return wOpt;
}
/* 5. Initialize wavefront with hubs only */
proc initializeWavefrontWithHubsOnly(ref state: WavefrontState, nodeDegree: [] int) {
  writeln("\n=== Initializing Wavefront with Hubs Only ===");
  
  // Simply set the wavefront to be the hub set
  state.wavefront = state.hubSet;
  state.newVertices = state.hubSet;
  
  writeln("- Initialized wavefront with ", state.hubSet.size, " hubs");
}
/* 6. Implement theoretically-sound wavefront expansion */
proc expandWavefrontTheoretical(ref state: WavefrontState,
                               ref nodeNeighbours: [] domain(int),
                               ref nodeDegree: [] int) {
  const currentSize = state.wavefront.size;
  writeln("\n=== Expanding Wavefront (Theoretical) ===");
  writeln("- Current wavefront size: ", currentSize);
  
  // Fixed expansion size
  const expansionSize = 50;
  
  // Clear previous new vertices
  state.newVertices.clear();
  
  // Collect candidate pools for three expansion categories
  var hubNeighbors: domain(int, parSafe=true);
  var diverseCandidates: domain(int, parSafe=true);
  var randomCandidates: domain(int, parSafe=true);
  
  // 1. Get hub neighbors (40%)
  forall hub in state.hubSet with (ref hubNeighbors) {
    for neighbor in nodeNeighbours[hub] {
      if !state.wavefront.contains(neighbor) && 
         !state.processedVertices.contains(neighbor) {
        hubNeighbors.add(neighbor);
      }
    }
  }
  
  // 2. Get diverse candidates (all non-selected vertices)
  forall v in 0..#state.ASconfig.n with (ref diverseCandidates) {
    if !state.wavefront.contains(v) && 
       !state.processedVertices.contains(v) &&
       !hubNeighbors.contains(v) {
      diverseCandidates.add(v);
    }
  }
  
  // Allocate from each category according to theory
  var hubNeighborTarget = (expansionSize * 0.4): int;
  var diverseTarget = (expansionSize * 0.4): int;
  var randomTarget = expansionSize - hubNeighborTarget - diverseTarget;
  
  // Select vertices from hub neighbors (40%)
  selectFromCandidates(state, hubNeighbors, hubNeighborTarget);
  
  // Select diverse vertices based on structural properties (40%)
  selectDiverseTheoretical(state, diverseCandidates, diverseTarget, nodeDegree, nodeNeighbours);
  
  // Select random vertices (20%)
  selectRandom(state, diverseCandidates - state.newVertices, randomTarget);
  
  writeln("=== Wavefront Expansion Complete ===");
  writeln("- Previous size: ", currentSize);
  writeln("- New wavefront size: ", state.wavefront.size);
  writeln("- Newly added vertices: ", state.newVertices.size);
}

/* Helper for selecting vertices from a candidate pool */
proc selectFromCandidates(ref state: WavefrontState, candidates: domain(int, parSafe=true), count: int) {
  var rng = new randomStream(real);
  var selected = 0;
  
  for v in candidates {
    if selected >= count then break;
    
    state.wavefront.add(v);
    state.newVertices.add(v);
    selected += 1;
  }
  
  writeln("  Selected ", selected, " vertices from candidate pool");
}

/* Helper for selecting diverse vertices with equal weighting */
proc selectDiverseTheoretical(ref state: WavefrontState, 
                             candidates: domain(int, parSafe=true), 
                             count: int,
                             ref nodeDegree: [] int,
                             ref nodeNeighbours: [] domain(int)) {
  // Scoring function with EQUAL weights
  proc calculateScore(v: int, maxDeg: real): real {
    var score = 0.0;
    
    // 1. Normalized degree (1/3 weight)
    var degreeScore = nodeDegree[v]:real / maxDeg;
    
    // 2. Clustering coefficient (1/3 weight)
    var clustering = 0.0;
    var neighbors = nodeNeighbours[v];
    var possibleEdges = neighbors.size * (neighbors.size - 1);
    
    if possibleEdges > 0 {
      var edgeCount = 0;
      for u in neighbors {
        for w in neighbors {
          if u != w && nodeNeighbours[u].contains(w) {
            edgeCount += 1;
          }
        }
      }
      clustering = edgeCount:real / possibleEdges:real;
    }
    
    // 3. Neighbor diversity (1/3 weight)
    var neighborDiversity = 0.0;
    if neighbors.size > 0 {
      var neighborRoles: [0..2] int = 0;
      for neighbor in neighbors {
        neighborRoles[state.vertexRoles[neighbor]] += 1;
      }
      
      // Calculate entropy
      for i in 0..2 {
        var p = neighborRoles[i]:real / neighbors.size:real;
        if p > 0 {
          neighborDiversity -= p * log(p);
        }
      }
      // Normalize to [0,1]
      neighborDiversity /= log(3.0);
    }
    
    // Combine scores with EQUAL weights
    score = (degreeScore + clustering + neighborDiversity) / 3.0;
    
    return score;
  }
  
  const maxDeg = max reduce nodeDegree;
  
  // Score candidates
  var candidateScores: [0..#candidates.size] (real, int); // (score, vertex)
  var idx = 0;
  
  for v in candidates {
    var score = calculateScore(v, maxDeg:real);
    candidateScores[idx] = (score, v);
    idx += 1;
  }
  
  // Sort by score (descending)
  sort(candidateScores, comparator=new ReverseComparator());
  
  // Take top scored vertices
  var selected = 0;
  for (score, v) in candidateScores {
    if selected >= count then break;
    
    state.wavefront.add(v);
    state.newVertices.add(v);
    selected += 1;
  }
  
  writeln("  Selected ", selected, " diverse vertices");
}

/* Helper for selecting random vertices */
proc selectRandom(ref state: WavefrontState, candidates: domain(int, parSafe=true), count: int) {
  var rng = new randomStream(real);
  var candidateArr: [0..#candidates.size] int;
  var idx = 0;
  
  for v in candidates {
    candidateArr[idx] = v;
    idx += 1;
  }
  
  // Shuffle array
  for i in 0..#candidateArr.size {
    var j = (rng.next() * candidateArr.size): int;
    var temp = candidateArr[i];
    candidateArr[i] = candidateArr[j];
    candidateArr[j] = temp;
  }
  
  // Take first 'count' elements
  var selected = 0;
  for i in 0..#min(count, candidateArr.size) {
    var v = candidateArr[i];
    state.wavefront.add(v);
    state.newVertices.add(v);
    selected += 1;
  }
  
  writeln("  Selected ", selected, " random vertices");
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
    } // End of initChildSet
  
    proc prepareNaugtyArguments(ref state: KavoshState) throws {
      if logLevel == LogLevel.DEBUG {
        writeln("===== prepareNaugtyArguments called =====");
      }
  
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
    } // End of prepareNaugtyArguments
  

  
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
        // Add vertices to flat list instead of forming arrays
        for level in 0..<state.k {
          const vertCount = state.getSubgraph(level, 0);
          for pos in 1..vertCount {
            state.motifVertices.pushBack(state.getSubgraph(level, pos));
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
    } // End of Explore
  
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
    } // End of swapping
  
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
    } // End of ForwardGenerator
  
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
    } // End of reverseGenerator
  
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
    } // End of patternToAdjMatrix
  
    /* This function takes a set of patterns (represented as uint64) and motif size,
       runs Nauty on each pattern to find canonical forms, and returns:
       1. A set of unique motif classes
       2. A flat array containing all adjacency matrices of the unique motifs
    */
/* Complete fixed verifyPatterns function */
proc verifyPatterns(globalMotifSet: set(uint(64)), 
                   globalMotifCounts: map(uint(64), atomic int),
                   motifSize: int) throws {
  var uniqueMotifClasses: set(uint(64));
  var uniqueMotifCounts: [0..#globalMotifSet.size] int;
  var motifCount = 0;
  
  writeln("\n=== Starting Pattern Verification ===");
  
  var motifArr: [0..#(globalMotifSet.size * motifSize * motifSize)] int;
  
  // Track the canonical patterns in an array for indexed access
  var patternArray: [0..#globalMotifSet.size] uint(64);
  
  // Process each pattern found
  var patternIdx = 0;
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
    var batchSize = 1; // We're processing one matrix at a time

    var status = c_nautyClassify(adjMatrix, motifSize, results, performCheck, verbose, batchSize);
    
    if status != 0 {
      writeln("Warning: Nauty failed with status ", status, " for pattern ", pattern);
      continue;
    }
    
    // Generate canonical pattern from Nauty's labeling
    var nautyPattern = generateNautyPattern(adjMatrix, results, motifSize);
    
    // Add the pattern if it's new
    var existingIdx = -1;
    for idx in 0..<patternIdx {
      if patternArray[idx] == nautyPattern {
        existingIdx = idx;
        break;
      }
    }
    
    if existingIdx == -1 {
      // New canonical pattern
      patternArray[patternIdx] = nautyPattern;
      uniqueMotifClasses.add(nautyPattern);
      
      // Add matrix to motifArr
      var startIdx = motifCount * motifSize * motifSize;
      var canonicalMatrix = patternToAdjMatrix(nautyPattern, motifSize);
      
      for i in 0..<(motifSize * motifSize) {
        motifArr[startIdx + i] = canonicalMatrix[i];
      }
      
      // Store its count
      var count = if globalMotifCounts.contains(pattern) then 
                    globalMotifCounts[pattern].read() 
                  else 0;
                  
      uniqueMotifCounts[patternIdx] = count;
      
      motifCount += 1;
      patternIdx += 1;
    } else {
      // Found existing canonical pattern - add its count to the existing one
      var count = if globalMotifCounts.contains(pattern) then 
                    globalMotifCounts[pattern].read() 
                  else 0;
                  
      uniqueMotifCounts[existingIdx] += count;
    }
  }
  
  // Create final arrays with correct sizes
  var finalMotifArr: [0..#(motifCount * motifSize * motifSize)] int;
  var finalCountArr: [0..#motifCount] int;
  
  // Copy data to final arrays with correct sizes
  for i in 0..<motifCount {
    finalCountArr[i] = uniqueMotifCounts[i];
  }
  
  for i in 0..#(motifCount * motifSize * motifSize) {
    finalMotifArr[i] = motifArr[i];
  }
  
  writeln("\n=== Verification Results ===");
  writeln("Started with total patterns: ", globalMotifSet.size);
  writeln("Found unique canonical patterns: ", uniqueMotifClasses.size);
  writeln("Filtered out non-canonical patterns: ", globalMotifSet.size - uniqueMotifClasses.size);
  
  writeln("\nCanonical patterns and their counts:");
  for i in 0..<motifCount {
    writeln("  Pattern: ", patternArray[i], " Count: ", finalCountArr[i]);
  }
  
  return (uniqueMotifClasses, finalMotifArr, finalCountArr);
}
  
    // New function to create pattern from adjMatrix and Nauty labeling
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

    var timer: stopwatch;

    writeln("**********************************************************************");
    writeln("**********************************************************************");
    writeln("Graph loaded:");
    writeln("Number of nodes: ", g1.n_vertices);
    writeln("Number of edges: ", g1.n_edges);
    writeln("Number of cores (max task parallelism): ", here.maxTaskPar);

    writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
    writeln("Maximum degree: ", maxDeg);

  // Execute the chosen algorithm
  //if doSampling == 1 {
    writeln("Using Adaptive Structural Wavefront Sampling");
    runASWSWithSwapping(g1.n_vertices, motifSize, nodeDegree, 
            nodeNeighbours, globalMotifCount, globalMotifSet, seenMatrices);
  //} else {
    // Complete enumeration
    //Enumerate(g1.n_vertices, motifSize, maxDeg);
  //}
 writeln(" globalMotifSet = ", globalMotifSet);
  writeln(" globalMotifCount = ", globalMotifCount.read());
  
  // Get the WavefrontState instance to access globalMotifCounts
  var ASconfig = new ASWSConfig(g1.n_vertices, motifSize);
  var state = new WavefrontState(ASconfig, maxDeg);
  
  // Execute pattern verification
  var (uniqueMotifClasses, finalMotifArr, motifCounts) = 
      verifyPatterns(globalMotifSet, state.globalMotifCounts, motifSize);
  

  var tempArr: [0..0] int;
  var srcPerMotif = makeDistArray(2*2, int);
  var dstPerMotif = makeDistArray(2*2, int);
  
  srcPerMotif[0] = uniqueMotifClasses.size;   // After verification
  srcPerMotif[1] = globalMotifSet.size;       // Before verification
  srcPerMotif[2] = globalMotifCount.read();   // All motifs
  srcPerMotif[3] = motifCounts.size;          // Unique pattern count
  
  // Output scaled frequency estimates
  writeln("\n=== Estimated Global Frequencies ===");
  var betaMin = calculateBetaMin(state);
  var scalingFactor = (g1.n_vertices:real / (betaMin * state.wavefront.size:real));
  
  writeln("- Scaling factor (n / (beta_min * |W|)): ", scalingFactor);
  writeln("Pattern\tSample Freq\tEstimated Total Freq");
  
  var patternIdx = 0;
  for pattern in uniqueMotifClasses {
    var sampleFreq = motifCounts[patternIdx];
    var estTotalFreq = sampleFreq:real * scalingFactor;
    writeln(pattern, "\t", sampleFreq, "\t", estTotalFreq:int);
    patternIdx += 1;
  }
  
  return (srcPerMotif, finalMotifArr, motifCounts, tempArr);

  } // End of runMotifCounting

} // End of MotifCounting Module
