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
 * Statistics tracking for motif frequencies in sampling-based motif counting
 * This record maintains:
 * - Pattern counts for each unique motif
 * - Total number of motifs found
 * - Number of vertices sampled
 * - Sum of squares for variance calculation
 */
record MotifFrequencyStats {
    /* Statistical tracking variables */
    var patternCounts: map(uint(64), atomic int);  // Maps motif patterns to their counts
    var totalMotifs: atomic int;                   // Total number of motifs found
    var sampledVertices: atomic int;               // Number of vertices sampled
    var sumSquares: atomic real;                   // For variance calculation
    
    proc init() {
        this.patternCounts = new map(uint(64), atomic int);
        init this;
        this.totalMotifs.write(0);
        this.sampledVertices.write(0);
        this.sumSquares.write(0.0);
    }
    
    proc ref updateStats(pattern: uint(64), count: int) {
        if !patternCounts.contains(pattern) {
            var newAtomic: atomic int;
            newAtomic.write(0);
            patternCounts.add(pattern, newAtomic);
        }
        patternCounts[pattern].add(count);
        totalMotifs.add(count);
        sumSquares.add(count:real * count:real);
        sampledVertices.add(1);
    }
    
    proc getVariance(): real {
        const n = sampledVertices.read();
        if n <= 1 then return 0.0;
        
        const mean = totalMotifs.read():real / n;
        return (sumSquares.read() - n * mean * mean) / (n - 1);
    }
    
    proc getStandardError(): real {
        const n = sampledVertices.read();
        if n == 0 then return 0.0;
        return sqrt(getVariance() / n);
    }
    
    proc getMean(): real {
        const n = sampledVertices.read();
        if n == 0 then return 0.0;
        return totalMotifs.read():real / n;
    }
    
    proc getConfidenceInterval(confidenceLevel: real): (real, real) {
        const mean = getMean();
        const stderr = getStandardError();
        const z = getZScore(confidenceLevel);
        const margin = z * stderr;
        
        return (mean - margin, mean + margin);
    }
    
    proc getUniquePatternCount(): int {
        return patternCounts.size;
    }
    
    proc hasReliableStats(): bool {
        return sampledVertices.read() >= 30;  // Central Limit Theorem minimum
    }
}
/*
* Configuration record for sampling parameters
* Manages sampling configuration and validation for motif census
* Includes parameters for statistical confidence, stratification,
* and adaptive sampling strategies
*/
record SamplingConfig {
   /* Statistical parameters for sampling confidence */
   var confidenceLevel: real = 0.95;    // Confidence level (e.g., 0.95 for 95% confidence interval)
   var marginOfError: real = 0.1;       // Acceptable margin of error (e.g., 0.1 for ±10%)
   var pilotFraction: real = 0.05;      // Initial sampling fraction for pilot phase
   
   /* Stratification control parameters */
   var numStrata: int = 3;              // Number of strata for stratified sampling
   var strategyType: string = "degree"; // Stratification strategy ("degree" or "uniform")
   var minSampleSize: int = 30;         // Minimum samples per stratum (for CLT validity)
   var minStratumSize: int = 100;       // Minimum stratum size for valid stratification
   
   /* Adaptive sampling parameters */
   var adaptiveBoundaries: bool = true;      // Enable/disable dynamic boundary adjustment
   var reStratificationThreshold: real = 0.2; // Variance change threshold for re-stratification
   
   /* Effective sampling range */
   var effectiveN: int;                 // N-K: Maximum valid vertex index for k-size motifs
   
   /*
    * Initialize sampling configuration
    * Parameters:
    * - totalVertices: Total number of vertices in graph
    * - motifSize: Size of motifs to be counted
    */
    proc init(totalVertices: int, motifSize: int) {
        // Validate input parameters
        if totalVertices <= motifSize then
            halt("Error: Motif size must be smaller than graph size");
        
        // Initialize in declaration order
        this.confidenceLevel = 0.95;
        this.marginOfError = 0.1;
        this.pilotFraction = 0.05;
        
        // Calculate numStrata first using a local variable
        var calculatedStrata = min(3, (totalVertices - motifSize) / 100); // Using 100 as default minStratumSize
        this.numStrata = calculatedStrata;
        
        this.strategyType = "degree";
        this.minSampleSize = 30;
        this.minStratumSize = 100;
        this.adaptiveBoundaries = true;
        this.reStratificationThreshold = 0.2;
        this.effectiveN = totalVertices - motifSize;
        
        // Any adjustments can now be done after complete()
        init this;
        
        // Additional validation and adjustments if needed
        if this.effectiveN < this.minStratumSize * this.numStrata {
            this.numStrata = max(1, this.effectiveN / this.minStratumSize);
            this.minStratumSize = max(10, this.effectiveN / this.numStrata);
        }
    }
    
   /*
    * Validate configuration parameters
    * Returns: true if configuration is valid, false otherwise
    */
   proc isValid(): bool {
       // Validate statistical parameters
       if confidenceLevel <= 0.0 || confidenceLevel >= 1.0 then return false;
       if marginOfError <= 0.0 || marginOfError >= 1.0 then return false;
       if pilotFraction <= 0.0 || pilotFraction >= 1.0 then return false;
       
       // Validate stratification parameters
       if numStrata < 1 then return false;
       if minSampleSize < 1 then return false;
       if minStratumSize < minSampleSize then return false;
       
       // Validate effective range
       if effectiveN < 1 then return false;
       if effectiveN < numStrata * minSampleSize then return false;
       
       // Validate strategy type
       if strategyType != "degree" && strategyType != "uniform" then return false;
       
       return true;
   }
   
   /*
    * Get recommended sample size based on configuration
    * Returns: Recommended total sample size
    */
   proc getRecommendedSampleSize(): int {
       var z = getZScore(confidenceLevel);
       var baseSize = ((z * z) / (4 * marginOfError * marginOfError)):int;
       return min(effectiveN, max(minSampleSize * numStrata, baseSize));
   }
   
   /*
    * Adjust configuration for small graphs
    * Returns: true if adjustments were made
    */
   proc adjustForSmallGraph(): bool {
       if effectiveN < 1000 {  // Threshold for "small" graphs
           numStrata = max(1, min(numStrata, effectiveN / 100));
           minSampleSize = max(5, min(minSampleSize, effectiveN / (numStrata * 2)));
           pilotFraction = max(0.1, pilotFraction * 2);
           return true;
       }
       return false;
   }
}
/*
 * Stratum record for managing vertex groups
 */
record Stratum {
   var id: int;
   var size: atomic int;
   var sampleSize: atomic int;
   var vertices: domain(int, parSafe=true);
   var validSamples: atomic int;
   var lowerBound: atomic int;
   var upperBound: atomic int;
   var motifStats: MotifFrequencyStats;
   
   proc init(id: int) {
       this.id = id;
       this.vertices = {1..0};
       init this;
       this.size.write(0);
       this.sampleSize.write(0);
       this.validSamples.write(0);
       this.lowerBound.write(0);
       this.upperBound.write(max(int));
       this.motifStats = new MotifFrequencyStats();
   }
    
    proc calculateRequiredSize(confidence: real, marginError: real): int {
        const variance = motifStats.getVariance();
        const z = getZScore(confidence);
        return ((z * z * variance) / (marginError * marginError)): int;
    }
    
    proc isValid(Sconfig: SamplingConfig): (bool, string) {
        const currentSize = size.read();
        if currentSize < Sconfig.minStratumSize {
            return (false, "Stratum " + id:string + " size (" + currentSize:string + 
                   ") below minimum required (" + Sconfig.minStratumSize:string + ")");
        }
        return (true, "");
    }
}

/*
 * Main class for managing sampling state
 */
class SamplingState {
    var Sconfig: SamplingConfig;
    var strata: [0..#Sconfig.numStrata] Stratum;
    var totalSampledVertices: atomic int;
    var stratificationVersion: atomic int; // Track re-stratification
    
    proc init(Sconfig: SamplingConfig) {
        this.Sconfig = Sconfig;
        this.strata = [i in 0..#Sconfig.numStrata] new Stratum(i);
        init this;
        this.totalSampledVertices.write(0);
        this.stratificationVersion.write(0);
    }
    
    proc validateState(): (bool, string) {
        var totalSamples = this.totalSampledVertices.read();
        if totalSamples < Sconfig.minSampleSize {
            return (false, "Insufficient total samples: " + totalSamples:string);
        }
        
        var errorMsg: string;
        var hasError = false;
        
        forall stratum in strata with (ref errorMsg, ref hasError) {
            var (valid, msg) = stratum.isValid(Sconfig);
            if !valid {
                hasError = true;
                errorMsg += msg + " ";
            }
        }
        
        if hasError then return (false, errorMsg);
        return (true, "");
    }
    
    proc needsReStratification(): bool {
        if !Sconfig.adaptiveBoundaries then return false;
        
        var maxVariance = max reduce [s in strata] s.motifStats.getVariance();
        var minVariance = min reduce [s in strata] s.motifStats.getVariance();
        
        if maxVariance == 0.0 then return false;
        return (maxVariance - minVariance) / maxVariance > Sconfig.reStratificationThreshold;
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

/*
 * Enhanced statistical calculations for stratified sampling
 * Implements proper variance estimation and CLT requirements
 */
class StratifiedStats {
    const numStrata: int;  // Store number of strata
    
    /* Per-stratum statistics */
    var stratumMeans: [0..#numStrata] atomic real;
    var stratumVariances: [0..#numStrata] atomic real;
    var effectiveSampleSizes: [0..#numStrata] atomic int;
    var designEffects: [0..#numStrata] atomic real;  // For measuring sampling efficiency
    
    /* Global statistics */
    var globalMean: atomic real;
    var globalVariance: atomic real;
    var standardError: atomic real;
    
    /* CLT validation */
    var normalityScore: atomic real;
    var minimumSampleSizesMet: atomic bool;
    
    proc init(numStrata: int) {
        this.numStrata = numStrata;
        init this;  // Required after initializing const fields
        
        // Initialize atomic arrays
        forall i in 0..#numStrata {
            this.stratumMeans[i].write(0.0);
            this.stratumVariances[i].write(0.0);
            this.effectiveSampleSizes[i].write(0);
            this.designEffects[i].write(1.0);
        }
    }
    
    /*
     * Check if CLT requirements are met
     * Returns: (bool, string) - (requirements met, explanation)
     */
    proc validateCLTRequirements(): (bool, string) {
        var minSamplesPerStratum = min reduce [e in effectiveSampleSizes] e.read();
        var totalSamples = + reduce [e in effectiveSampleSizes] e.read();
        
        if minSamplesPerStratum < 30 {
            return (false, "Minimum samples per stratum (30) not met. Current minimum: " + 
                   minSamplesPerStratum:string);
        }
        
        if totalSamples < 50 {
            return (false, "Total sample size too small for CLT approximation");
        }
        
        var maxDeff = max reduce [d in designEffects] d.read();
        if maxDeff > 3.0 {
            return (false, "Design effect too large, indicating inefficient sampling");
        }
        
        return (true, "CLT requirements met");
    }
    
    /*
     * Calculate stratified variance using proper formula
     * Implements unbiased variance estimation for stratified sampling
     */
    proc calculateStratifiedVariance(samplingState: borrowed SamplingState): real {
        var totalVariance = 0.0;
        var totalSize = + reduce [s in samplingState.strata] s.size.read();
        
        forall stratum in samplingState.strata with (+ reduce totalVariance) {
            var strataSize = stratum.size.read():real;
            var weight = strataSize / totalSize;
            var variance = stratum.motifStats.getVariance();
            
            // Finite population correction
            var fpc = (strataSize - stratum.sampleSize.read()) / strataSize;
            
            // Add weighted variance component
            totalVariance += (weight * weight * variance * fpc) / stratum.sampleSize.read();
        }
        
        return totalVariance;
    }
    
    /*
     * Calculate design effect for each stratum
     * Measures the efficiency of the stratified design compared to SRS
     */
    proc updateDesignEffects(samplingState: borrowed SamplingState) {
        forall (stratum, deff) in zip(samplingState.strata, designEffects) {
            var variance = stratum.motifStats.getVariance();
            var n = stratum.sampleSize.read();
            if n > 1 {
                var srs_var = variance / (n - 1);
                var strat_var = calculateStratumVariance(stratum);
                deff.write(strat_var / srs_var);
            }
        }
    }
    
    /*
     * Implements Neyman allocation with proper statistical foundations
     */
    proc calculateNeymanAllocation(samplingState: borrowed SamplingState, 
                                 totalSampleSize: int): [] int {
        var numStrata = samplingState.Sconfig.numStrata;
        var allocation: [0..#numStrata] int;
        var totalWeight = 0.0;
        
        // Calculate stratum weights using population SD (not variance)
        forall stratum in samplingState.strata with (+ reduce totalWeight) {
            var strataSize = stratum.size.read();
            var stdDev = sqrt(stratum.motifStats.getVariance());
            var weight = strataSize * stdDev;
            totalWeight += weight;
        }
        
        // Allocate samples using Neyman's formula
        forall (stratum, size) in zip(samplingState.strata, allocation) {
            var strataSize = stratum.size.read();
            var stdDev = sqrt(stratum.motifStats.getVariance());
            var weight = strataSize * stdDev;
            
            if totalWeight > 0.0 {
                size = (totalSampleSize * (weight / totalWeight)): int;
                
                // Apply finite population correction
                var fpc = sqrt((strataSize - size) / strataSize);
                size = (size * fpc): int;
            } else {
                // Fallback to proportional allocation if no variance information
                size = (totalSampleSize * (strataSize:real / 
                       samplingState.totalSampledVertices.read())): int;
                       writeln("samplingState.totalSampledVertices inside calculateNeymanAllocation ", samplingState.totalSampledVertices.read());
            }
            
            // Ensure minimum size requirements
            size = max(size, samplingState.Sconfig.minSampleSize);
        }
        
        return allocation;
    }
    
    /*
     * Calculate confidence interval using proper stratified sampling theory
     */
    proc calculateConfidenceInterval(samplingState: borrowed SamplingState): (real, real) {
        var variance = calculateStratifiedVariance(samplingState);
        var standardError = sqrt(variance);
        
        var z = getZScore(samplingState.Sconfig.confidenceLevel);
        var estimate = globalMean.read();
        
        var margin = z * standardError;
        return (estimate - margin, estimate + margin);
    }
    
    /*
     * Test for approximate normality using Shapiro-like criterion
     */
    proc checkNormality(samplingState: borrowed SamplingState): bool {
        var normalityScore = 0.0;
        var totalWeight = 0.0;
        
        forall stratum in samplingState.strata with (+ reduce normalityScore,
                                                    + reduce totalWeight) {
            if stratum.validSamples.read() >= 30 {
                var weight = stratum.size.read():real;
                normalityScore += weight * calculateStratumNormalityScore(stratum);
                totalWeight += weight;
            }
        }
        
        if totalWeight > 0.0 {
            normalityScore /= totalWeight;
        }
        
        this.normalityScore.write(normalityScore);
        return normalityScore > 0.95;  // Threshold for approximate normality
    }
    
    /*
     * Calculate normality score for a stratum using skewness and kurtosis
     */
    proc calculateStratumNormalityScore(stratum: Stratum): real {
        const n = stratum.validSamples.read();
        if n < 30 then return 0.0;
        
        var mean = stratum.motifStats.totalMotifs.read():real / n;
        var variance = stratum.motifStats.getVariance();
        var stdDev = sqrt(variance);
        
        if stdDev == 0.0 then return 1.0;  // Perfect normality for constant values
        
        // Calculate skewness and kurtosis
        var skewness = calculateSkewness(stratum, mean, stdDev);
        var kurtosis = calculateKurtosis(stratum, mean, stdDev);
        
        // Convert to normality score (1.0 = perfectly normal)
        var score = 1.0 - (abs(skewness) / 2.0) - (abs(kurtosis - 3.0) / 6.0);
        return max(0.0, score);
    }
}
/*
 * Comprehensive statistical validation module
 * Ensures sampling maintains statistical validity throughout the process
 */
class SamplingValidator {
    var stats: owned StratifiedStats;
    var validationHistory: [0..#100] real;  // Circular buffer for tracking
    var historyIndex: atomic int;
    const stabilityThreshold = 0.05;        // 5% change threshold
    
    proc init(numStrata: int) {
    this.stats = new owned StratifiedStats(numStrata);
    this.validationHistory = 0.0;
    init this;
    this.historyIndex.write(0);
    }
    
    /*
     * Comprehensive validation of sampling process
     * Returns: (bool, string) - (isValid, detailed message)
     */
    proc validateSampling(samplingState: borrowed SamplingState): (bool, string) {
        // Check CLT requirements
        var (cltValid, cltMsg) = stats.validateCLTRequirements();
        if !cltValid {
            return (false, "CLT requirements not met: " + cltMsg);
        }
        
        // Validate stratum sizes and sampling fractions
        var (strataValid, strataMsg) = validateStrata(samplingState);
        if !strataValid {
            return (false, "Stratum validation failed: " + strataMsg);
        }
        
        // Check estimate stability
        var (stable, stabilityMsg) = checkEstimateStability();
        if !stable {
            return (false, "Estimate stability issues: " + stabilityMsg);
        }
        
        // Verify statistical power
        var (powerValid, powerMsg) = validateStatisticalPower(samplingState);
        if !powerValid {
            return (false, "Insufficient statistical power: " + powerMsg);
        }
        
        return (true, "All statistical validations passed");
    }
    
    /*
     * Validate stratum-level statistics
     */
    proc validateStrata(samplingState: borrowed SamplingState): (bool, string) {
        var minValidSamples = max(30, samplingState.Sconfig.minSampleSize);
        var errorMsg: string;
        var isValid = true;
        
        forall stratum in samplingState.strata with (ref errorMsg, ref isValid) {
            // Check sample size
            if stratum.validSamples.read() < minValidSamples {
                errorMsg += "Stratum " + stratum.id:string + 
                          " has insufficient samples. ";
                isValid = false;
                continue;
            }
            
            // Check sampling fraction
            var samplingFraction = stratum.validSamples.read():real / 
                                 stratum.size.read():real;
            if samplingFraction < 0.01 {  // Minimum 1% sampling
                errorMsg += "Stratum " + stratum.id:string + 
                          " has too low sampling fraction. ";
                isValid = false;
            }
            
            // Check variance estimation reliability
            var variance = stratum.motifStats.getVariance();
            if variance == 0.0 && stratum.validSamples.read() > minValidSamples {
                errorMsg += "Stratum " + stratum.id:string + 
                          " shows suspicious zero variance. ";
                isValid = false;
            }
        }
        
        return (isValid, errorMsg);
    }
    
    /*
     * Check if estimates have stabilized
     */
    proc checkEstimateStability(): (bool, string) {
        const historySize = historyIndex.read();
        if historySize < 10 then return (false, "Insufficient history for stability check");
        
        var recentEstimates = validationHistory[max(0, historySize-10)..historySize-1];
        var meanEstimate = (+ reduce recentEstimates) / recentEstimates.size;
        var maxDeviation = max reduce abs(recentEstimates - meanEstimate);
        
        if maxDeviation / meanEstimate > stabilityThreshold {
            return (false, "Estimates haven't stabilized. Current deviation: " + 
                   (maxDeviation / meanEstimate * 100):string + "%");
        }
        
        return (true, "Estimates have stabilized");
    }
    
    /*
     * Validate statistical power
     */
    proc validateStatisticalPower(samplingState: borrowed SamplingState): (bool, string) {
        const desiredPower = 0.8;  // Standard 80% power
        const alpha = 1.0 - samplingState.Sconfig.confidenceLevel;
        
        var achievedPower = calculateAchievedPower(samplingState, alpha);
        
        if achievedPower < desiredPower {
            return (false, "Power (" + (achievedPower * 100):string + 
                   "%) below target (" + (desiredPower * 100):string + "%)");
        }
        
        return (true, "Sufficient statistical power achieved");
    }
    
    /*
     * Calculate achieved statistical power
     */
    proc calculateAchievedPower(samplingState: borrowed SamplingState, 
                              alpha: real): real {
        var variance = stats.calculateStratifiedVariance(samplingState);
        if variance == 0.0 then return 1.0;
        
        var standardError = sqrt(variance);
        var effectSize = stats.globalMean.read() * samplingState.Sconfig.marginOfError;
        
        // Calculate non-centrality parameter
        var Slambda = effectSize / standardError;
        
        // Approximate power using normal distribution
        var zAlpha = getZScore(1.0 - alpha/2);
        var zBeta = Slambda - zAlpha;
        
        // Convert to power
        return 1.0 - normcdf(-zBeta);
    }
    
    /*
     * Update validation history
     */
    proc updateHistory(currentEstimate: real) {
        var idx = historyIndex.fetchAdd(1) % validationHistory.size;
        validationHistory[idx] = currentEstimate;
    }
}

/*
 * Enhanced dynamic adjustment with statistical guidance
 */
class DynamicAdjuster {
    var validator: owned SamplingValidator;
    var adjustmentHistory: [0..#10] real;  // Track recent adjustments
    var historyIndex: atomic int;
    const maxAdjustmentRate = 0.25;        // Maximum 25% change per adjustment
    
    proc init(numStrata: int) {
    this.validator = new owned SamplingValidator(numStrata);
    this.adjustmentHistory = 0.0;
    init this;
    this.historyIndex.write(0);
    }
    
    /*
     * Calculate optimal adjustment based on current statistics
     */
    proc calculateAdjustment(samplingState: borrowed SamplingState): [] real {
        var numStrata = samplingState.Sconfig.numStrata;
        var adjustments: [0..#numStrata] real;
        
        // Get current statistical state
        var (valid, _) = validator.validateSampling(samplingState);
        
        if !valid {
            // Calculate required increases based on statistical needs
            forall (stratum, adj) in zip(samplingState.strata, adjustments) {
                var currentSize = stratum.sampleSize.read();
                var variance = stratum.motifStats.getVariance();
                var stdError = sqrt(variance / currentSize);
                
                // Calculate required size for target precision
                var targetSize = getTargetSize(stratum, stdError, 
                                            samplingState.Sconfig);
                
                // Calculate smooth adjustment
                adj = calculateSmoothAdjustment(currentSize, targetSize);
            }
            
            // Record adjustment
            recordAdjustment(max reduce abs(adjustments));
        }
        
        return adjustments;
    }
    
    /*
     * Calculate smooth adjustment factor
     */
    proc calculateSmoothAdjustment(current: int, target: int): real {
        var rawAdjustment = (target - current):real / current:real;
        
        // Limit rate of change
        var smoothedAdjustment = sign(rawAdjustment) * 
                                min(abs(rawAdjustment), maxAdjustmentRate);
        
        // Consider adjustment history
        var recentMean = calculateRecentAdjustmentMean();
        if recentMean * smoothedAdjustment > 0 {  // Same direction
            smoothedAdjustment *= 0.8;  // Dampen oscillations
        }
        
        return smoothedAdjustment;
    }
    
    /*
     * Calculate target sample size based on statistical needs
     */
    proc getTargetSize(stratum: Stratum, currentError: real, 
                      Sconfig: SamplingConfig): int {
        var z = getZScore(Sconfig.confidenceLevel);
        var targetError = Sconfig.marginOfError * stratum.motifStats.getMean();
        
        var requiredSize = (z * z * stratum.motifStats.getVariance()) / 
                          (targetError * targetError);
                          
        // Apply finite population correction
        var fpc = (stratum.size.read() - requiredSize) / stratum.size.read();
        requiredSize = (requiredSize / fpc): int;
        
        return max(requiredSize, Sconfig.minSampleSize);
    }
    
    /*
     * Record adjustment for history
     */
    proc recordAdjustment(adjustmentMagnitude: real) {
        var idx = historyIndex.fetchAdd(1) % adjustmentHistory.size;
        adjustmentHistory[idx] = adjustmentMagnitude;
    }
    
    /*
     * Calculate mean of recent adjustments
     */
    proc calculateRecentAdjustmentMean(): real {
        const historySize = min(historyIndex.read(), adjustmentHistory.size);
        if historySize == 0 then return 0.0;
        
        return (+ reduce adjustmentHistory[0..#historySize]) / historySize;
    }
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
      // Collect all neighbors (both in and out) in a domain
      nodeNeighbours[v] = neighbours;
    }
    var maxDeg = max reduce nodeDegree;


    // All motif counting and classify variables
    var globalMotifCount: atomic int;
    var globalClasses: set(uint(64), parSafe=true);
    // Initiate it to 0
    globalMotifCount.write(0);

    var useSampling:bool = true;
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
/*
 * Creates initial stratification based on configuration
 * Returns: A new SamplingState instance
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
        when "uniform" {
            stratifyUniformly(n, motifSize, samplingState); //n: int, k: int, ref samplingState: SamplingState
        }
        otherwise {
            throw new Error("Unknown stratification strategy: " + Sconfig.strategyType);
        }
    }
    
    // Validate strata
    var (valid, errorMsg) = samplingState.validateState();
    if !valid {
        writeln("Warning: Initial stratification validation failed - ", errorMsg);
    }
    
    if logLevel == LogLevel.DEBUG {
        printStratificationStats(samplingState);
    }
    
    return samplingState;
}

/*
 * Stratifies vertices based on their degrees
 * Divides vertices into strata based on degree ranges
 */
proc stratifyByDegree(n: int, ref nodeDegree: [] int, ref samplingState: SamplingState) {
    // Only consider vertices up to N-K
    const maxValidVertex = n - k;

    // First, filter out zero-degree vertices and sort degrees
    var validDegrees: [0..#maxValidVertex] int;
    var validVertices: [0..#maxValidVertex] int;
    var validCount: atomic int;
    
    forall i in 0..#maxValidVertex with (ref validCount) {
        if nodeDegree[i] > 0 {
            const idx = validCount.fetchAdd(1);
            validDegrees[idx] = nodeDegree[i];
            validVertices[idx] = i;
        }
    }
    
    // Get actual count of valid vertices
    const actualValidCount = validCount.read();
    
    // Calculate degree boundaries for stratification
    var sortedDegrees = nodeDegree[0..maxValidVertex];  // Only consider valid vertices
    sort(sortedDegrees);
    
    // Calculate stratum boundaries
    var boundaries: [0..#(samplingState.Sconfig.numStrata-1)] int;
    for i in 0..#(samplingState.Sconfig.numStrata-1) {
        var idx = ((i + 1) * actualValidCount / samplingState.Sconfig.numStrata): int;
        boundaries[i] = sortedDegrees[idx];
    }
    
    // Initialize stratum bounds
    samplingState.strata[0].lowerBound.write(1);  // Minimum valid degree
    samplingState.strata[0].upperBound.write(boundaries[0]);
    
    for i in 1..#(samplingState.Sconfig.numStrata-1) {
        samplingState.strata[i].lowerBound.write(boundaries[i-1] + 1);
        samplingState.strata[i].upperBound.write(boundaries[i]);
    }
    
    // Last stratum upper bound is max degree
    const lastIdx = samplingState.Sconfig.numStrata-1;
    samplingState.strata[lastIdx].lowerBound.write(boundaries[lastIdx-1] + 1);
    samplingState.strata[lastIdx].upperBound.write(max reduce nodeDegree);
    
    // Assign vertices to strata
    forall v in 0..#maxValidVertex {  // Changed from n to maxValidVertex
        if nodeDegree[v] > 0 {  // Skip zero-degree vertices
            var assigned = false;
            for stratum in samplingState.strata {
                if nodeDegree[v] >= stratum.lowerBound.read() && 
                   nodeDegree[v] <= stratum.upperBound.read() {
                    stratum.vertices.add(v);
                    stratum.size.add(1);
                    assigned = true;
                    break;
                }
            }
            
            if !assigned && logLevel == LogLevel.DEBUG {
                writeln("Warning: Vertex ", v, " with degree ", nodeDegree[v], 
                       " not assigned to any stratum");
            }
        }
    }
    
    // Set initial sample sizes based on pilot fraction
    setInitialSampleSizes(samplingState);
}

/*
 * Stratifies vertices uniformly across strata
 */
proc stratifyUniformly(n: int, k: int, ref samplingState: SamplingState) {
    const maxValidVertex = n - k;
    var verticesPerStratum = (maxValidVertex / samplingState.Sconfig.numStrata): int;
    var remainingVertices = maxValidVertex % samplingState.Sconfig.numStrata;

    // Calculate stratum sizes accounting for remainder
    var stratumSizes: [0..#samplingState.Sconfig.numStrata] int;
    for i in 0..#samplingState.Sconfig.numStrata {
        stratumSizes[i] = verticesPerStratum;
        if i < remainingVertices then stratumSizes[i] += 1;
    }
    
    var startIndex = 0;
    for i in 0..#samplingState.Sconfig.numStrata {
        ref stratum = samplingState.strata[i];
        var size = stratumSizes[i];
        var endIndex = startIndex + size;
        
        for v in startIndex..<endIndex {
            stratum.vertices.add(v);
        }
        stratum.size.write(size);
        startIndex = endIndex;
    }
    // Set initial sample sizes
    setInitialSampleSizes(samplingState);
}


/*
 * Sets initial sample sizes for all strata
 */
proc setInitialSampleSizes(ref samplingState: SamplingState) {
    forall stratum in samplingState.strata {
        var initialSize = (stratum.size.read() * samplingState.Sconfig.pilotFraction): int;
        // Ensure minimum sample size
        initialSize = max(initialSize, samplingState.Sconfig.minSampleSize);
        // Ensure we don't sample more than stratum size
        initialSize = min(initialSize, stratum.size.read());
        stratum.sampleSize.write(initialSize);
    }
}

/*
 * Prints detailed statistics about current stratification
 */
proc printStratificationStats(samplingState: borrowed SamplingState) {
    writeln("Stratification Statistics:");
    writeln("Strategy: ", samplingState.Sconfig.strategyType);
    writeln("Number of strata: ", samplingState.Sconfig.numStrata);
    writeln();
    
    for stratum in samplingState.strata {
        writeln("Stratum ", stratum.id, ":");
        writeln("  Size: ", stratum.size.read());
        writeln("  Initial sample size: ", stratum.sampleSize.read());
        if samplingState.Sconfig.strategyType == "degree" {
            writeln("  Degree range: [", stratum.lowerBound.read(), 
                   ", ", stratum.upperBound.read(), "]");
        }
        writeln("  Number of vertices: ", stratum.vertices.size);
        writeln();
    }
}

/*
 * Main sampling-based enumeration process
 * This integrates sampling with the existing Kavosh exploration
 */
proc SampledEnumerate(n: int, k: int, maxDeg: int,
                     ref samplingState: SamplingState,
                     ref globalMotifCount: atomic int,
                     ref globalClasses: set(uint(64), parSafe=true)) throws {
    
    // First create domain to hold all sampled vertices
    var sampledVertices: domain(int, parSafe=true);
    
    // Sample vertices from each stratum
    forall stratum in samplingState.strata with (ref sampledVertices) {
        var targetSize = stratum.sampleSize.read();
        var currentSize = stratum.size.read();
        
        // Use reservoir sampling within each stratum
        forall v in stratum.vertices with (ref sampledVertices, 
                                         var rng = new randomStream(real)) {
            if rng.getNext() <= (targetSize:real / currentSize) {
                sampledVertices.add(v);
            }
        }
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Selected ", sampledVertices.size, " vertices for sampling");
        writeln("Distribution across strata:");
        for stratum in samplingState.strata {
            var count = + reduce [v in sampledVertices] stratum.vertices.contains(v);
            writeln("  Stratum ", stratum.id, ": ", count, " vertices");
        }
    }
    
    // Now explore from each sampled vertex
    forall v in sampledVertices with (ref globalClasses, ref globalMotifCount) {
        var state = new KavoshState(n, k, maxDeg);
        
        // Initialize root vertex
        state.setSubgraph(0, 0, 1);      // Set count to 1
        state.setSubgraph(0, 1, v);      // Set the vertex
        state.visited.clear();           
        state.visited.add(v);
        
        // Find the stratum this vertex belongs to
        var stratumId = -1;
        for (id, stratum) in zip(0..#samplingState.strata.size, samplingState.strata) {
            if stratum.vertices.contains(v) {
                stratumId = id;
                break;
            }
        }
        
        if stratumId == -1 {
            halt("Error: Sampled vertex ", v, " not found in any stratum");
        }
        
        // Explore from this vertex
        Explore(state, v, 1, k - 1);
        
        // Update stratum statistics
        ref stratum = samplingState.strata[stratumId];
        stratum.motifStats.updateStats(state.localmotifClasses.size:uint(64), 
                                     state.localsubgraphCount);
        
        // Calculate scaling factor for this stratum
        var scaleFactor = calculateScaleFactor(stratum.size.read(), 
                                             stratum.sampleSize.read());
        
        // Update global counts with scaling
        var scaledCount = (state.localsubgraphCount:real * scaleFactor):int;
        globalMotifCount.add(scaledCount);
        globalClasses += state.localmotifClasses;
    }
    
    // Calculate and report statistical confidence
    reportSamplingStatistics(samplingState);
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
 * Calculate overall standard error across all strata
 */
proc calculateOverallStandardError(samplingState: borrowed SamplingState): real {
    var weightedVariance = 0.0;
    var totalWeight = 0.0;
    
    forall stratum in samplingState.strata with (+ reduce weightedVariance,
                                               + reduce totalWeight) {
        const weight = stratum.size.read():real;
        weightedVariance += weight * stratum.motifStats.getVariance();
        totalWeight += weight;
    }
    
    if totalWeight == 0.0 then return 0.0;
    return sqrt(weightedVariance / totalWeight);
}
/*
 * Adjust sample sizes with N-K consideration
 */
proc adjustSampleSizes(ref samplingState: SamplingState, currentProgress: real): bool {
    const effectiveN = samplingState.Sconfig.effectiveN;
    
    // Don't adjust if we haven't sampled enough for reliable estimates
    const minSamplesForAdjustment = samplingState.Sconfig.minSampleSize * 2;
    var totalSampled = + reduce [s in samplingState.strata] 
                       min(s.validSamples.read(), effectiveN - s.id * effectiveN/samplingState.Sconfig.numStrata);
    
    if totalSampled < minSamplesForAdjustment then return false;
    
    // Calculate new sizes considering N-K limit
    var newSizes = calculateOptimalSampleSizes(samplingState);
    var needsAdjustment = false;
    
    forall (stratum, newSize) in zip(samplingState.strata, newSizes) 
    with (|| reduce needsAdjustment) {
        // Ensure we don't exceed effective N in any stratum
        newSize = min(newSize, effectiveN - stratum.id * effectiveN/samplingState.Sconfig.numStrata);
        var currentSize = stratum.sampleSize.read();
        var changeFraction = abs(newSize - currentSize):real / currentSize:real;
        
        if changeFraction > 0.2 {  // 20% threshold for adjustment
            needsAdjustment = true;
        }
    }
    
    if needsAdjustment {
        implementSampleSizeChanges(samplingState, newSizes);
        return true;
    }
    
    return false;
}

/*
 * Calculate optimal sample sizes using Neyman allocation
 */
proc calculateOptimalSampleSizes(samplingState: borrowed SamplingState): [] int {
    var numStrata = samplingState.Sconfig.numStrata;
    var newSizes: [0..#numStrata] int;
    var totalWeight = 0.0;
    
    // Calculate Neyman weights (Nh * Sh)
    forall stratum in samplingState.strata with (+ reduce totalWeight) {
        var strataSize = stratum.size.read();
        var stdDev = sqrt(stratum.motifStats.getVariance());
        var weight = strataSize * stdDev;
        totalWeight += weight;
    }
    
    // Calculate minimum total sample size needed for desired precision
    var requiredTotalSamples = calculateRequiredTotalSamples(samplingState);
    
    // Allocate samples based on Neyman allocation
    forall (stratum, size) in zip(samplingState.strata, newSizes) {
        var strataSize = stratum.size.read();
        var stdDev = sqrt(stratum.motifStats.getVariance());
        var weight = strataSize * stdDev;
        
        if totalWeight > 0.0 {
            size = (requiredTotalSamples * (weight / totalWeight)): int;
        } else {
            // If no variance information, allocate proportionally to stratum size
            size = (requiredTotalSamples * (strataSize:real / 
                   samplingState.totalSampledVertices.read())): int;
            writeln("samplingState.totalSampledVertices inside calculateOptimalSampleSizes ", samplingState.totalSampledVertices.read());

        }
        
        // Ensure minimum and maximum constraints
        size = max(size, samplingState.Sconfig.minSampleSize);
        size = min(size, strataSize);
    }
    
    return newSizes;
}

/*
 * Calculate required total samples considering N-K limit
 */
proc calculateRequiredTotalSamples(samplingState: borrowed SamplingState): int {
    var z = getZScore(samplingState.Sconfig.confidenceLevel);
    var e = samplingState.Sconfig.marginOfError;
    const effectiveN = samplingState.Sconfig.effectiveN;
    
    // Calculate pooled variance
    var totalVariance = 0.0;
    var totalValidSize = 0;
    
    forall stratum in samplingState.strata with (+ reduce totalVariance,
                                               + reduce totalValidSize) {
        // Only consider vertices within N-K limit
        var validSize = min(stratum.size.read(), effectiveN);
        totalVariance += validSize * stratum.motifStats.getVariance();
        totalValidSize += validSize;
    }
    
    if totalValidSize == 0 then return samplingState.Sconfig.minSampleSize;
    
    var avgVariance = totalVariance / totalValidSize;
    
    // Use sample size formula with finite population correction
    var numerator = (z * z * avgVariance * effectiveN);
    var denominator = (e * e * (effectiveN - 1) + z * z * avgVariance);
    
    var requiredSize = (numerator / denominator): int;
    
    // Ensure minimum sample size and don't exceed effective N
    return min(effectiveN, 
              max(requiredSize, 
                  samplingState.Sconfig.minSampleSize * samplingState.Sconfig.numStrata));
}


/*
 * Implement new sample sizes with smooth transitions
 */
proc implementSampleSizeChanges(ref samplingState: SamplingState, 
                              newSizes: [] int) {
    forall (stratum, newSize) in zip(samplingState.strata, newSizes) {
        var currentSize = stratum.sampleSize.read();
        
        // Limit the rate of change to avoid sudden large adjustments
        const maxChange = max(currentSize / 4, // Max 25% change
                            samplingState.Sconfig.minSampleSize);
        
        var sizeChange = newSize - currentSize;
        sizeChange = max(-maxChange, min(maxChange, sizeChange));
        
        var adjustedSize = currentSize + sizeChange;
        
        // Ensure size constraints
        adjustedSize = max(adjustedSize, samplingState.Sconfig.minSampleSize);
        adjustedSize = min(adjustedSize, stratum.size.read());
        
        stratum.sampleSize.write(adjustedSize);
        
        if logLevel == LogLevel.DEBUG {
            writeln("Stratum ", stratum.id, " sample size adjusted: ",
                   currentSize, " -> ", adjustedSize,
                   " (optimal: ", newSize, ")");
        }
    }
}

proc isSamplingComplete(samplingState: borrowed SamplingState): bool {
    var complete = true;
    forall stratum in samplingState.strata with (& reduce complete) {
        complete &= stratum.validSamples.read() >= stratum.sampleSize.read();
    }
    return complete;
}
/*
 * Sample next batch of vertices considering N-K limit
 */
proc sampleNextBatch(samplingState: borrowed SamplingState, n: int, k: int): domain(int, parSafe=true) {
    var batchVertices: domain(int, parSafe=true);
    const batchSize = 100;
    const maxValidVertex = samplingState.Sconfig.effectiveN;  // Using pre-calculated N-K

    if logLevel == LogLevel.DEBUG {
        writeln("Sampling batch with max valid vertex: ", maxValidVertex);
    }
    
    forall stratum in samplingState.strata with(ref batchVertices){
        var targetSize = stratum.sampleSize.read();
        var currentCount = stratum.validSamples.read();
        
        if currentCount >= targetSize then continue;
        
        var batchTarget = min(batchSize, targetSize - currentCount);
        var sampledInBatch: atomic int;
        var localVertices: domain(int, parSafe=true);
        
        // Only sample vertices that are valid for k-size motifs
        forall v in stratum.vertices with (ref localVertices) {
            if v >= maxValidVertex then continue;  // Skip vertices that can't form k-size motifs
            if sampledInBatch.read() >= batchTarget then continue;
            
            var rng = new randomStream(real);
            if rng.next() <= (batchTarget:real / stratum.size.read()) {
                localVertices.add(v);
                sampledInBatch.add(1);
                samplingState.totalSampledVertices.add(1);
            }
        }
        
        batchVertices += localVertices;
    }
    
    return batchVertices;
}
/*
 * Enhanced SampledEnumerate with dynamic adjustment
 */
proc SampledEnumerateWithDynamicAdjustment(n: int, k: int, maxDeg: int,
                                          ref samplingState: SamplingState,
                                          ref globalMotifCount: atomic int,
                                          ref globalClasses: set(uint(64), parSafe=true)) throws {
    
    const maxValidVertex = n - k;
    if maxValidVertex <= 0 {
        throw new Error("Motif size too large for graph size");
    }
    
    const checkInterval = max(100, maxValidVertex / 1000); // Adjusted to use maxValidVertex
    var lastAdjustmentCount = 0;
    var adjustmentCount = 0;
    const maxAdjustments = 5;
    
    // Sample vertices and explore in batches
    while !isSamplingComplete(samplingState) {
        writeln("Current sampling status (valid vertex range: 0..", maxValidVertex, "):");
        for stratum in samplingState.strata {
            writeln("  Stratum ", stratum.id, ":");
            writeln("    Valid samples: ", stratum.validSamples.read());
            writeln("    Target sample size: ", stratum.sampleSize.read());
        }
        var currentTotal = samplingState.totalSampledVertices.read();
        writeln("samplingState.totalSampledVertices inside SampledEnumerateWithDynamicAdjustment ", samplingState.totalSampledVertices.read());

        // Consider adjustment if enough new samples since last adjustment
        if currentTotal - lastAdjustmentCount >= checkInterval && 
           adjustmentCount < maxAdjustments {
            
            var currentProgress = currentTotal:real / maxValidVertex:real;  // Adjusted to use maxValidVertex
            if adjustSampleSizes(samplingState, currentProgress) {
                lastAdjustmentCount = currentTotal;
                adjustmentCount += 1;
                
                if logLevel == LogLevel.DEBUG {
                    writeln("Performed sample size adjustment #", adjustmentCount,
                           " at progress ", (currentProgress * 100):int, "%");
                }
            }
        }
        
        // Sample and explore next batch
        var sampledVertices = sampleNextBatch(samplingState, n, k);
        exploreVertices(sampledVertices, n, k, maxDeg, samplingState, 
                       globalMotifCount, globalClasses);
    }
}
/*
 * Explore vertices and collect motifs, considering N-K limit
 */
proc exploreVertices(sampledVertices: domain(int, parSafe=true),
                    n: int, k: int, maxDeg: int,
                    samplingState: borrowed SamplingState,
                    ref globalMotifCount: atomic int,
                    ref globalClasses: set(uint(64), parSafe=true)) throws{
    
    const maxValidVertex = samplingState.Sconfig.effectiveN;
    
    forall v in sampledVertices with (ref globalClasses, ref globalMotifCount) {
        if v >= maxValidVertex {
            if logLevel == LogLevel.DEBUG {
                writeln("Skipping vertex ", v, " as it exceeds N-K limit");
            }
            continue;
        }
        
        var state = new KavoshState(n, k, maxDeg);
        state.setSubgraph(0, 0, 1);
        state.setSubgraph(0, 1, v);
        state.visited.clear();
        state.visited.add(v);
        
        // Find stratum for scaling
        var stratumId = -1;
        for (id, stratum) in zip(0..#samplingState.strata.size, samplingState.strata) {
            if stratum.vertices.contains(v) {
                stratumId = id;
                break;
            }
        }
        
        if stratumId == -1 {
            halt("Error: Sampled vertex ", v, " not found in any stratum");
        }
        
        // Explore and update statistics
        Explore(state, v, 1, k - 1);
        
        ref stratum = samplingState.strata[stratumId];
        stratum.validSamples.add(1);
        stratum.motifStats.updateStats(state.localmotifClasses.size:uint(64), 
                                     state.localsubgraphCount);
        
        // Scale results based on sampling
        var scaleFactor = calculateScaleFactor(stratum.size.read(), 
                                             stratum.sampleSize.read());
        var scaledCount = (state.localsubgraphCount:real * scaleFactor):int;
        globalMotifCount.add(scaledCount);
        globalClasses += state.localmotifClasses;
    }
}
/*
 * Comprehensive sampling report combining runtime statistics and detailed analysis
 */
proc printComprehensiveSamplingReport(samplingState: borrowed SamplingState, 
                                    globalMotifCount: atomic int,
                                    globalClasses: set(uint(64), parSafe=true),
                                    timeTaken: real) throws{
    writeln("\n============= Sampling-based Motif Census Report =============");
    
    // Configuration Summary
    writeln("\n1. Configuration Parameters:");
    writeln("  - Confidence Level: ", samplingState.Sconfig.confidenceLevel * 100, "%");
    writeln("  - Margin of Error: ±", samplingState.Sconfig.marginOfError * 100, "%");
    writeln("  - Strategy: ", samplingState.Sconfig.strategyType);
    writeln("  - Number of Strata: ", samplingState.Sconfig.numStrata);
    writeln("  - Pilot Fraction: ", samplingState.Sconfig.pilotFraction * 100, "%");
    writeln("  - Effective Vertex Range (N-K): ", samplingState.Sconfig.effectiveN);
    
    // Runtime Statistics
    writeln("\n2. Runtime Statistics:");
    writeln("  - Total Vertices Sampled: ", samplingState.totalSampledVertices.read());
    writeln("  - Execution Time: ", timeTaken:real, " seconds");

    // Per-Stratum Details
    writeln("\n3. Stratum-wise Analysis:");
    for stratum in samplingState.strata {
        writeln("\n  Stratum ", stratum.id, ":");
        
        // Population Statistics
        writeln("    Population Statistics:");
        writeln("    - Total Size: ", stratum.size.read());
        writeln("    - Number of Vertices: ", stratum.vertices.size);
        writeln("    - Valid Samples: ", stratum.validSamples.read());
        writeln("    - Target Sample Size: ", stratum.sampleSize.read());
        
        // Degree Range (if using degree-based stratification)
        if samplingState.Sconfig.strategyType == "degree" {
            writeln("    Degree Range:");
            writeln("    - Lower Bound: ", stratum.lowerBound.read());
            writeln("    - Upper Bound: ", stratum.upperBound.read());
        }
        
        // Motif Statistics
        writeln("    Motif Analysis:");
        writeln("    - Total Motifs Found: ", stratum.motifStats.totalMotifs.read());
        writeln("    - Sampled Vertices: ", stratum.motifStats.sampledVertices.read());
        writeln("    - Unique Patterns: ", stratum.motifStats.getUniquePatternCount());
        writeln("    - Mean Motifs per Vertex: ", stratum.motifStats.getMean():real);
        writeln("    - Standard Error: ", stratum.motifStats.getStandardError():real);
        writeln("    - Variance: ", stratum.motifStats.getVariance():real);
        
        // Pattern Distribution
        writeln("    Pattern Distribution:");
        for pattern in stratum.motifStats.patternCounts.keys() {
            writeln("      Pattern ", pattern, ": ", stratum.motifStats.patternCounts[pattern].read());
        }
        
        // Confidence Intervals
        var (lower, upper) = stratum.motifStats.getConfidenceInterval(samplingState.Sconfig.confidenceLevel);
        writeln("    Statistical Bounds:");
        writeln("    - Confidence Interval: [", lower:real, ", ", upper:real, "]");
        
        // Sampling Rate
        var samplingRate = (stratum.validSamples.read():real / stratum.size.read():real) * 100;
        writeln("    Sampling Rate: ", samplingRate:real, "%");
    }

    // Global Results
    writeln("\n4. Global Results:");
    writeln("  - Total Motifs (Scaled): ", globalMotifCount.read());
    writeln("  - Unique Motif Classes: ", globalClasses.size);
    writeln("  - Motif Class IDs: ", globalClasses);
    
    // Quality Metrics
    writeln("\n5. Quality Assessment:");
    var totalVariance = + reduce [s in samplingState.strata] s.motifStats.getVariance();
    var avgVariance = totalVariance / samplingState.Sconfig.numStrata;
    writeln("  - Average Variance: ", avgVariance:real);
    
    var coverageRate = (samplingState.totalSampledVertices.read():real / 
                       samplingState.Sconfig.effectiveN:real) * 100;
    writeln("  - Overall Vertex Coverage: ", coverageRate:real, "%");
    
    writeln("\n==========================================================");
}
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
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

    var timer:stopwatch;

    writeln("**********************************************************************");
    if useSampling {
        timer.start();


        // Initialize sampling components
        var Sconfig = new SamplingConfig(g1.n_vertices, motifSize);
        var validator = new SamplingValidator(Sconfig.numStrata);
        var adjuster = new DynamicAdjuster(Sconfig.numStrata);
        
        // Create sampling state
        var samplingState = stratifyGraph(n, nodeDegree, Sconfig);
        
        try {
            // Run sampling-based enumeration
            SampledEnumerateWithDynamicAdjustment(n, motifSize, maxDeg,
                                                 samplingState, globalMotifCount,
                                                 globalClasses);
            timer.stop();
            
            // Print detailed sampling report
            printComprehensiveSamplingReport(samplingState, globalMotifCount, 
                                        globalClasses, timer.elapsed());
        } catch e {
            writeln("Sampling failed: ", e.message());
            writeln("Falling back to full enumeration...");
            useSampling = false;
        }
    }
    
    if !useSampling {
    writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
    writeln("Maximum degree: ", maxDeg);

    Enumerate(g1.n_vertices, motifSize, maxDeg );
    // Oliver: Now you can make your src and dst based on Classes that I gathered in 
    // motifClasses and return them to users 
    // we should decide to keep or delete (allmotifs list)
    
    }
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