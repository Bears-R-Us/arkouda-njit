module WellConnectedComponents {
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

  // Arachne modules.
  use WellConnectedComponentsMsg;
  use GraphArray;
  use Utils;
  use ConnectedComponents;
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;
  use Logging;

  // C header and object files.
  require "viecut_helpers/computeMinCut.h",
          "viecut_helpers/computeMinCut.o",
          "viecut_helpers/logger.cpp.o";
  
  extern proc c_computeMinCut(partition_arr: [] int, src: [] int, dst: [] int, n: int, m: int): int;

  /* Modified version of the standard set module intersection method to only return the size of
     the intersection. */
  proc setIntersectionSize(const ref a: set(?t, ?), const ref b: set(t, ?)) {
    // Internal way to force processor atomic instead of network atomic in multilocale mode.
    var size:chpl__processorAtomicType(int) = 0;

    /* Iterate over the smaller set */
    if a.size <= b.size {
      if a.parSafe && b.parSafe {
        forall x in a do if b.contains(x) then size.add(1);
      } else {
        for x in a do if b.contains(x) then size.add(1);
      }
    } else {
      if a.parSafe && b.parSafe {
        forall x in b do if a.contains(x) then size.add(1);
      } else {
        for x in b do if a.contains(x) then size.add(1);
      }
    }
    
    return size.read();
  }

  // Helper methods to return a specified criterion.
  proc log10Criterion(n:int, m:real) { return floor(log10(n:real)); }
  proc log2Criterion(n:int,  m:real) { return floor(log2(n:real)); }
  proc sqrtCriterion(n:int,  m:real) { return floor(sqrt(n:real)/5); }
  proc multCriterion(n:int,  m:real) { return floor(m*n:real); }

  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string, outputType: string,
               connectednessCriterion: string, connectednessCriterionMultValue: real, 
               preFilterMinSize: int, postFilterMinSize: int): int throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG1 = toSymEntry(g1.getComp("NEIGHBORS_SET_SDI"), set(int)).a;
    
    var finalVertices = new list(int, parSafe=true);
    var finalClusters = new list(int, parSafe=true);
    var globalId:atomic int = 0;

    
    var newClusterIdToOriginalClusterId = new map(int, int);
    var criterionFunction = if connectednessCriterion == "log10" then log10Criterion
                            else if connectednessCriterion == "log2" then log2Criterion
                            else if connectednessCriterion == "sqrt" then sqrtCriterion
                            else if connectednessCriterion == "mult" then multCriterion
                            else log10Criterion;
    
          
      writeln("/************* graph info**************/");
      var graphset: set(int, parSafe = true);
      forall i in 0..g1.n_vertices - 1 with (ref graphset){
        graphset.add(i);
      }
      //printGraphState(graphset);
      var totalVolume: int = 0;  // To store the total degree sum of the graph
      var graphMinDegree: int = g1.n_vertices;
      for v in 0..<g1.n_vertices{
        var degree = neighborsSetGraphG1[v].size;
        totalVolume += degree;
        graphMinDegree = if degree < graphMinDegree then degree else graphMinDegree;
      }
      var meanDegreeGraph :real = totalVolume / g1.n_vertices: real;

      writeln("graph totalVolume: ", totalVolume);
      writeln("graph MinDegree: ", graphMinDegree);
      writeln("graph nodes: ", g1.n_vertices);
      writeln("graph edges: ", g1.n_edges);

      writeln("meanDegreeGraph: ", meanDegreeGraph);
      writeln();

      // Module level variables
      const graphSize = g1.n_vertices;
      const clusterMinSize: int = 10;
      const gapThreshold = 0.03;
      const maxRecursionDepth = 20;
      const minRelativeSize = 0.1;

    /*
      Process file that lists clusterID with one vertex on each line to a map where each cluster
      ID is mapped to all of the vertices with that cluster ID. 
    */
    proc readClustersFile(filename: string) throws {
      var clusters = new map(int, set(int));
      var file = open(filename, ioMode.r);
      var reader = file.reader(locking=false);

      for line in reader.lines() {
        var fields = line.split();
        if fields.size >= 2 {
          var originalNode = fields(0): int;
          var clusterID = fields(1): int;
          const (found, idx) = binarySearch(nodeMapGraphG1, originalNode);

          if found {
            var mappedNode = idx;
            if clusters.contains(clusterID) {
              clusters[clusterID].add(mappedNode);
            } else {
              var s = new set(int);
              s.add(mappedNode);
              clusters[clusterID] = s;
            }
          }
          else {
            if logLevel == LogLevel.DEBUG {
              var outMsg = "Vertex not found in the graph: " + originalNode:string;
              wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            }
          }
        }
      }
      reader.close();
      file.close();
      var outMsg = "Number of clusters originally found in file: " + clusters.size:string;
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      
      return clusters;
    }

    /* Returns the edge list of the induced subgraph given a set of vertices. */
    proc getEdgeList(ref vertices: set(int)) throws {
      var srcList = new list(int);
      var dstList = new list(int);

      var v2idx = new map(int, int);
      var idx2v = vertices.toArray();
      sort(idx2v);

      for (v,idx) in zip(idx2v, idx2v.domain) do v2idx[v] = idx;

      // Gather the edges of the subgraph induced by the given vertices.
      for u in vertices {
        const ref neighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];
        for v in neighbors {
          if v2idx.contains(v) {
            srcList.pushBack(v2idx[u]);
            dstList.pushBack(v2idx[v]);
          }
        }
      }      

      // Convert lists to arrays since we need arrays for our edge list processing methods.
      var src = srcList.toArray();
      var dst = dstList.toArray();

      // Sort the redges and remove any multiples if they exist.
      // TODO: Do we actually need to sort and remove multiple edges? If the input graph is simple, 
      //       wouldn't any induced subgraphs also be simple?
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);

      return (uniqueSrc, uniqueDst, idx2v);
    }


    /* Define a custom tuple comparator. */
    record TupleComparator {
      proc compare(a: (int, int), b: (int, int)) {
        if a(0) != b(0) then return a(0)-b(0);
        else return a(1)-b(1);
      }
    }

    /* Function to sort edge lists based on src and dst nodes */
    proc sortEdgeList(ref src: [] int, ref dst: [] int) {
      // Move elements of src and dst to an array of tuples.
      var edges: [0..<src.size] (int, int);
      for i in 0..<src.size do edges[i] = (src[i], dst[i]);

      // Sort the array of tuples.
      var TupleComp: TupleComparator;
      sort(edges, comparator=TupleComp);
      
      // Split sorted edge list into two different arrays.
      var sortedSrc: [0..<src.size] int;
      var sortedDst: [0..<dst.size] int;
      for i in 0..<src.size {
        sortedSrc[i] = edges[i][0];
        sortedDst[i] = edges[i][1];
      }

      return (sortedSrc, sortedDst);
    }
 
    /* Function to remove duplicate edges from sorted edge lists. */
    proc removeMultipleEdges(ref src: [] int, ref dst: [] int) {
      var uniqueSrc = new list(int);
      var uniqueDst = new list(int);

      if src.size == 0 then return (src, dst);

      uniqueSrc.pushBack(src[0]);
      uniqueDst.pushBack(dst[0]);

      for i in 1..<src.size {
        if src[i] != src[i-1] || dst[i] != dst[i-1] {
          uniqueSrc.pushBack(src[i]);
          uniqueDst.pushBack(dst[i]);
        }
      }

      var noDupsSrc = uniqueSrc.toArray();
      var noDupsDst = uniqueDst.toArray();

      return (noDupsSrc, noDupsDst);
    }

    /* Function to calculate the degree of a vertex within a component/cluster/community. */
    proc calculateClusterDegree(ref members: set(int), vertex: int) throws {
      const ref neighbors = neighborsSetGraphG1[vertex];
      return setIntersectionSize(neighbors,members);
    }

    /* Writes a cluster out to a file DURING its well-connectedness check. Contains verbose output
      for debugging purposes. */
    proc writeClustersToFile(ref members:set(int), id:int, currentId:int, d:int, c:int) throws {
      var filename = outputPath + "_" + newClusterIdToOriginalClusterId[id]:string + "_" + id:string 
                   + currentId:string + "_" + members.size:string + "_" + d:string + "_" + c:string 
                   + ".tsv";
      var file = open(filename, ioMode.cw);
      var fileWriter = file.writer(locking=false);
      var mappedArr = nodeMapGraphG1[members.toArray()];

      fileWriter.writeln("# Original Cluster ID:             " + newClusterIdToOriginalClusterId[id]:string);
      fileWriter.writeln("# Connected Components Cluster ID: " + id:string);
      fileWriter.writeln("# Final Cluster ID:                " + currentId:string);
      fileWriter.writeln("# Cluster Depth:                   " + d:string);
      fileWriter.writeln("# Number of Members:               " + members.size:string);
      fileWriter.writeln("# Minimum Cut:                     " + c:string);
      fileWriter.writeln("# Members:                         ");
      for m in mappedArr do fileWriter.writeln(m:string);
      
      try fileWriter.close();
      try file.close();
    }

    /* Writes all clusters out to a file AFTER they are deemed well-connected. */
    proc writeClustersToFile() throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(finalVertices, finalClusters) do writer.writeln(nodeMapGraphG1[v], " ", c);

      writer.close();
      outfile.close();
    }

    /* Writes a cluster out to a file DURING its well-connectedness check. */
    proc writeClustersToFile(ref vertices: set(int), cluster:int) throws {
      var filename = outputPath;
      var outfile = open(filename, ioMode.a);
      var writer = outfile.writer(locking=true);

      for v in vertices do writer.writeln(nodeMapGraphG1[v], " ", cluster);

      writer.close();
      outfile.close();
    }

    /* Given a specific partition, removes vertices with degree one, and returns a new set. */
    proc removeDegreeOne(ref partition:set(int)): set(int) throws{
      if partition.size <= 1 {
        var zeroset = new set(int);
        return zeroset;
      }
      var reducedPartition = partition;
      for v in partition {
        var memberDegree = calculateClusterDegree(partition, v);
        if memberDegree < 2 then reducedPartition.remove(v);
      }
      return reducedPartition;
    }
////////////////////////////////////////////// Metrics ///////////////////////////////////////////////////////////////////
////////////////////////////////////////////// Metrics ///////////////////////////////////////////////////////////////////
////////////////////////////////////////////// Metrics ///////////////////////////////////////////////////////////////////



    /* Enhanced Record definitions for storing metrics */
    record connectivityMetrics {
        // Basic connectivity
        var minDegree: int;
        var maxDegree: int;
        var avgDegree: real;
        var totalInternalEdges: int;
        var edgeConnectivityLowerBound: int;
        
        // Advanced connectivity
        var degreeVariance: real;      // Measure of degree distribution spread
        var degreeSkewness: real;      // Asymmetry of degree distribution
        var assortativity: real;       // Correlation of adjacent vertex degrees
        var effectiveDiameter: real;   // Distance within which 90% of pairs fall
        var avgBetweenness: real;      // Average betweenness centrality
        var maxBetweenness: real;      // Maximum betweenness centrality
    }

    record densityMetrics {
        // Basic density
        var density: real;
        var sparsity: real;
        var internalEdges: int;
        var maxPossibleEdges: int;
        
        // Advanced density
        var triangleCount: int;               // Number of triangles in cluster
        var globalClusteringCoeff: real;      // Ratio of triangles to connected triples
        var avgLocalClusteringCoeff: real;    // Average of local clustering coefficients
        var edgeDensityDistribution: real;    // Distribution of edge density across cluster
        var localDensityVariance: real;       // Variance in local neighborhood densities
        var densityCorrelation: real;         // Correlation of densities of adjacent vertices
    }

    record spectralMetrics {
        // Basic spectral
        var conductance: real;  
        var lambda2Lower: real;
        var lambda2Upper: real;
        var lambda2Estimate: real;
        
        // Advanced spectral
        var normalizedLambda2Lower: real;    // Bounds for normalized Laplacian
        var normalizedLambda2Upper: real;
        var spectralRadius: real;            // Largest eigenvalue
        var energyRadius: real;              // Spectral energy (sum of absolute eigenvalues)
        var spectralVariance: real;          // Variance of eigenvalues

        var spectralGap: real;              // Gap between λ2 and λ3
        var communityStrength: real;        // Derived from gap
        var partitionResistance: real;      // Resistance to splitting
        var mixingTime: int;                // Information spread rate
        var subcommunityLikelihood: real;   // Probability of sub-communities
    }


    /* Enhanced core metrics record with advanced features */
    record coreMetrics {
        // Basic core metrics 
        var coreNumber: int;
        var coreDensity: real;
        var coreSize: int;
        
        var maxCoreSize: int;                // Size of maximum k-core

        // Core-Periphery Structure
        var corePeripheryScore: real;
        var coreStrength: real;         // Measure of core dominance
        var peripherySize: int;         // Size of periphery
        
        // Shell Decomposition
        var shellDecomposition: [0..10] int;  // Distribution of vertices in shells
        var shellDensities: [0..10] real;     // Density of each shell
        var shellConnectivity: [0..10] real;  // Connectivity between shells
        
        // Hierarchical Structure
        var coreHierarchyDepth: int;          // Number of non-empty shells
        var coreDegreeCorrelation: real;      // Correlation between core numbers and degrees
        var hierarchyBalance: real;           // Balance of shell sizes
        
        // Core Stability
        var coreStability: real;              // Resistance to vertex removal
        var corePersistence: [0..10] real;    // Core membership persistence
        var coreOverlap: [0..10] real;        // Overlap between consecutive cores
        
        // Core Quality
        var coreCohesion: real;               // Internal connectivity of core
        var coreSeparation: real;             // Separation from periphery
        var coreCompactness: real;            // Density relative to size
    }

    /* Main record to hold all metrics */
    record clusterMetricsRecord {
        var connectivity: connectivityMetrics;
        var density: densityMetrics;
        var spectral: spectralMetrics;
        var core: coreMetrics;
    }
        /* Basic connectivity metrics */
    proc calculateBasicConnectivity(ref cluster: set(int)) throws {
        var metrics: connectivityMetrics;
        
        // Handle empty or singleton clusters
        if cluster.size <= 1 {
            metrics.minDegree = 0;
            metrics.maxDegree = 0;
            metrics.totalInternalEdges = 0;
            metrics.avgDegree = 0.0;
            metrics.edgeConnectivityLowerBound = 0;
            return metrics;
        }
                // Get basic statistics first
        var basicStats = calculateBasicStats(cluster);
        
        // Set basic metrics from stats
        metrics.minDegree = basicStats.min_degree;
        metrics.maxDegree = basicStats.max_degree;
        metrics.avgDegree = basicStats.avg_degree;
        metrics.totalInternalEdges = basicStats.n_edges;
        
        // Calculate degree variance and skewness in one pass
        var variance_sum: real = 0.0;
        var skewness_sum = 0.0;
        forall v in cluster with (+ reduce variance_sum, + reduce skewness_sum) {
            var diff = basicStats.degrees[v] - metrics.avgDegree;
            var diff_squared = diff * diff;
            variance_sum += diff_squared;
            skewness_sum += diff_squared * diff;
        }
        
        metrics.degreeVariance = variance_sum / cluster.size:real;
        metrics.degreeSkewness = if metrics.degreeVariance > 0 then 
            (skewness_sum / cluster.size) / (sqrt(metrics.degreeVariance) ** 3): real
            else 0.0;
        
        // Calculate Mader's theorem bound
        metrics.edgeConnectivityLowerBound = ((metrics.avgDegree + 2) / 2): int;
        
        return metrics;
    }

    /* Basic statistics calculation - foundation for other metrics */
    proc calculateBasicStats(ref cluster: set(int)) throws {
        const SAMPLE_THRESHOLD = 10000; // To Oliver: Threshold for sampling in large clusters. most of the time it is ok for clstring purposes. 
        // I didn't use it I put it here for Oliver, we can pass it to all functions that need to sampling!!!!!!!!!!
        // Create a record to hold basic statistics
        record BasicStats {
            var n_vertices: int;            // Number of vertices
            var n_edges: int;               // Number of edges
            const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
            var degrees: [clusterDomain] int;     // Degree sequence
            var avg_degree: real;           // Average degree
            var degree_second_moment: real; // Second moment of degree distribution
            var degree_sum: int;            // Sum of degrees
            var max_degree: int;            // Maximum degree
            var min_degree: int;            // Minimum degree
        }
        
        var stats = new BasicStats();
        stats.n_vertices = cluster.size;

        const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
        var tempDegrees: [clusterDomain] int;     // Degree sequence
        // First calculate degrees
        forall v in cluster with(ref tempDegrees) {
            var neighbors = neighborsSetGraphG1[v];
            tempDegrees[v] = (neighbors & cluster).size;
        }
        
        stats.degrees = tempDegrees;
        // Then calculate statistics from degrees
        stats.degree_sum = + reduce stats.degrees;
        stats.max_degree = max reduce stats.degrees;
        stats.min_degree = min reduce stats.degrees;
        
        // Calculate second moment
        var second_moment = 0.0;
        forall degree in stats.degrees with (+ reduce second_moment) {
            second_moment += (degree * degree): real;
        }
        stats.degree_second_moment = second_moment;
        
        // Calculate remaining statistics
        stats.n_edges = stats.degree_sum / 2;
        stats.avg_degree = stats.degree_sum: real / stats.n_vertices: real;
        
        return stats;
    }

    /* Basic and advanced density metrics */
    proc calculateInternalDensity(ref cluster: set(int)) throws {
        var metrics: densityMetrics;
        writeln(" =====================     calculateInternalDensity     =====================================");
        // Handle empty or singleton clusters
        if cluster.size <= 1 {
            metrics.density = 0.0;
            metrics.sparsity = 1.0;
            metrics.internalEdges = 0;
            metrics.maxPossibleEdges = 0;
            return metrics;
        }
        
        // Get basic statistics
        var basicStats = calculateBasicStats(cluster);
        
        // Calculate basic density metrics
        metrics.internalEdges = basicStats.n_edges;
        metrics.maxPossibleEdges = (cluster.size * (cluster.size - 1)) / 2;
        
        if metrics.maxPossibleEdges > 0 {
            metrics.density = metrics.internalEdges: real / metrics.maxPossibleEdges: real;
            metrics.sparsity = 1.0 - metrics.density;
        } else {
            metrics.density = 0.0;
            metrics.sparsity = 1.0;
        }
        
        // Calculate triangle count efficiently
        // metrics.triangleCount = calculateTriangles(cluster);
        writeln("\n metrics: ", metrics);
        return metrics;
    }
/* Basic spectral bounds based on conductance */
proc calculateSpectralBounds(conductance: real) {
    var metrics: spectralMetrics;
    writeln("==================== calculateSpectralBounds ======================");

    // Store conductance
    metrics.conductance = conductance;

    // Basic Cheeger inequality bounds
    metrics.lambda2Lower = (conductance * conductance) / 2;
    metrics.lambda2Upper = 2 * conductance;
    metrics.lambda2Estimate = (metrics.lambda2Lower + metrics.lambda2Upper) / 2;


    
    return metrics;
}

    /* Main analysis function */
    proc analyzeCluster(ref cluster: set(int)) throws {
      var metrics = new clusterMetricsRecord();
        
      // Handle empty or singleton clusters
      if cluster.size <= 1 {
        // metrics = initializeEmptyMetrics();
        printClusterAnalysis(metrics, cluster.size);
        return metrics;
      }
        
      // Basic Metrics
      metrics.connectivity = calculateBasicConnectivity(cluster);
      metrics.density = calculateInternalDensity(cluster);
      
      
      // Calculate conductance and spectral properties
      var conductance = calculateConductance(cluster, totalVolume);
      metrics.spectral = calculateSpectralBounds(conductance);
      
      printClusterAnalysis(metrics, cluster.size);

      return metrics;
    }
    proc printClusterAnalysis(metrics: clusterMetricsRecord, clusterSize: int) throws {
    writeln("\n=================== Cluster Analysis (Size: ", clusterSize, ") ===================");
    
    writeln("\n1. Basic Connectivity Metrics:");
    writeln("   - Minimum Degree: ", metrics.connectivity.minDegree);
    writeln("   - Maximum Degree: ", metrics.connectivity.maxDegree);
    writeln("   - Average Degree: ", metrics.connectivity.avgDegree);
    //writeln("   - Edge Connectivity Lower Bound: ", metrics.connectivity.edgeConnectivityLowerBound);
    writeln("*/*/ (Mader's Theorem and Its Implications ): Cluster has a ", metrics.connectivity.edgeConnectivityLowerBound, "-edge-connected subgraph. in the best(worst) case!");
    writeln("   Advanced Connectivity:");
    writeln("   - Degree Variance: ", metrics.connectivity.degreeVariance);
    writeln("   - Degree Skewness: ", metrics.connectivity.degreeSkewness);
    writeln("   - Assortativity: ", metrics.connectivity.assortativity);
    // writeln("   - Effective Diameter: ", metrics.connectivity.effectiveDiameter);
    // writeln("   - Average Betweenness: ", metrics.connectivity.avgBetweenness);
    // writeln("   - Maximum Betweenness: ", metrics.connectivity.maxBetweenness);
    
    writeln("\n2. Density Metrics:");
    writeln("   Basic Density:");
    writeln("   - Internal Density: ", metrics.density.density);
    writeln("   - Sparsity: ", metrics.density.sparsity);
    writeln("   - Internal Edges: ", metrics.density.internalEdges);
    writeln("   - Maximum Possible Edges: ", metrics.density.maxPossibleEdges);
    writeln("   Advanced Density:");
    writeln("   - Triangle Count: ", metrics.density.triangleCount);
    writeln("   - Global Clustering Coefficient: ", metrics.density.globalClusteringCoeff);
    writeln("   - Average Local Clustering: ", metrics.density.avgLocalClusteringCoeff);
    writeln("   - Edge Density Distribution: ", metrics.density.edgeDensityDistribution);
    writeln("   - Local Density Variance: ", metrics.density.localDensityVariance);
    writeln("   - Density Correlation: ", metrics.density.densityCorrelation);
    
    writeln("\n3. Conductance Metrics:");
    writeln("   - Conductance: ", metrics.spectral.conductance);
    // writeln("   - External Edges: ", metrics.conductanceData[1]);
    
    writeln("\n4. Spectral Properties:");
    writeln("   Basic Spectral:");
    writeln("   - λ2 lower bound: ", metrics.spectral.lambda2Lower);
    writeln("   - λ2 upper bound: ", metrics.spectral.lambda2Upper);
    writeln("   - λ2 estimate: ", metrics.spectral.lambda2Estimate);
    writeln("   Advanced Spectral:");
    writeln("   - Normalized λ2 bounds: [", metrics.spectral.normalizedLambda2Lower, 
            ", ", metrics.spectral.normalizedLambda2Upper, "]");
    writeln("   - Spectral Gap: ", metrics.spectral.spectralGap);
    writeln("   - Community Strength: ", metrics.spectral.communityStrength);
    writeln("   - Partition Resistance: ", metrics.spectral.partitionResistance);
    writeln("   - Mixing Time: ", metrics.spectral.mixingTime);
    writeln("   - Sub-community Likelihood: ", metrics.spectral.subcommunityLikelihood);
    writeln("   - Spectral Radius: ", metrics.spectral.spectralRadius);
    writeln("   - Energy Radius: ", metrics.spectral.energyRadius);
    writeln("   - Spectral Variance: ", metrics.spectral.spectralVariance);
    
    writeln("\n5. Core Structure:");
    writeln("   Basic Core:");
    // writeln("   - k-core number: ", metrics.core.coreNumber);
    // writeln("   - Core density: ", metrics.core.coreDensity);
    // writeln("   - Core size: ", metrics.core.coreSize);
    // writeln("   Advanced Core:");
    // writeln("   - Core-Periphery Score: ", metrics.core.corePeripheryScore);
    // writeln("   - Max Core Size: ", metrics.core.maxCoreSize);
    // writeln("   - Core-Degree Correlation: ", metrics.core.coreDegreeCorrelation);
    // writeln("   - Core Hierarchy Depth: ", metrics.core.coreHierarchyDepth);
    
    writeln("\n6. Flow and Boundary Properties:");
    writeln("   Basic Flow:");
    // writeln("   - Edge boundary size: ", metrics.flow.edgeBoundarySize);
    // writeln("   - Normalized boundary: ", metrics.flow.normalizedBoundarySize);
    // writeln("   - Minimum cut estimate: ", metrics.flow.minCutEstimate);
    // writeln("   Advanced Flow:");
    // writeln("   - Edge Expansion: ", metrics.flow.edgeExpansion);
    // writeln("   - Vertex Expansion: ", metrics.flow.vertexExpansion);
    // writeln("   - Bottleneck Score: ", metrics.flow.bottleneckScore);
    // writeln("   - Flow Centrality: ", metrics.flow.flowCentrality);
    // writeln("   - Max Flow-Min Cut: ", metrics.flow.maxFlowMinCut);
    
    // writeln("\n7. Robustness Properties:");
    // writeln("   Basic Robustness:");
    // writeln("   - Estimated diameter: ", metrics.robustness.estimatedDiameter);
    // writeln("   - Average path length: ", metrics.robustness.avgPathLength);
    // writeln("   - Robustness score: ", metrics.robustness.robustnessScore);
    // writeln("   Advanced Robustness:");
    // writeln("   - Local Efficiency: ", metrics.robustness.localEfficiency);
    // writeln("   - Global Efficiency: ", metrics.robustness.globalEfficiency);
    // writeln("   - Vulnerability Score: ", metrics.robustness.vulnerabilityScore);
    // writeln("   - Edge Vulnerability: ", metrics.robustness.edgeVulnerability);
    // writeln("   - Redundancy: ", metrics.robustness.redundancy);
    // writeln("   - Percolation Threshold: ", metrics.robustness.percolationThreshold);

    writeln("\nComprehensive Quality Assessment:");
    // 1. Connectivity Assessment
    writeln("\n1. Connectivity Quality:");
    if metrics.connectivity.minDegree == 0 {
        writeln("   ! Critical: Cluster contains isolated vertices");
    } else if metrics.connectivity.assortativity > 0.3 {
        writeln("   + Strong degree correlation (well-mixed connectivity)");
    }
    if metrics.connectivity.degreeVariance > metrics.connectivity.avgDegree * 2 {
        writeln("   ! High degree heterogeneity detected");
    }

    // 2. Density Assessment
    writeln("\n2. Density Quality:");
    if metrics.density.density > 0.7 {
        writeln("   + Excellent density (>70% of possible edges)");
    } else if metrics.density.density > 0.5 {
        writeln("   + Good density (>50% of possible edges)");
    } else if metrics.density.density < 0.1 {
        writeln("   ! Very sparse structure (<10% of possible edges)");
    }
    if metrics.density.globalClusteringCoeff > 0.6 {
        writeln("   + Strong local clustering");
    }

    // 3. Structural Assessment
    writeln("\n3. Structural Quality:");
    if  metrics.spectral.conductance < 0.1 {
        writeln("   + Excellent cluster separation");
    } else if  metrics.spectral.conductance > 0.7 {
        writeln("   ! Poor cluster separation");
    }
    // if metrics.core.coreNumber == 0 {
    //     writeln("   ! Critical: Disconnected structure");
    // } else if metrics.core.corePeripheryScore > 0.8 {
    //     writeln("   + Strong core-periphery structure");
    // }

    // 4. Spectral Assessment
    writeln("\n4. Spectral Quality:");
    if metrics.spectral.lambda2Estimate < 0.01 {
        writeln("   ! Critical: Very weak connectivity");
    } else if metrics.spectral.lambda2Estimate >= 1.0 {
        writeln("   + Strong algebraic connectivity");
    }
// Add detailed spectral analysis
writeln("\n   Spectral Structure Analysis:");
// Community structure assessment
if metrics.spectral.spectralGap > 0.5 {
    writeln("   + Very strong community structure (gap > 0.5)");
} else if metrics.spectral.spectralGap > 0.1 {
    writeln("   + Moderate community structure (gap > 0.1)");
} else {
    writeln("   ! Weak community structure, possible sub-communities");
}

// Partition resistance assessment
if metrics.spectral.partitionResistance > 0.8 {
    writeln("   + High resistance to partitioning");
} else if metrics.spectral.partitionResistance < 0.2 {
    writeln("   ! Low resistance, easily partitionable");
}

// Information flow assessment
if metrics.spectral.mixingTime < log2(clusterSize: real) {
    writeln("   + Fast information spread (efficient mixing)");
} else if metrics.spectral.mixingTime > 2 * log2(clusterSize: real) {
    writeln("   ! Slow information spread (poor mixing)");
}

// Sub-community assessment
if metrics.spectral.subcommunityLikelihood > 0.7 {
    writeln("   ! High likelihood of sub-communities");
} else if metrics.spectral.subcommunityLikelihood < 0.3 {
    writeln("   + Unified community structure");
}

// Community strength assessment
writeln("\n   Community Cohesion Analysis:");
// writeln("   - Strength Score: ", (metrics.spectral.communityStrength * 100.0):int / 100.0, 
//         " (", interpretCommunityStrength(metrics.spectral.communityStrength), ")");
// writeln("   - Internal Communication Speed: ", 
//         interpretMixingTime(metrics.spectral.mixingTime, clusterSize));
// writeln("   - Structural Stability: ", 
//         interpretPartitionResistance(metrics.spectral.partitionResistance));

    // 5. Flow Assessment
    writeln("\n5. Flow Quality:");
    // if metrics.flow.bottleneckScore < 0.1 {
    //     writeln("   ! Significant bottleneck detected");
    // }
    // if metrics.flow.edgeExpansion > 0.5 {
    //     writeln("   + Good expansion properties");
    // }

    // 6. Robustness Assessment
    writeln("\n6. Robustness Quality:");
    // if metrics.robustness.vulnerabilityScore > 0.7 {
    //     writeln("   ! High vulnerability to node removal");
    // }
    // if metrics.robustness.localEfficiency > 0.8 {
    //     writeln("   + Excellent local efficiency");
    // }

    // Overall Quality Score
    writeln("\nOverall Cluster Quality Score:");
    var qualityIssues = 0;
    // Connectivity Issues
    if metrics.connectivity.minDegree == 0 || metrics.connectivity.avgDegree < 2 then qualityIssues += 1;
    // Density Issues
    if metrics.density.density < 0.3 then qualityIssues += 1;
    // Structural Issues
    if metrics.spectral.conductance > 0.5 || metrics.core.coreNumber < 2 then qualityIssues += 1;
    // Spectral Issues
    if metrics.spectral.lambda2Estimate < 0.1 then qualityIssues += 1;
    if (metrics.spectral.communityStrength < 0.3 || 
      metrics.spectral.partitionResistance < 0.2 || 
      metrics.spectral.subcommunityLikelihood > 0.8) {
      qualityIssues += 1;
    }
    // // Flow Issues
    // if metrics.flow.bottleneckScore < 0.1 then qualityIssues += 1;
    // // Robustness Issues
    // if metrics.robustness.vulnerabilityScore > 0.7 then qualityIssues += 1;

    if qualityIssues == 0 {
        writeln("✓ Excellent: High-quality cluster with strong connectivity and robustness");
    } else if qualityIssues == 1 {
        writeln("○ Good: Well-formed cluster with minor issues");
    } else if qualityIssues == 2 {
        writeln("△ Fair: Cluster has some structural weaknesses");
    } else {
        writeln("! Poor: Cluster has significant structural issues");
    }
    
    writeln("\n================================================================\n");
}
/* Helper to create and print graph state */
proc printClusterState(vertices: set(int)) throws{
    writeln("\nCurrent cluster state:");
    //writeln("Vertices: ", vertices.size, " ", vertices);
    writeln("Vertices: ", vertices.size);
    // for v in vertices {
    //     writeln("Vertex ", v, " connects to: ", setToString(neighborsSetGraphG1[v] & vertices));
    // }
}
proc printGraphState(vertices: set(int)) throws{
    writeln("\nCurrent graph state:");
    writeln("Vertices: ", vertices.size, " ", vertices);
    for v in vertices {
        writeln("Vertex ", v, " connects to: ", setToString(neighborsSetGraphG1[v]));
    }
}
/* For sets of integers */
proc setToString(s: set(int)): string {
   var result = "{";
   var first = true;
   for x in s {
       if !first then result += ", ";
       result += x:string;
       first = false;
   }
   result += "}";
   return result;
}


    /* Function to calculate the conductance of a cluster */
    proc calculateConductance(ref cluster: set(int), const totalVolume: int ) throws {
      var cutSizePrevios: int = totalVolume;
      var SumOutEdges: int = 0;
      var volumeCluster: int = 0;
      var volumeComplement: int = 0;
      var minDegreeCluster: int = g1.n_edges;  // 
      var maxCutSizePrevios = 0;       // Initialize with a low value for max comparison

      // Iterate through all vertices to calculate volumes, cutSize, and total graph volume
      for v in cluster {
        var neighbors = neighborsSetGraphG1[v];
        volumeCluster += neighbors.size;
        var outEdge = neighbors - cluster;
        //writeln("outEdge: ", outEdge);
        SumOutEdges += outEdge.size;

        // Update minimum outEdge size
        cutSizePrevios = if outEdge.size < cutSizePrevios &&  outEdge.size > 0 then outEdge.size else cutSizePrevios;

        // Update maximum outEdge size
        maxCutSizePrevios = if outEdge.size > maxCutSizePrevios then outEdge.size else maxCutSizePrevios;

        // Update minimum degree in cluster
        minDegreeCluster = if neighbors.size < minDegreeCluster then neighbors.size else minDegreeCluster;
      }

      volumeComplement = totalVolume - volumeCluster;

      //writeln("*****************calculateConductance called***********************");


      // Calculate mean degrees for cluster and overall graph
      var meanDegreeCluster = volumeCluster / cluster.size: real;


      // Compute conductance
      var denom = min(volumeCluster, volumeComplement);
      var conductance: real;

      if denom > 0 then
        conductance = SumOutEdges / denom: real;
      else
        conductance = 0.0;
      var output: [0..2] real;
      output[0] = conductance;
      output[1] = SumOutEdges;
      // output[2] = minDegreeCluster;
      // output[3] = meanDegreeCluster;
      //output[0] = conductance;
      // writeln("conductance: ", conductance);
      if conductance == 0 then writeln("This cluster seems to be far from other clusters (outlier cluster)!!"); 

      // writeln("volumeCluster: ", volumeCluster);
      // writeln("volumeComplement: ", volumeComplement);
      // Output intermediate calculations for verification
      // writeln(cutSizePrevios, " <= Est. of Previos cutsize ");
      // writeln("Cluster SumOutEdges : ", SumOutEdges);
      // writeln("Cluster Mean degree: ",meanDegreeCluster );
      // writeln("Based on Mader's theorem for sure we have a ",((meanDegreeCluster+2)/2):int,"-edge-connected subgraph. (a lower bound)" );
      // writeln("Based on Iequlaity. MinCut <= ", minDegreeCluster);
      // // Calculate lower and upper bounds of lambda2
      // var lambda2_lower = (conductance * conductance) / 2;
      // var lambda2_upper = 2 * conductance;
      // writeln("Based on Cheeger's Inequalit: ",lambda2_lower," <= λ2 <= ", lambda2_upper);
      // writeln("λ2 Midpoint Approximation: ",(lambda2_lower + lambda2_upper)/2 );
      // writeln("My metric: ",2 * conductance/(lambda2_lower + lambda2_upper) );
      //alpha*lambda2_lower + (1-alpha)* lambda2_upper

 
      // writeln("//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*");
      // writeln("λ2 == 0    --> Cluster is disconnected!");
      // writeln("λ2 near 0  --> Cluster is weakly connected, and for sure there is 2 subcluster in it.");
      // writeln("0 << λ2 < 1 --> Cluster is reasonably well-connected structure, with some potential for partitioning.");
      // writeln("λ2 >= 1    --> Cluster has strong connectivity and robustness");
      // writeln("//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*//*\n");

      return conductance;
    }// end of calculateConductance
/* Enhanced conductance calculation with additional metrics */
proc calculateConductanceWCC(ref cluster: set(int), const totalVolume: int) throws {
    var minDegree = g1.n_edges;  // Initialize to max possible
    var conductance: real = 0.0;
    // Calculate volumes and edge counts
    var volumeCluster: int = 0;
    var outEdges: int = 0;
    for v in cluster {
        var neighbors = neighborsSetGraphG1[v];
        volumeCluster += neighbors.size;
        var outGoingEdges = neighbors - cluster;
        outEdges += outGoingEdges.size;
    }

    var volumeComplement = totalVolume - volumeCluster;
    // Calculate conductance
    var denom = min(volumeCluster, volumeComplement);
    if denom > 0 {
        conductance = outEdges / denom: real;
    } else {
        conductance = 0.0;
    }

    // Calculate spectral bounds using Cheeger's inequality
    var lambda2Lower = (conductance * conductance) / 2;
    var lambda2Upper = 2 * conductance;
    var lambda2Estimate = (lambda2Lower + lambda2Upper) / 2;

    /* Debug output for cluster analysis */
    //if logLevel == LogLevel.DEBUG {
        writeln("\nGraph Volume:", totalVolume);
        writeln("Cluster Analysis:");
        writeln("Size: ", cluster.size);
        writeln("Cluster Volume: ", volumeCluster);
        writeln("Cluster cutedges: ", outEdges);
        writeln("Conductance: ", conductance);
        writeln("Spectral Bounds (λ2):");
        writeln("  Lower: ", lambda2Lower);
        writeln("  Upper: ", lambda2Upper);
        writeln("  Estimate: ", lambda2Estimate);
    //}

    return conductance;
}


    /* Calculate gap based on metrics */
proc calculateGap(in cluster: set(int), conductance: real, const totalVolume: int): real throws{
    writeln("================   calculateGap   =====================\n");
    var gap: real = 0.0;
    if conductance == 0 {
      gap = 0.0;
      writeln("  Final Gap: ", gap);
      // writeln("=====================================\n");
      return gap;
    }
    
    // var internalConnectivity = metrics.lambda2Estimate;
    // var clusterConn = (internalConnectivity * internalConnectivity) / 
    //                   log(max(2, metrics.volumeCluster):real);  // avoid log(1)
    var phiC = conductance;
    var conn = calculateConn(cluster, totalVolume);

    gap = if phiC > 0.0 then conn/phiC:real else 0.0;
    

    writeln("  Final Gap: ", gap);
    // writeln("=====================================\n");

    return gap;
}

proc calculateConn(in cluster: set(int), totalVolume: int) throws{
   // Calculate |E(A)| - internal edges
   var internalEdges = 0;
   for v in cluster {
       internalEdges += calculateClusterDegree(cluster, v);
   }
   internalEdges /= 2;  // Each edge counted twice

   // Calculate vol(A)
   var clusterVolume = 0;
   for v in cluster {
       clusterVolume += neighborsSetGraphG1[v].size;
   }

   // Calculate Conn(A) = |E(A)|/(|A|*log(vol(A)))
   var conn = internalEdges:real / (cluster.size * log10(clusterVolume):real);

  //  writeln("Cluster size: ", cluster.size);
   writeln("Internal edges: ", internalEdges);  
   writeln("Cluster volume: ", clusterVolume);
   writeln("Conn value: ", conn);

   return conn;
}
proc calculateClusterVolume(ref cluster: set(int)) throws{
     var clusterVolume = 0;
   for v in cluster {
       clusterVolume += neighborsSetGraphG1[v].size;
   }
  return clusterVolume;
}


////////////////////////////////////////////// End of Metrics ///////////////////////////////////////////////////////////////////
proc wccRecursiveChecker(ref vertices: set(int), id: int, depth: int, originalSize: int = -1) throws {
    var actualOriginalSize = if originalSize == -1 then vertices.size else originalSize;
    var splitFlag: bool = false;
    writeln("\n============== WCC Recursive Checker (Depth: ", depth, ") ==============");
    // writeln("Current cluster info:");
    // writeln("  Size: ", vertices.size);
    // writeln("  Original size: ", actualOriginalSize);
    printClusterState(vertices);

    // Check stopping conditions
    if vertices.size <= clusterMinSize { 
        writeln("Warning: Size < clusterMinSize (", clusterMinSize, ")");
        //return;
    }
    if depth > min(maxRecursionDepth, ceil(log10(actualOriginalSize:real)):int) {
        writeln("STOP: Exceeded max depth");
        return;
    }
    // if vertices.size:real < g1.n_vertices:real * minRelativeSize {
    //     writeln("STOP: Size too small relative to original. we reached 0.1 size of graph.");
    //     return;
    // }

    // 1. Volume condition
    var clusterVolume = calculateClusterVolume(vertices);
    if clusterVolume > totalVolume/2 {
      writeln("HINT: Volume Condition failed: vol(cluster) > 1/2 vol(Graph)");
      writeln("Cluster is a good candidate for splitting.");
      splitFlag = true ;
    }

    // 2. Gap condition
    writeln("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$ We are here for Gap");
    var conductance = calculateConductanceWCC(vertices, totalVolume);
    var gap = calculateGap(vertices, conductance, totalVolume);
    
        var (src, dst, mapper) = getEdgeList(vertices);
        if src.size < 1 {
            writeln("WARNING: Empty edge list - cannot split further");
            // return;
        }
        else{
        var n = mapper.size;
        var partitionArr: [{0..<n}] int;
        var cut = c_computeMinCut(partitionArr, src, dst, n, src.size);
        var cluster1 = new set(int);
        var cluster2 = new set(int);
        for (v,p) in zip(partitionArr.domain, partitionArr) {
            if p == 1 then cluster1.add(mapper[v]);
            else cluster2.add(mapper[v]);
        }
        if gap == 90.2858 || gap == 29.8999{
          writeln("partitionArr = ", partitionArr);
        }
        writeln("Split result:");
        writeln("  Cluster 1 size: ", cluster1.size);
        writeln("  Cluster 2 size: ", cluster2.size);
        writeln("  Cut size: ", cut);
        }
/*
    // Use theoretical approach for decision making
    if isWellConnectedTheo {
        writeln("\n>>> Cluster ACCEPTED as well-connected (theoretical) <<<");
        wccMetrics.passedGapThreshold.add(1);
        var currentId = globalId.fetchAdd(1);
        
        // Output handling
        if outputType == "debug" {
            writeClustersToFile(vertices, id, currentId, depth, metrics.conductance:int);
            writeln("Found well-connected cluster: ", currentId);
            writeln("  Size: ", vertices.size);
            writeln("  Theoretical Gap: ", theoreticalGap);
            writeln("  Conductance: ", metrics.conductance);
        } else if outputType == "during" {
            writeClustersToFile(vertices, currentId);
        }
        
        // Add to final results
        for v in vertices {
            finalVertices.pushBack(v);
            finalClusters.pushBack(currentId);
        }
        
    } else {
        writeln("\n>>> Cluster needs splitting (theoretical) <<<");
        // Split cluster using VieCut
        var (src, dst, mapper) = getEdgeList(vertices);
        if src.size < 1 {
            writeln("WARNING: Empty edge list - cannot split further");
            return;
        }

        writeln("Splitting cluster using VieCut:");
        writeln("  Number of vertices: ", mapper.size);
        writeln("  Number of edges: ", src.size/2);

        var n = mapper.size;
        var partitionArr: [{0..<n}] int;
        var cut = c_computeMinCut(partitionArr, src, dst, n, src.size);
        
        // Create two new clusters
        var cluster1 = new set(int);
        var cluster2 = new set(int);
        for (v,p) in zip(partitionArr.domain, partitionArr) {
            if p == 1 then cluster1.add(mapper[v]);
            else cluster2.add(mapper[v]);
        }
        
        writeln("Split result:");
        writeln("  Cluster 1 size: ", cluster1.size);
        writeln("  Cluster 2 size: ", cluster2.size);
        writeln("  Cut size: ", cut);
        
        // Record split sizes
        wccMetrics.recordSplit(cluster1.size);
        wccMetrics.recordSplit(cluster2.size);
        
        // Recursively process new clusters if they're large enough
        if cluster1.size > postFilterMinSize {
            writeln("\nProcessing Cluster 1:");
            var inPartition = cluster1;
            writeln("  Cluster 1 has: ", inPartition.size, " vertices");
            wccRecursiveChecker(inPartition, id, depth+1, actualOriginalSize);
        } else {
            writeln("Cluster 1 too small - discarding");
        }
        
        if cluster2.size > postFilterMinSize {
            writeln("\nProcessing Cluster 2:");
            var outPartition = cluster2;
            writeln("  After degree-one removal: ", outPartition.size, " vertices");
            wccRecursiveChecker(outPartition, id, depth+1, actualOriginalSize);
        } else {
            writeln("Cluster 2 too small - discarding");
        }
    }*/
    writeln("================================================================\n");
}
     /* Main executing function for well-connected components. */
    proc wcc(g1: SegGraph): int throws {
      var outMsg = "Graph loaded with " + g1.n_vertices:string + " vertices and " 
                 + g1.n_edges:string + " edges.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      var originalClusters = readClustersFile(inputcluster_filePath);
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),
                     "Reading clusters file finished.");

      var newClusterIds: chpl__processorAtomicType(int) = 0;
      var newClusters = new map(int, set(int));
      
      // NOTE: Sequential for now since connected components is highly parallel. We need to discuss
      //       the tradeoff if it is more important to run connected components on the original
      //       clusters in parallel or run connected components in parallel.
      //
      // NOTE: This is probably noy even needed here. We could add a pre-filtering step to run this
      //       during graph construction or as a totally separate process instead of here.
      for key in originalClusters.keysToArray() {
        var (src, dst, mapper) = getEdgeList(originalClusters[key]);
        if src.size > 0 { // If no edges were generated, then do not process this component.
          // Call connected components and decide if multiple connected components exist or not.
          var components = connectedComponents(src, dst, mapper.size);
          var multipleComponents:bool = false;
          for c in components do if c != 0 { multipleComponents = true; break; }
          
          // Add each vertex in each connected component to its own cluster, or just add the whole
          // cluster if it is composed of only one connected component.
          if multipleComponents {
            var tempMap = new map(int, set(int));
            for (c,v) in zip(components,components.domain) { // NOTE: Could be parallel.
              if tempMap.contains(c) then tempMap[c].add(mapper[v]);
              else {
                var s = new set(int);
                s.add(mapper[v]);
                tempMap[c] = s;
              }
            }
            for c in tempMap.keys() { // NOTE: Could be parallel.
              var newId = newClusterIds.fetchAdd(1);
              if tempMap[c].size > preFilterMinSize {
                newClusters[newId] = tempMap[c];
                newClusterIdToOriginalClusterId[newId] = key;
              }
            }
            if logLevel == LogLevel.DEBUG {
              var outMsg = "Original cluster " + key:string + " was split up into " 
                        + tempMap.size:string + " clusters.";
              wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
            }
          } else {
            if originalClusters[key].size > preFilterMinSize {
              var newId = newClusterIds.fetchAdd(1);
              newClusters[newId] = originalClusters[key];
              newClusterIdToOriginalClusterId[newId] = key;
            }
          }
        }
      }
      outMsg = "Splitting up clusters yielded " + newClusters.size:string + " new clusters.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

      // forall key in newClusters.keysToArray() with (ref newClusters) {
      for key in newClusters.keysToArray() {
        ref clusterToAdd = newClusters[key];
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Processing cluster " + key:string + " which is a subcluster of " 
                    + newClusterIdToOriginalClusterId[key]:string + ".";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        writeln(" Graph size = ", g1.n_vertices);
        wccRecursiveChecker(clusterToAdd, key, 0);
      }
      if outputType == "post" then writeClustersToFile();
      
      outMsg = "WCC found " + globalId.read():string + " clusters to be well-connected.";
      wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
      

      return globalId.read();
    } // end of wcc
    
    var numClusters = wcc(g1);
    return numClusters;
  } // end of runWCC
} // end of WellConnectedComponents module