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
    

    proc calculateGraphTotalVolume(): int throws {
      var totalVolume: int = 0;  // To store the total degree sum of the graph
      var tempdegree:[0..<g1.n_vertices] int;
      forall v in 0..<g1.n_vertices{
        tempdegree[v] = neighborsSetGraphG1[v].size;
      }
      totalVolume = + reduce tempdegree;
      return totalVolume;
    }
    record graphRecord {
      var totalVolume: int;
    }
    var graphGlobalRecord : graphRecord;
    graphGlobalRecord.totalVolume = calculateGraphTotalVolume();
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
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////   Metrics //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////

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


/* Path and transitivity metrics */
record pathMetrics {
    var localGlobalRatio: real;          // local/global transitivity ratio
    var cohesionScore: real;             // measure of cluster cohesion
    var pathDistribution: [0..#10] int;  // distribution of path lengths
}

/* Diameter-based metrics */
record eccentricityMetrics {
    var radius: int;                     // minimum eccentricity
    var centerVertices: list(int);       // vertices with minimum eccentricity
    var peripheralVertices: list(int);   // vertices with maximum eccentricity
    var avgEccentricity: real;           // average eccentricity
}
/* Record for diameter calculation results */
record diameterMetrics {
    var exactDiameter: bool;          // Whether result is exact
    var lowerBound: int;             // Lower bound on diameter
    var upperBound: int;             // Upper bound on diameter
    var estimatedDiameter: int;     // Best estimate
}
/* Record for transitivity-based metrics */
record transitivityMetrics {
    var wedgeCount: int;              // Number of two-edge paths
    var triangleToWedgeRatio: real;   // Global clustering coefficient
    var globalTransitivity: real;     // Alternative measure of global clustering
}
/* Enhanced Record definitions for storing metrics */
record connectivityMetrics {
    // Basic connectivity
    var n_vertices: int;
    var minDegree: int;
    var maxDegree: int;
    var avgDegree: real;
    var totalInternalEdges: int;
    var edgeConnectivityLowerBound: int;

    // Advanced connectivity
    var degreeSecondMoment: real;  // Second moment of degree distribution
    var clusterVolume: int;        // Total volume of cluster
    var clusterCutEdges: int;

    var degreeVariance: real;      // Measure of degree distribution spread
    var degreeSkewness: real;      // Asymmetry of degree distribution
    var assortativity: real;       // Correlation of adjacent vertex degrees
    var effectiveDiameter: real;   // Distance within which 90% of pairs fall
    var avgBetweenness: real;      // Average betweenness centrality
    var maxBetweenness: real;      // Maximum betweenness centrality

    var triangleCentrality = new list(real);  // List of triangle centralities

    var diameter: int;              // Estimated diameter
    var diameterLowerBound: int;     // Lower bound
    var diameterUpperBound: int;     // Upper bound
    var exactDiameter: bool;         // Whether diameter is exact

    var bridgeCount: int;
    var bridges: list((int,int), parSafe=true);
    
    var ViecutMincut: int;
    var ViecutInPartiotionSize: int;
    var ViecutOutPartitionSize: int;

}

record densityMetrics {
    // Basic density
    var density: real;
    var sparsity: real;
    var maxPossibleEdges: int;
    
    // Clustering metrics
    var triangleCount: int;               // Number of triangles in cluster
    var globalClusteringCoeff: real;      // Ratio of triangles to connected triples
    var avgLocalClusteringCoeff: real;    // Average of local clustering coefficients
    
    var triangleDensity: real;           // triangles/possible triangles
    var participationRate: real;         // % of vertices in triangles
    var maxLocalTriangles: int;          // max triangles for any vertex
    var avgTrianglesPerVertex: real;     // average triangles per vertex

    var edgeDensityDistribution: real = 0.0;  // Not implemented
    var localDensityVariance: real = 0.0;     // Not implemented
    var densityCorrelation: real = 0.0;       // Not implemented
}
record spectralMetrics {
    // Basic spectral
    var lambda2Lower: real;
    var lambda2Upper: real;
    var lambda2Estimate: real;
    var conductance: real;
}

/* Enhanced Record definitions for storing metrics */
record clusterMetricsRecord {
    var key: int;
    var connectivity: connectivityMetrics;
    var density: densityMetrics;
    var spectral: spectralMetrics;
    var transitivity: transitivityMetrics;
    
    var paths: pathMetrics;
    var eccentricity: eccentricityMetrics;
    
    // Add statistical distributions
    var degreeDistribution: distributionStats;
    var triangleDistribution: distributionStats;
    var pathDistribution: distributionStats;
    var core: coreMetrics;
}
/* Record for statistical analysis of distributions */
record distributionStats {
    var mean: real;
    var median: real;
    var standardDev: real;
    var skewness: real;
    var kurtosis: real;
    var percentiles: [0..100] real;  // Store all percentiles
}

/* Triangle Centrality record for storing metrics */
record triangleCentralityMetrics {
    var triangleCentralities = new list(real);  // List to store centrality values
    var totalTriangles: int;                    // Total number of triangles in the cluster
}


/* Main analysis function for cluster metrics */
proc analyzeCluster(ref cluster: set(int), clusterId: int, ref runConfig: MetricsConfig) throws {
   // Validate configuration first
    runConfig.validate();
    writeln("runConfig: ", runConfig);
    var metrics = new clusterMetricsRecord();
    
    if logLevel == LogLevel.DEBUG {
        writeln("\n========== Starting Cluster Analysis ==========");
        writeln("Cluster size: ", cluster.size);
    }
    
    // Handle empty or singleton clusters
    if cluster.size <= 1 {
        if logLevel == LogLevel.DEBUG {
            writeln("Empty or singleton cluster detected. Initializing empty metrics.");
        }
        metrics = initializeEmptyMetrics();
        printClusterAnalysis(metrics, cluster.size);
        return metrics;
    }

    try {
            // Basic connectivity metrics
            if runConfig.computeBasicConnectivity {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Basic Connectivity Metrics -----");
                }
                metrics.connectivity = calculateBasicConnectivity(cluster);
            }

            // Advanced connectivity metrics(including assortativity)
            if runConfig.computeTriangles {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Advanced Connectivity Metrics -----");
                }
                var advancedMetrics = calculateAdvancedConnectivity(cluster);
                metrics.connectivity.assortativity = advancedMetrics.assortativity;
                metrics.connectivity.effectiveDiameter = advancedMetrics.effectiveDiameter;
                metrics.connectivity.avgBetweenness = advancedMetrics.avgBetweenness;
                metrics.connectivity.maxBetweenness = advancedMetrics.maxBetweenness;

                var cutMetrics = calculateViecutMincut(cluster, advancedMetrics);
                metrics.connectivity.ViecutMincut = cutMetrics.ViecutMincut;
                metrics.connectivity.ViecutInPartiotionSize = cutMetrics.ViecutInPartiotionSize;
                metrics.connectivity.ViecutOutPartitionSize = cutMetrics.ViecutOutPartitionSize;
            }

            // Density metrics
            if runConfig.computeDensity {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Density Metrics -----");
                }
                var n = cluster.size;
                metrics.density.maxPossibleEdges = (n * (n-1)) / 2;
                metrics.density.density = if metrics.density.maxPossibleEdges > 0 
                    then metrics.connectivity.totalInternalEdges:real / metrics.density.maxPossibleEdges:real
                    else 0.0;
                metrics.density.sparsity = 1.0 - metrics.density.density;
            }
        
            // Triangle metrics
            if runConfig.computeTriangles {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Triangle Metrics -----");
                }
                var (densityMetrics, triangleStats) = calculateTriangleMetrics(cluster, metrics.density);
                metrics.density = densityMetrics;
                if runConfig.computeTriangleDistribution {
                    metrics.triangleDistribution = triangleStats;
                }
            }

            if runConfig.computeTriangleCentrality {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Triangle Centrality -----");
                }
                var tcMetrics = calculateTriangleCentrality(cluster);
                metrics.connectivity.triangleCentrality = tcMetrics.triangleCentralities;
            }
            // Spectral metrics
            if runConfig.computeSpectral {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Spectral Metrics -----");
                }
                var (conductance, volumeCluster, outEdges) = calculateConductance(cluster);
                metrics.connectivity.clusterVolume = volumeCluster;
                metrics.connectivity.clusterCutEdges = outEdges;
                metrics.spectral = calculateSpectralBounds(conductance);
                metrics.spectral.conductance = conductance;
            }

            // Transitivity metrics
            if runConfig.computeTransitivity {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Transitivity Metrics -----");
                }
                metrics.transitivity = calculateTransitivityMetrics(cluster);
            }

            // Diameter and eccentricity metrics
            if runConfig.computeDiameter {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Diameter Metrics -----");
                }
                var diameterMetrics = calculateDiameter(cluster);
                metrics.connectivity.diameter = diameterMetrics.estimatedDiameter;
                metrics.connectivity.diameterLowerBound = diameterMetrics.lowerBound;
                metrics.connectivity.diameterUpperBound = diameterMetrics.upperBound;
                metrics.connectivity.exactDiameter = diameterMetrics.exactDiameter;

                metrics.eccentricity = calculateEccentricityMetrics(cluster, metrics.connectivity.diameter);
            }

            // Distribution statistics
            if runConfig.computeDegreeDistribution {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Degree Distribution -----");
                }
                var degrees = [v in cluster] (neighborsSetGraphG1[v] & cluster).size: real;
                metrics.degreeDistribution = calculateDistributionStats(degrees);
            }

            if runConfig.computeCoreMetrics {
                if logLevel == LogLevel.DEBUG {
                    writeln("\n----- Computing Core Metrics -----");
                }
                // Basic core numbers first
                // var basicCore = calculateCoreNumbers(cluster);
                // metrics.core = basicCore;
                
                // Then advanced core metrics if needed
                var advancedCore = calculateAdvancedCore(cluster);
                metrics.core = advancedCore;  // This will include both basic and advanced metrics
            }



        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Analysis Complete -----");
        }

    } catch e {
        writeln("Error in analyzeCluster: ", e.message());
        metrics = initializeEmptyMetrics();
    }


        printClusterAnalysis(metrics, cluster.size);
    
    return metrics;
}

/* Calculate distribution statistics */
proc calculateDistributionStats(ref data: [?D1] real) {
    var stats = new distributionStats();
    
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Calculating Distribution Statistics ====");
        writeln("Sample size: ", data.size);
        writeln("data.domain: ", data.domain);
    }

    // Calculate mean
    stats.mean = + reduce data / data.size;
    
    // Calculate median and percentiles

    // var sortedData = data;
    var sortedData: [0..data.size - 1] real; // 0-indexed array for sorted data
    var i = 0;
    for val in data {
        sortedData[i] = val;
        i += 1;
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("sortedData.domin: ", sortedData.domain);
        writeln("sortedData: ", sortedData);
    }

    sort(sortedData);
    stats.median = if data.size % 2 == 0 
                  then (sortedData[data.size/2 - 1] + sortedData[data.size/2]) / 2.0
                  else sortedData[data.size/2];
    
    // Calculate standard deviation
    var variance = 0.0;
    forall x in data with (+ reduce variance) {
        var diff = x - stats.mean;
        variance += diff * diff;
    }

    stats.standardDev = sqrt(max(variance / (data.size - 1), 0.0));
    
    // Calculate higher moments (skewness and kurtosis)
        // Check if all values are same
    if stats.standardDev == 0.0 {
        stats.skewness = 0.0;  // No skewness when all values same
        stats.kurtosis = 0.0;  // No kurtosis when all values same
    } else {
        var m3 = 0.0, m4 = 0.0;
        forall x in data with (+ reduce m3, + reduce m4) {
            var diff = x - stats.mean;
            var diff2 = diff * diff;
            m3 += diff * diff2;
            m4 += diff2 * diff2;
        }
    
        stats.skewness = m3 / (data.size * stats.standardDev ** 3);
        stats.kurtosis = m4 / (data.size * stats.standardDev ** 4) - 3.0;
    }
    
    // Calculate percentiles
    for i in 0..100 {
        var idx = (i:real * (data.size-1):real / 100.0):int;
        stats.percentiles[i] = sortedData[idx];
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nDistribution Statistics:");
        writeln("  Mean: ", stats.mean);
        writeln("  Median: ", stats.median);
        writeln("  Standard Deviation: ", stats.standardDev);
        writeln("  Skewness: ", stats.skewness);
        writeln("  Kurtosis: ", stats.kurtosis);
        writeln("  Key Percentiles:");
        writeln("    25th: ", stats.percentiles[25]);
        writeln("    50th: ", stats.percentiles[50]);
        writeln("    75th: ", stats.percentiles[75]);
        writeln("==== Distribution Statistics Complete ====\n");
    }

    return stats;
}

/* Calculate triangle-based metrics including clustering coefficients and distribution */
proc calculateTriangleMetrics(ref cluster: set(int), ref metrics: densityMetrics) throws {
   if logLevel == LogLevel.DEBUG {
       writeln("\n==== Starting Triangle and Clustering Analysis ====");
       writeln("Original cluster size: ", cluster.size);
   }

   var updatedMetrics = metrics;
   
   // Convert to array and create domain
   var clusterArray = cluster.toArray();
   var clusterDomain: domain(int, parSafe=true) = clusterArray;

   // Arrays for accumulating metrics
   var totalTriangles: atomic int;
   var totalWedges: atomic int;
   var sumLocalCC: atomic real;
   var validVertices: atomic int;
   var participatingVertices: atomic int;
   var maxTriangles: atomic int;
   var totalEdges: atomic int;
   
   // Array for triangle distribution
   var triangleCounts: [clusterDomain] atomic int;

   if logLevel == LogLevel.DEBUG {
       writeln("Starting triangle counting and wedge calculation");
   }

   // Process vertices in parallel
   forall v in clusterDomain {
       var v_neighbors = neighborsSetGraphG1[v] & cluster;
       var v_deg = v_neighbors.size;
       totalEdges.add(v_deg);
       
       if logLevel == LogLevel.DEBUG {
           writeln("\nProcessing vertex ", v);
           writeln("  Degree: ", v_deg);
           writeln("  Neighbors: ", v_neighbors);
       }
       
       if v_deg >= 2 {
           validVertices.add(1);
           var localTriangles = 0;
           var possibleTriangles = (v_deg * (v_deg - 1)) / 2;
           totalWedges.add(possibleTriangles);

           // Count triangles
           for u in v_neighbors {
               var u_neighbors = neighborsSetGraphG1[u] & cluster;
               if logLevel == LogLevel.DEBUG {
                   writeln("    Checking neighbor ", u);
                   writeln("    U's neighbors: ", u_neighbors);
               }
               for w in v_neighbors {
                   if u != w {
                       if u_neighbors.contains(w) {
                           localTriangles += 1;
                           if localTriangles == 1 {  // Mark participating on first triangle
                               participatingVertices.add(1);
                           }
                           if logLevel == LogLevel.DEBUG {
                               writeln("      Found triangle: ", v, "-", u, "-", w);
                           }
                       }
                   }
               }
           }

           // Store raw triangle count for max triangles and distribution
           var rawTriangles = localTriangles;  // Before division
           triangleCounts[v].write(rawTriangles/2);
           maxTriangles.write(max(maxTriangles.read(), rawTriangles/2));

           // Now divide for final counts
           localTriangles /= 2;
           totalTriangles.add(localTriangles);

           // Calculate local clustering coefficient
           var localCC = if possibleTriangles > 0 
                        then localTriangles:real / possibleTriangles:real
                        else 0.0;
           sumLocalCC.add(localCC);

           if logLevel == LogLevel.DEBUG {
               writeln("  Stats for vertex ", v, ":");
               writeln("    Raw triangles: ", rawTriangles);
               writeln("    Local triangles (after division): ", localTriangles);
               writeln("    Possible triangles: ", possibleTriangles);
               writeln("    Local CC: ", localCC);
           }
       }
   }

   // Calculate final metrics
   var finalTriangles = totalTriangles.read() / 3;  // Each triangle counted thrice
   var finalWedges = totalWedges.read();
   var numValidVertices = validVertices.read();
   var edges = totalEdges.read() / 2;

   // Update density metrics
   updatedMetrics.triangleCount = finalTriangles;
   updatedMetrics.avgLocalClusteringCoeff = sumLocalCC.read() / cluster.size:real;
   updatedMetrics.globalClusteringCoeff = if finalWedges > 0
                                         then (finalTriangles:real * 3.0) / finalWedges:real
                                         else 0.0;

   // Update triangle distribution metrics
   updatedMetrics.triangleDensity = if edges > 0 
                                   then finalTriangles:real / edges:real
                                   else 0.0;
   updatedMetrics.participationRate = participatingVertices.read():real / cluster.size:real;
   updatedMetrics.maxLocalTriangles = maxTriangles.read();
   updatedMetrics.avgTrianglesPerVertex = finalTriangles:real / cluster.size:real;

   // Convert triangle counts to real array for distribution stats
   var triangleDistArray: [clusterDomain] real;
   forall i in clusterDomain do
       triangleDistArray[i] = triangleCounts[i].read():real;
   
   // Calculate distribution statistics
   var triangleDistStats = calculateDistributionStats(triangleDistArray);

   if logLevel == LogLevel.DEBUG {
       writeln("\nFinal Results:");
       writeln("Total triangles: ", finalTriangles);
       writeln("Total wedges: ", finalWedges);
       writeln("Valid vertices: ", numValidVertices);
       writeln("Participating vertices: ", participatingVertices.read());
       writeln("Maximum triangles per vertex: ", maxTriangles.read());
       writeln("Average local CC: ", updatedMetrics.avgLocalClusteringCoeff);
       writeln("Global CC: ", updatedMetrics.globalClusteringCoeff);
       writeln("Triangle density: ", updatedMetrics.triangleDensity);
       writeln("Participation rate: ", updatedMetrics.participationRate);
       writeln("\nTriangle Distribution Statistics:");
       writeln("Mean: ", triangleDistStats.mean);
       writeln("Median: ", triangleDistStats.median);
       writeln("Standard Deviation: ", triangleDistStats.standardDev);
       writeln("==== Triangle Analysis Complete ====\n");
   }

   return (updatedMetrics, triangleDistStats);
}

/* Calculate path-based metrics */
proc calculatePathMetrics(ref cluster: set(int), globalTransitivity: real, localTransitivity: real, clusterDensity: real) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Path Metrics Analysis ====");
        writeln("Global transitivity: ", globalTransitivity);
        writeln("Local transitivity: ", localTransitivity);
        writeln("Cluster density: ", clusterDensity);
    }

    var metrics = new pathMetrics();
    
    // Calculate local/global ratio
    metrics.localGlobalRatio = if globalTransitivity > 0.0 then 
                              localTransitivity / globalTransitivity else 0.0;
    
    // Calculate cohesion score (based on transitivity and density)
    metrics.cohesionScore = (metrics.localGlobalRatio + clusterDensity) / 2.0;
    
    if logLevel == LogLevel.DEBUG {
        writeln("\nPath Metrics Results:");
        writeln("  Local/Global ratio: ", metrics.localGlobalRatio);
        writeln("  Cohesion score: ", metrics.cohesionScore);
        writeln("==== Path Metrics Analysis Complete ====\n");
    }

    return metrics;
}
/* Calculate eccentricity-based metrics */
proc calculateEccentricityMetrics(ref cluster: set(int), diameter: int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Eccentricity Analysis ====");
        writeln("Diameter: ", diameter);
    }

    // Convert cluster to array and create proper domain
    var clusterArray = cluster.toArray();
    var clusterDomain: domain(int, parSafe=true) = clusterArray;
    
    if logLevel == LogLevel.DEBUG {
        writeln("Created domain from cluster of size: ", clusterArray.size);
    }

    var metrics = new eccentricityMetrics();
    var eccentricities: [clusterDomain] atomic int;
    
    // Calculate eccentricities for each vertex
    forall v in cluster with(ref cluster){
        var maxDist = 0;
        var (dist, _) = enhancedBFS(v, cluster);
        eccentricities[v].write(dist);
    }
    
    // Find radius and center vertices
    var radius = min reduce [v in cluster] eccentricities[v].read();
    metrics.radius = radius;
    
    // Identify center and peripheral vertices
    var centerSet: set(int, parSafe=true);  
    var peripheralSet: set(int, parSafe=true);

    forall v in cluster with(ref centerSet, ref peripheralSet) {
        var ecc = eccentricities[v].read();
        if ecc == radius then
            centerSet.add(v);
        if ecc == diameter then
            peripheralSet.add(v);
    }

    // After parallel section, convert to lists
    for v in centerSet do
        metrics.centerVertices.pushBack(v);
    for v in peripheralSet do
        metrics.peripheralVertices.pushBack(v);
    
    // Calculate average eccentricity
    metrics.avgEccentricity = (+ reduce [v in cluster] eccentricities[v].read()):real / cluster.size:real;

    if logLevel == LogLevel.DEBUG {
        writeln("\nEccentricity Results:");
        writeln("  Radius: ", metrics.radius);
        writeln("  Number of center vertices: ", metrics.centerVertices.size);
        writeln("  Number of peripheral vertices: ", metrics.peripheralVertices.size);
        writeln("  Average eccentricity: ", metrics.avgEccentricity);
        writeln("==== Eccentricity Analysis Complete ====\n");
    }

    return metrics;
}
/* Enhanced BFS for cluster analysis */
proc enhancedBFS(start: int, ref cluster: set(int)) {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Enhanced BFS ====");
        writeln("Starting vertex: ", start);
        writeln("Cluster size: ", cluster.size);
    }

    // Create arrays and domains
    var maxDist = 0;
    
    var clusterArray = cluster.toArray();
    if logLevel == LogLevel.DEBUG {
        writeln("Created cluster array of size: ", clusterArray.size);
    }

    var clusterDomain: domain(int, parSafe=true) = clusterArray;
    if logLevel == LogLevel.DEBUG {
        writeln("Created domain: ", clusterDomain);
    }
    var depth: [clusterDomain] int = -1;

    // Check if start vertex is valid
    if !clusterDomain.contains(start) {
        writeln("ERROR: Start vertex ", start, " not in cluster domain");
        return (0, depth);
    }

    // Create frontier sets for current and next level
    var frontierSets: [0..1] list(int, parSafe=true);
    frontierSets[0] = new list(int, parSafe=true);
    frontierSets[1] = new list(int, parSafe=true);
    
    // Initialize BFS from start vertex
    var currentLevel: atomic int;
    currentLevel.write(0);
    depth[start] = 0;
    frontierSets[0].pushBack(start);
    var frontierIdx = 0;

    if logLevel == LogLevel.DEBUG {
        writeln("Initialized frontier sets and depth array");
        writeln("Starting BFS traversal");
    }
    
    while true {
        var pendingWork = false;
        
        if logLevel == LogLevel.DEBUG {
            writeln("\nProcessing level ", currentLevel.read());
            writeln("Current frontier size: ", frontierSets[frontierIdx].size);
        }
        
        forall u in frontierSets[frontierIdx] with (|| reduce pendingWork, 
                                                   max reduce maxDist,
                                                   ref currentLevel) {
            var neighbors = neighborsSetGraphG1[u] & cluster;
            var uLevel = depth[u];
            
            if logLevel == LogLevel.DEBUG {
                writeln("Processing vertex ", u, " at level ", uLevel);
                writeln("Number of neighbors: ", neighbors.size);
            }
            
            for v in neighbors {
                if depth[v] == -1 {
                    pendingWork = true;
                    var newLevel = uLevel + 1;
                    depth[v] = newLevel;
                    frontierSets[(frontierIdx + 1) % 2].pushBack(v);
                    maxDist = max(maxDist, newLevel);
                    currentLevel.write(newLevel);
                    
                    if logLevel == LogLevel.DEBUG {
                        writeln("  Found new vertex ", v, " at level ", newLevel);
                    }
                }
            }
        }
        
        frontierSets[frontierIdx].clear();
        if !pendingWork then break;
        
        frontierIdx = (frontierIdx + 1) % 2;
        
        if logLevel == LogLevel.DEBUG {
            writeln("Completed level ", currentLevel.read());
            writeln("Current max distance: ", maxDist);
        }
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("\nBFS Complete:");
        writeln("$$$ Maximum distance found: ", maxDist);
        writeln("==== Enhanced BFS Complete ====\n");
    }
    
    return (maxDist, depth);
}
/* Enhanced diameter calculation using double sweep */
proc calculateDiameter(ref cluster: set(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Enhanced Diameter Calculation ====");
        writeln("Cluster size: ", cluster.size);
    }

    var metrics = new diameterMetrics();
    
    // For very small clusters, use exact calculation
    if cluster.size <= 1000 {
        if logLevel == LogLevel.DEBUG {
            writeln("Using exact calculation for small cluster");
        }
        metrics.exactDiameter = true;
        var maxDist = 0;
        
        forall v in cluster with (max reduce maxDist, ref cluster) {
            var (dist, _) = enhancedBFS(v, cluster);
            maxDist = max(maxDist, dist);
        }
        
        metrics.lowerBound = maxDist;
        metrics.upperBound = maxDist;
        metrics.estimatedDiameter = maxDist:int;
        return metrics;
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Using approximate calculation for large cluster");
    }
    // For larger clusters, use double sweep with sampling
    metrics.exactDiameter = false;
    
    // First sweep from random vertex
    if logLevel == LogLevel.DEBUG {
        writeln("Converting cluster to array");
    }
    var clusterArray = cluster.toArray();
    
    if logLevel == LogLevel.DEBUG {
        writeln("Created array of size: ", clusterArray.size);
        writeln("Setting up random number generator");
    }
    
    var rng = new randomStream(real);
    
    if logLevel == LogLevel.DEBUG {
        writeln("Selecting random start vertex");
    }
    
    var randIdx = (rng.next() * (cluster.size-1)):int;
    
    if logLevel == LogLevel.DEBUG {
        writeln("Selected random index: ", randIdx);
    }

    var start = clusterArray[randIdx];
    
    if logLevel == LogLevel.DEBUG {
        writeln("Selected start vertex: ", start);
    }

  
    var (firstDist, firstDepths) = enhancedBFS(start, cluster);
    
    // Find farthest vertex
    var maxDist = 0;
    var farthestVertex = start;
    forall v in cluster with (max reduce maxDist, 
                            ref farthestVertex) {
        if firstDepths[v] > maxDist {
            maxDist = firstDepths[v];
            farthestVertex = v;
        }
    }
    
    // Second sweep from farthest vertex
    var (secondDist, _) = enhancedBFS(farthestVertex, cluster);
    
    metrics.lowerBound = secondDist;
    metrics.upperBound = min(2 * secondDist, cluster.size - 1);
    metrics.estimatedDiameter = ((metrics.lowerBound + metrics.upperBound) / 2.0):int;

    if logLevel == LogLevel.DEBUG {
        writeln("\nDiameter Results:");
        writeln("  First sweep max distance: ", firstDist);
        writeln("  Second sweep max distance: ", secondDist);
        writeln("  Lower bound: ", metrics.lowerBound);
        writeln("  Upper bound: ", metrics.upperBound);
        writeln("==== Diameter Calculation Complete ====\n");
    }
    
    return metrics;
}

/* Perform double sweep for initial diameter bounds */
proc doubleSweepEstimate(ref cluster: set(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\nStarting double sweep diameter estimation");
    }

    // First sweep: start from random vertex
    var clusterArray = cluster.toArray();
    var rng = new randomStream(int);
    var start = clusterArray[rng.next(0..#cluster.size)];
    
    var (dist1, firstDistances) = bfsDistance(start, cluster);
    
    // Find farthest vertex from start
    var maxDist = 0;
    var farthestVertex = start;
    for v in cluster {
        if firstDistances[v] > maxDist {
            maxDist = firstDistances[v];
            farthestVertex = v;
        }
    }
    
    // Second sweep: from farthest vertex
    var (dist2, _) = bfsDistance(farthestVertex, cluster);
    
    if logLevel == LogLevel.DEBUG {
        writeln("Double sweep results:");
        writeln("  First sweep max distance: ", dist1);
        writeln("  Second sweep max distance: ", dist2);
    }
    
    return dist2;  // This is a lower bound on the diameter
}

/* Calculate transitivity-based metrics for a cluster with parallel optimizations */
proc calculateTransitivityMetrics(ref cluster: set(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Transitivity Metrics Calculation ====");
        writeln("Original cluster size: ", cluster.size);
    }

    var analysisCluster = cluster;
    
    // Handle sampling for large clusters
    if cluster.size > 10000 {
        const sampleSize = if cluster.size <= 50000 then (cluster.size * 0.2): int
                     else if cluster.size <= 100000 then (cluster.size * 0.1): int
                     else (cluster.size * 0.05): int;

        if logLevel == LogLevel.DEBUG {
            writeln("Cluster size > 10000, using sampling");
            writeln("Calculated sample size: ", sampleSize);
        }
        analysisCluster = sampleClusterVertices(cluster, sampleSize);
    }

    var metrics = new transitivityMetrics();
    
    // Atomic counters for parallel processing
    var totalWedges: atomic int;
    var totalTriangles: atomic int;

    // Create domain from cluster for parallel iteration
    var clusterArray = analysisCluster.toArray();
    var clusterDomain: domain(int, parSafe=true) = clusterArray;

    // Pre-compute and cache neighbor sets to avoid repeated computation
    var neighborCache: [clusterDomain] set(int);
    
    if logLevel == LogLevel.DEBUG {
        writeln("Pre-computing neighbor sets");
    }
    
    // Parallel neighbor set computation
    forall v in clusterDomain {
        neighborCache[v] = neighborsSetGraphG1[v] & analysisCluster;
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Starting parallel wedge and triangle counting");
    }

    // Parallel processing of vertices
    forall v in clusterDomain {
        var neighbors = neighborCache[v];
        var degree = neighbors.size;
        
        // Count wedges (potential triangles)
        if degree >= 2 {
            var possibleWedges = (degree * (degree - 1)) / 2;
            totalWedges.add(possibleWedges);
            
            // Count actual triangles
            // Process only higher-ID neighbors to avoid counting triangles multiple times
            for u in neighbors {
                if u > v {
                    var u_neighbors = neighborCache[u];
                    // Use set intersection for common neighbors
                    for w in (u_neighbors & neighbors) {
                        if w > u {  // Maintain strict ordering
                            if logLevel == LogLevel.DEBUG {
                                //writeln("Found triangle: ", v, "-", u, "-", w);
                            }
                            totalTriangles.add(1);
                        }
                    }
                }
            }
        }
    }

    // Calculate final metrics
    metrics.wedgeCount = totalWedges.read();
    var triangles = totalTriangles.read();
    
    // Scale metrics if sampling was used
    if cluster.size > 10000 {
        var scaleFactor = cluster.size:real / analysisCluster.size:real;
        metrics.wedgeCount = (metrics.wedgeCount:real * scaleFactor):int;
        triangles = (triangles:real * scaleFactor):int;
    }

    // Calculate final ratios with checks for division by zero
    if metrics.wedgeCount > 0 {
        // Multiply triangles by 3 because each triangle creates three wedges
        metrics.triangleToWedgeRatio = triangles:real / metrics.wedgeCount:real;
        metrics.globalTransitivity = (3 * triangles):real / metrics.wedgeCount:real;
    } else {
        metrics.triangleToWedgeRatio = 0.0;
        metrics.globalTransitivity = 0.0;
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nFinal Results:");
        writeln("Analyzed vertices: ", analysisCluster.size);
        writeln("Total wedges found: ", metrics.wedgeCount);
        writeln("Total triangles found: ", triangles);
        writeln("Triangle-to-Wedge ratio: ", metrics.triangleToWedgeRatio);
        writeln("Global transitivity: ", metrics.globalTransitivity);
        writeln("==== Transitivity Metrics Calculation Complete ====\n");
    }

    return metrics;
}

proc calculateConductance(ref cluster: set(int)) throws {
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

    var volumeComplement = graphGlobalRecord.totalVolume - volumeCluster;
    // Calculate conductance
    var denom = min(volumeCluster, volumeComplement);
    if denom > 0 {
        conductance = outEdges / denom: real;
    } else {
        conductance = 0.0;
    }
    /* Debug output for cluster analysis */
    if logLevel == LogLevel.DEBUG {
        writeln("\nGraph Volume:", graphGlobalRecord.totalVolume);
        writeln("Cluster Analysis:");
        writeln("Size: ", cluster.size);
        writeln("Cluster Volume: ", volumeCluster);
        writeln("Cluster cutedges: ", outEdges);
        writeln("Conductance: ", conductance);
        writeln("Spectral Bounds (λ2):");

    }

    return (conductance, volumeCluster, outEdges);
}
/* Basic spectral bounds based on conductance */
proc calculateSpectralBounds(conductance: real) {
    var metrics: spectralMetrics;
    if logLevel == LogLevel.DEBUG {
        writeln("==================== calculateSpectralBounds ======================");
    }

    // Store conductance
    metrics.conductance = conductance;

    // Basic Cheeger inequality bounds
    metrics.lambda2Lower = (conductance * conductance) / 2;
    metrics.lambda2Upper = 2 * conductance;
    metrics.lambda2Estimate = (metrics.lambda2Lower + metrics.lambda2Upper) / 2;


    
    return metrics;
}

/* Basic statistics calculation - foundation for other metrics */
proc calculateBasicStats(in cluster: set(int)) throws {
    const SAMPLE_THRESHOLD = 500; 
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
        var clusterVolume: int;         // cluster Volume
    }
    
    var stats = new BasicStats();
    stats.n_vertices = cluster.size;

    const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
    var tempDegrees: [clusterDomain] int;     // Degree sequence
    // First calculate degrees
    forall v in cluster with(ref tempDegrees) {
        // var neighbors = neighborsSetGraphG1[v];
        tempDegrees[v] = calculateClusterDegree(cluster , v);
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
  /* Basic connectivity metrics */
    proc calculateBasicConnectivity(ref cluster: set(int)) throws {
        var metrics: connectivityMetrics;
        
        // Handle empty or singleton clusters
        if cluster.size <= 1 {
            metrics.n_vertices = 0;
            metrics.minDegree = 0;
            metrics.maxDegree = 0;
            metrics.totalInternalEdges = 0;
            metrics.avgDegree = 0.0;
            metrics.edgeConnectivityLowerBound = 0;
            return metrics;
        }
        metrics.n_vertices = cluster.size;
        // Get basic statistics first
        var basicStats = calculateBasicStats(cluster);

        // Set basic metrics from stats
        metrics.degreeSecondMoment = basicStats.degree_second_moment;
        metrics.clusterVolume = basicStats.clusterVolume;
        metrics.minDegree = basicStats.min_degree;
        metrics.maxDegree = basicStats.max_degree;
        metrics.avgDegree = basicStats.avg_degree;
        metrics.totalInternalEdges = basicStats.n_edges;
        
        // Calculate degree variance and skewness in one pass
        var variance_sum = 0.0;
        var skewness_sum = 0.0;
        forall v in cluster with (+ reduce variance_sum, + reduce skewness_sum) {
            var diff = basicStats.degrees[v] - metrics.avgDegree;
            var diff_squared = diff * diff;
            variance_sum += diff_squared;
            skewness_sum += diff_squared * diff;
        }
        
        metrics.degreeVariance = variance_sum / cluster.size;
        metrics.degreeSkewness = if metrics.degreeVariance > 0 then 
            (skewness_sum / cluster.size) / (sqrt(metrics.degreeVariance) ** 3)
            else 0.0;
        
        // Calculate Mader's theorem bound
        metrics.edgeConnectivityLowerBound = ((metrics.avgDegree + 2) / 2): int;
        
        return metrics;
    }

/* Advanced connectivity metrics with sampling for large clusters */
proc calculateAdvancedConnectivity(ref cluster: set(int)) throws {
    var metrics: connectivityMetrics;
    
    // Determine sample size based on cluster size
    const SAMPLE_SIZE = max(2, ceil(log2(cluster.size) * 10): int);
    
    // Get basic stats first 
    var basicStats = calculateBasicStats(cluster);
    
    // Calculate assortativity
    metrics = calculateAssortativity(cluster, basicStats, metrics);
    
    // For very large clusters, use sampling for expensive computations
    var sampleSet = if cluster.size > 10000 then sampleClusterVertices(cluster, SAMPLE_SIZE)
                                              else cluster;
    
    // Calculate diameter and betweenness (placeholder - need to implement)
    if logLevel == LogLevel.DEBUG {
        writeln("Using sample size: ", sampleSet.size, " for diameter and betweenness");
    }
    
    return metrics;
}


/* Sampling function for large cluster analysis */
proc sampleClusterVertices(ref cluster: set(int), sampleSize: int) {
    if cluster.size <= 10000 {
        if logLevel == LogLevel.DEBUG {
            writeln("Cluster size <= 10000, using full cluster");
        }
        return cluster;
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Starting sampling for cluster of size ", cluster.size);
        writeln("Target sample size: ", sampleSize);
    }

    var sampledVertices: set(int);
    var clusterArray = cluster.toArray();
    var rng = new randomStream(real);
    
    // Calculate vertex weights based on degree within the cluster
    var weights: [clusterArray.domain] real;
    var maxDegree = max reduce [v in cluster] (neighborsSetGraphG1[v] & cluster).size;

    forall i in clusterArray.domain {
        var vertex = clusterArray[i];
        var degree = (neighborsSetGraphG1[vertex] & cluster).size;  // Degree within cluster
        weights[i] = sqrt(degree: real / maxDegree: real);
    }
    
    // Normalize weights
    var totalWeight = + reduce weights;
    weights /= totalWeight;
    
    // Perform weighted sampling
    var available = cluster;
    while (sampledVertices.size < sampleSize && available.size > 0) {
        var r = rng.next();
        var cumSum = 0.0;
        
        for i in clusterArray.domain {
            var vertex = clusterArray[i];
            if available.contains(vertex) {
                cumSum += weights[i];
                if r <= cumSum {
                    sampledVertices.add(vertex);
                    available.remove(vertex);
                    break;
                }
            }
        }
    }
    
    if logLevel == LogLevel.DEBUG {
        writeln("Sampling complete. Selected ", sampledVertices.size, " vertices");
        writeln("Sample average degree: ", 
                (+ reduce [v in sampledVertices] neighborsSetGraphG1[v].size) / sampledVertices.size);
    }
    
    return sampledVertices;
}


/* Comparator for sorting vertices by degree */
record DegreeComparator {
    proc compare(a: (int, int), b: (int, int)): int {
        return a(1) - b(1);  // Sort by degree (second element of tuple)
    }
}



/* Calculate triangle centrality for a cluster */
proc calculateTriangleCentrality(ref cluster: set(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Triangle Centrality Calculation ====");
        writeln("Cluster size: ", cluster.size);
    }

    // Create array and domain from cluster
    var clusterArray = cluster.toArray();
    var clusterDomain: domain(int, parSafe=true) = clusterArray;
    
    // Arrays to track triangle participation
    var vertexTriangles: [clusterDomain] atomic int;        // Number of triangles per vertex
    var neighborTriangles: [clusterDomain] atomic int;      // Number of triangles for neighbors
    var tempCentralities: [clusterDomain] real;         // Final centrality values
    
    // Initialize arrays
    forall v in clusterDomain {
        vertexTriangles[v].write(0);
        neighborTriangles[v].write(0);
        tempCentralities[v] = 0.0;
    }

    var totalTriangles: atomic int;

    if logLevel == LogLevel.DEBUG {
        writeln("Starting triangle counting phase");
    }

    // Count triangles and update vertex participation
    forall v in clusterDomain {
        var neighbors = neighborsSetGraphG1[v] & cluster;
        
        for u in neighbors {
            if u > v {  // Process each edge once
                var u_neighbors = neighborsSetGraphG1[u] & cluster;
                
                // Find common neighbors forming triangles
                for w in (u_neighbors & neighbors) {
                    if w > u {  // Ensure ordered counting
                        totalTriangles.add(1);
                        
                        // Update triangle counts for all vertices in the triangle
                        vertexTriangles[v].add(1);
                        vertexTriangles[u].add(1);
                        vertexTriangles[w].add(1);
                        
                        if logLevel == LogLevel.DEBUG {
                            writeln("Found triangle: ", v, "-", u, "-", w);
                        }
                    }
                }
            }
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nCalculating neighbor triangle counts");
    }

    // Calculate neighbor triangle counts
    forall v in clusterDomain {
        var neighbors = neighborsSetGraphG1[v] & cluster;
        for u in neighbors {
            neighborTriangles[v].add(vertexTriangles[u].read());
        }
    }

    // Calculate final centralities
    if logLevel == LogLevel.DEBUG {
        writeln("\nCalculating final centralities");
    }

    var finalTriangleCount = totalTriangles.read();
    if finalTriangleCount > 0 {
        forall v in clusterDomain {
            var v_triangles = vertexTriangles[v].read();
            var neighbor_sum = neighborTriangles[v].read();
            
            // Calculate centrality using the formula from the original code
            tempCentralities[v] = (
                v_triangles + 
                (neighbor_sum - (neighborTriangles[v].read() + v_triangles) * 2.0 / 3.0)
            ) / finalTriangleCount:real;
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nTriangle Centrality Results:");
        writeln("Total triangles: ", finalTriangleCount);
        writeln("Sample centralities:");
        var sampleSize = min(5, cluster.size);
        for i in 0..#sampleSize {
            writeln("Vertex ", clusterArray[i], ": ", tempCentralities[clusterArray[i]]);
        }
        writeln("==== Triangle Centrality Calculation Complete ====\n");
    }

    // Convert results to list and return metrics
    var metrics = new triangleCentralityMetrics();
    for v in clusterDomain {
        metrics.triangleCentralities.pushBack(tempCentralities[v]);
    }
    metrics.totalTriangles = finalTriangleCount;
    
    return metrics;
}
/* Basic core numbers calculation */
proc calculateCoreNumbers(in cluster: set(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Core Number Calculation ====");
        writeln("Cluster size: ", cluster.size);
    }

    var metrics: coreMetrics;

    // Handle empty or singleton clusters
    if cluster.size <= 1 {
        if logLevel == LogLevel.DEBUG {
            writeln("Empty or singleton cluster detected");
        }
        metrics.coreNumber = 0;
        metrics.coreDensity = 0.0;
        metrics.coreSize = cluster.size;
        return metrics;
    }

    // Create domain and arrays for tracking degrees
    var clusterArray = cluster.toArray();
    var clusterDomain: domain(int, parSafe=true) = clusterArray;
    var degrees: [clusterDomain] atomic int;
    var vertexShells: [clusterDomain] atomic int;
    var vertexProcessed: [clusterDomain] atomic bool;  // New: track processed vertices
    
    // Initialize degrees in parallel
    forall v in clusterDomain {
        var deg = calculateClusterDegree(cluster, v);
        degrees[v].write(deg);
        vertexShells[v].write(-1);
        vertexProcessed[v].write(false);
    }

    // Core decomposition
    var maxDegree = max reduce [v in clusterDomain] degrees[v].read();
    var shellMembers: [0..maxDegree] set(int, parSafe=true);
    var currentDegrees: [clusterDomain] atomic int;  // New: track current degrees separately
    
    // Initialize current degrees
    forall v in clusterDomain {
        currentDegrees[v].write(degrees[v].read());
    }

    var k = 0;
    var remainingVertices = cluster.size;
    
    while remainingVertices > 0 {
        var processedAny: atomic bool = false;
        
        // Process vertices in parallel
        forall v in clusterDomain with (ref shellMembers) {
            // Only process unprocessed vertices with current degree <= k
            if !vertexProcessed[v].read() && currentDegrees[v].read() <= k {
                vertexProcessed[v].write(true);
                vertexShells[v].write(k);
                shellMembers[k].add(v);
                processedAny.write(true);
                
                // Update neighbors' degrees
                var neighbors = neighborsSetGraphG1[v] & cluster;
                for u in neighbors {
                    if !vertexProcessed[u].read() {
                        currentDegrees[u].sub(1);
                    }
                }
            }
        }
        
        // If no vertices were processed at this k, increment k
        if !processedAny.read() {
            k += 1;
            if k > maxDegree then break;
        } else {
            remainingVertices = + reduce [v in clusterDomain] (!vertexProcessed[v].read());
        }
    }

    // Calculate final metrics
    metrics.coreNumber = max reduce [v in clusterDomain] vertexShells[v].read();
    var maxCoreVertices = shellMembers[metrics.coreNumber];
    metrics.coreSize = maxCoreVertices.size;
    metrics.maxCoreSize = maxCoreVertices.size;

    // Calculate core density in parallel
    if maxCoreVertices.size > 1 {
        var edgeCount: atomic int;
        forall v in maxCoreVertices with (ref edgeCount) {
            var coreNeighbors = neighborsSetGraphG1[v] & maxCoreVertices;
            edgeCount.add(coreNeighbors.size);
        }
        var numEdges = edgeCount.read() / 2;
        var maxPossibleEdges = (maxCoreVertices.size * (maxCoreVertices.size - 1)) / 2;
        metrics.coreDensity = if maxPossibleEdges > 0 then numEdges:real / maxPossibleEdges:real else 0.0;
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nFinal Results:");
        writeln("  Core Number: ", metrics.coreNumber);
        writeln("  Core Size: ", metrics.coreSize);
        writeln("  Core Density: ", metrics.coreDensity);
        writeln("==== Core Number Calculation Complete ====\n");
    }

    return metrics;
}

/* Enhanced core analysis implementation */
proc calculateAdvancedCore(ref cluster: set(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Advanced Core Analysis ====");
        writeln("Cluster size: ", cluster.size);
    }

    var metrics: coreMetrics;
    
    // Basic initialization and checks
    if cluster.size <= 1 {
        if logLevel == LogLevel.DEBUG {
            writeln("Empty or singleton cluster detected");
        }
        return calculateCoreNumbers(cluster);  // Return basic metrics for small clusters
    }

    // Handle sampling for large clusters
    var analysisCluster = cluster;
    if cluster.size > 100000 {
        const sampleSize = if cluster.size <= 500000 then (cluster.size * 0.1): int     
                     else if cluster.size <= 1000000 then (cluster.size * 0.05): int   
                     else (cluster.size * 0.01): int;                                  

        if logLevel == LogLevel.DEBUG {
            writeln("Large cluster detected, using sampling");
            writeln("Sample size: ", sampleSize);
        }
        analysisCluster = sampleClusterVertices(cluster, sampleSize);
    }
    
    // Get basic core decomposition first
    metrics = calculateCoreNumbers(analysisCluster);
    
    if logLevel == LogLevel.DEBUG {
        writeln("Basic core numbers calculated");
        writeln("Starting shell decomposition");
    }
    
    // Create necessary data structures
    var clusterArray = analysisCluster.toArray();
    var clusterDomain: domain(int, parSafe=true) = clusterArray;
    var vertexShells: [clusterDomain] atomic int;
    var shellMembers: [0..metrics.coreNumber] set(int, parSafe=true);

    // Calculate shell decomposition
    var (shells, members) = calculateShellDecomposition(analysisCluster);
    
    if logLevel == LogLevel.DEBUG {
        writeln("Shell decomposition complete");
        writeln("Calculating shell metrics");
    }

    // Calculate shell metrics
    metrics = calculateShellMetrics(metrics, analysisCluster, members);

    if logLevel == LogLevel.DEBUG {
        writeln("Calculating core-periphery metrics");
    }

    // Calculate core-periphery metrics
    metrics = calculateCorePeripheryMetrics(metrics, analysisCluster, shells, members);

    if logLevel == LogLevel.DEBUG {
        writeln("Calculating hierarchical metrics");
    }

    // Calculate hierarchical metrics
    metrics = calculateHierarchicalMetrics(metrics, analysisCluster, shells, members);

    if logLevel == LogLevel.DEBUG {
        writeln("Calculating stability metrics");
    }

    // Calculate stability metrics
    metrics = calculateStabilityMetrics(metrics, analysisCluster, shells, members);

    if logLevel == LogLevel.DEBUG {
        writeln("Calculating quality metrics");
    }

    // Calculate quality metrics
    metrics = calculateQualityMetrics(metrics, analysisCluster, members);

    if logLevel == LogLevel.DEBUG {
        writeln("\nAdvanced Core Analysis Results:");
        writeln("Basic Metrics:");
        writeln("  Core Number: ", metrics.coreNumber);
        writeln("  Core Size: ", metrics.coreSize);
        writeln("  Core Density: ", metrics.coreDensity);
        
        writeln("\nCore-Periphery Metrics:");
        writeln("  Core-Periphery Score: ", metrics.corePeripheryScore);
        writeln("  Core Strength: ", metrics.coreStrength);
        writeln("  Periphery Size: ", metrics.peripherySize);
        
        writeln("\nHierarchical Metrics:");
        writeln("  Core Hierarchy Depth: ", metrics.coreHierarchyDepth);
        writeln("  Core-Degree Correlation: ", metrics.coreDegreeCorrelation);
        writeln("  Hierarchy Balance: ", metrics.hierarchyBalance);
        
        writeln("\nStability Metrics:");
        writeln("  Core Stability: ", metrics.coreStability);
        writeln("  Average Persistence: ", (+ reduce metrics.corePersistence) / (min(11, metrics.coreNumber + 1)));
        writeln("  Average Overlap: ", (+ reduce metrics.coreOverlap) / (min(11, metrics.coreNumber + 1)));
        
        writeln("\nQuality Metrics:");
        writeln("  Core Cohesion: ", metrics.coreCohesion);
        writeln("  Core Separation: ", metrics.coreSeparation);
        writeln("  Core Compactness: ", metrics.coreCompactness);
        
        writeln("\nShell Metrics:");
        writeln("  Number of Shells: ", metrics.coreNumber + 1);
        writeln("  Shell Distribution: ", metrics.shellDecomposition);
        writeln("==== Advanced Core Analysis Complete ====\n");
    }

    return metrics;
}
/* 
    Shell Decomposition Definition:

    A k-shell is the set of vertices that belong to the k-core but NOT to the (k+1)-core
    In other words, it's the set of vertices that get removed during the k+1 iteration of 
    the k-core decomposition process.
 */
/* Helper function for shell decomposition */
proc calculateShellDecomposition(ref cluster: set(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Shell Decomposition ====");
        writeln("Initial cluster size: ", cluster.size);
        writeln("\nInitial graph structure:");
        for v in cluster {
            writeln("Vertex ", v, " neighbors: ", neighborsSetGraphG1[v] & cluster);
        }
    }

    // Convert cluster to array and create proper domain
    var clusterArray = cluster.toArray();
    var clusterDomain: domain(int, parSafe=true) = clusterArray;
    var vertexShells: [clusterDomain] atomic int;
    var degrees: [clusterDomain] atomic int;
    
    // Initialize degrees and shells
    forall v in clusterDomain with (ref cluster){
        degrees[v].write(calculateClusterDegree(cluster, v));
        vertexShells[v].write(-1);  // -1 indicates unprocessed
    }
    
    var maxDegree = max reduce [v in clusterDomain] degrees[v].read();
    var shellMembers: [1..maxDegree+1] set(int, parSafe=true);  // 1-based shell numbering
    var remainingVertices: set(int) = cluster;
    
    if logLevel == LogLevel.DEBUG {
        writeln("\nInitial degrees:");
        for v in clusterDomain {
            writeln("Vertex ", v, ": ", degrees[v].read());
        }
        writeln("\nMaximum degree: ", maxDegree);
        writeln("Starting shell identification");
    }

    // Shell decomposition
    var k = 1;  // Start with shell 1
    while remainingVertices.size > 0 {
        var currentShell: set(int, parSafe=true);
        var processedInIteration: bool;
        
        do {
            processedInIteration = false;
            var toProcess: set(int, parSafe=true);
            
            // Find vertices with minimum degree k
            forall v in remainingVertices with (ref toProcess) {
                if degrees[v].read() <= k {
                    toProcess.add(v);
                }
            }
            
            if toProcess.size > 0 {
                processedInIteration = true;
                
                // Process identified vertices
                forall v in toProcess with (ref currentShell, ref remainingVertices) {
                    currentShell.add(v);
                    vertexShells[v].write(k);
                    remainingVertices.remove(v);
                    
                    // Update neighbor degrees
                    var neighbors = neighborsSetGraphG1[v] & remainingVertices;
                    for u in neighbors {
                        degrees[u].sub(1);
                    }
                }
                
                if logLevel == LogLevel.DEBUG {
                    writeln("  Processed vertices in iteration for k=", k, ": ", toProcess);
                }
            }
        } while processedInIteration;

        if currentShell.size > 0 {
            shellMembers[k] = currentShell;
            if logLevel == LogLevel.DEBUG {
                writeln("\nShell ", k, ":");
                writeln("  Vertices: ", currentShell);
                writeln("  Size: ", currentShell.size);
            }
            k += 1;
        } else {
            k += 1;
            if k > maxDegree + 1 then break;
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nFinal Shell Decomposition:");
        for i in 1..k-1 {
            if shellMembers[i].size > 0 {
                writeln("Shell ", i, ":");
                writeln("  Vertices: ", shellMembers[i]);
                writeln("  Size: ", shellMembers[i].size);
                writeln("  Internal edges: ", + reduce [v in shellMembers[i]] 
                    (neighborsSetGraphG1[v] & shellMembers[i]).size / 2);
            }
        }
        
        writeln("\nVertex shell assignments:");
        for v in clusterDomain {
            writeln("Vertex ", v, ": shell ", vertexShells[v].read());
        }
        
        writeln("\nShell Decomposition Complete");
        writeln("Total shells found: ", k-1);
        writeln("==== Shell Decomposition Complete ====\n");
    }

    return (vertexShells, shellMembers);
}

/* Core-Periphery metrics calculation */
proc calculateCorePeripheryMetrics(ref metrics: coreMetrics, 
                                 ref cluster: set(int, parSafe=false),
                                 in vertexShells: [] atomic int,
                                 in shellMembers: [] set(int, parSafe=true)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Core-Periphery Analysis ====");
        writeln("Cluster size: ", cluster.size);
    }

    var analysisCluster = cluster;
    if cluster.size > 100000 {
        const sampleSize = if cluster.size <= 500000 then (cluster.size * 0.1): int     
                     else if cluster.size <= 1000000 then (cluster.size * 0.05): int   
                     else (cluster.size * 0.01): int;                                  
        analysisCluster = sampleClusterVertices(cluster, sampleSize);
    }

    var updatedMetrics = metrics;
    var maxShell = metrics.coreNumber;
    
    // Get core vertices
    var coreVertices = shellMembers[maxShell];
    
    if logLevel == LogLevel.DEBUG {
        writeln("Core size: ", coreVertices.size);
        writeln("Computing edge distributions");
    }

    // Count different types of edges in parallel
    var internalEdges: atomic int;
    var externalEdges: atomic int;
    var crossEdges: atomic int;
    
    forall v in analysisCluster {
        var neighbors = neighborsSetGraphG1[v] & analysisCluster;
        var vShell = vertexShells[v].read();
        
        for u in neighbors {
            var uShell = vertexShells[u].read();
            if vShell == maxShell && uShell == maxShell {
                internalEdges.add(1);
            } else if vShell != maxShell && uShell != maxShell {
                externalEdges.add(1);
            } else {
                crossEdges.add(1);
            }
        }
    }

    // Adjust for double counting in undirected graph
    var finalInternalEdges = internalEdges.read() / 2;
    var finalExternalEdges = externalEdges.read() / 2;
    var finalCrossEdges = crossEdges.read();
    
    // Calculate metrics
    updatedMetrics.coreStrength = if (finalInternalEdges + finalCrossEdges) > 0 then
                                 finalInternalEdges:real / (finalInternalEdges + finalCrossEdges):real
                                 else 0.0;
    
    updatedMetrics.peripherySize = analysisCluster.size - coreVertices.size;

    if logLevel == LogLevel.DEBUG {
        writeln("\nCore-Periphery Results:");
        writeln("  Internal Edges: ", finalInternalEdges);
        writeln("  External Edges: ", finalExternalEdges);
        writeln("  Cross Edges: ", finalCrossEdges);
        writeln("  Core Strength: ", updatedMetrics.coreStrength);
        writeln("  Periphery Size: ", updatedMetrics.peripherySize);
        writeln("==== Core-Periphery Analysis Complete ====\n");
    }

    return updatedMetrics;
}
/* Calculate comprehensive shell metrics with parallel processing and sampling */
proc calculateShellMetrics(in metrics: coreMetrics,
                         ref cluster: set(int, parSafe=false),  // Specify parSafe
                         ref shellMembers: [] set(int, parSafe=true)) throws {  
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Shell Metrics Calculation ====");
        writeln("Cluster size: ", cluster.size);
        writeln("Number of shells: ", metrics.coreNumber + 1);
    }

    var updatedMetrics = metrics;
    
    // Handle sampling for large clusters
    var analysisCluster = cluster;
    if cluster.size > 100000 {
        const sampleSize = if cluster.size <= 500000 then (cluster.size * 0.1): int
                     else if cluster.size <= 1000000 then (cluster.size * 0.05): int
                     else (cluster.size * 0.01): int;

        if logLevel == LogLevel.DEBUG {
            writeln("Large cluster detected, using sampling");
            writeln("Sample size: ", sampleSize);
        }
        analysisCluster = sampleClusterVertices(cluster, sampleSize);
    }

    // Arrays for parallel computation
    var shellDensities: [0..metrics.coreNumber] atomic real;
    var shellConnectivity: [0..metrics.coreNumber] atomic real;
    var shellSizes: [0..metrics.coreNumber] atomic int;

    if logLevel == LogLevel.DEBUG {
        writeln("Starting parallel shell analysis");
    }

    // Calculate shell metrics in parallel
    forall i in 0..metrics.coreNumber with (ref shellMembers) {
        var currentShell = shellMembers[i];
        shellSizes[i].write(currentShell.size);

        if logLevel == LogLevel.DEBUG {
            writeln("Processing shell ", i, " with size ", currentShell.size);
        }

        // Calculate shell density if shell has more than one vertex
        if currentShell.size > 1 {
            var internalEdges: atomic int;
            
            // Count internal edges in parallel
            forall v in currentShell with (ref internalEdges) {
                var neighbors = neighborsSetGraphG1[v] & currentShell;
                internalEdges.add(neighbors.size);
            }
            
            var maxPossibleEdges = (currentShell.size * (currentShell.size - 1));
            var density = if maxPossibleEdges > 0 then 
                         (internalEdges.read() : real) / maxPossibleEdges
                         else 0.0;
            
            shellDensities[i].write(density);

            if logLevel == LogLevel.DEBUG {
                writeln("Shell ", i, " density: ", density);
            }

            // Calculate connectivity to next shell if it exists
            if i < metrics.coreNumber {
                var nextShell = shellMembers[i+1];
                var crossEdges: atomic int;
                
                // Count cross edges in parallel
                forall v in currentShell with (ref crossEdges) {
                    var nextShellNeighbors = neighborsSetGraphG1[v] & nextShell;
                    crossEdges.add(nextShellNeighbors.size);
                }

                var maxPossibleCross = currentShell.size * nextShell.size;
                var connectivity = if maxPossibleCross > 0 then
                                 (crossEdges.read() : real) / maxPossibleCross
                                 else 0.0;
                
                shellConnectivity[i].write(connectivity);

                if logLevel == LogLevel.DEBUG {
                    writeln("Shell ", i, " to ", i+1, " connectivity: ", connectivity);
                }
            }
        }
    }

    // Update metrics with computed values
    forall i in 0..min(10, metrics.coreNumber) with(ref updatedMetrics){
        updatedMetrics.shellDensities[i] = shellDensities[i].read();
        updatedMetrics.shellConnectivity[i] = shellConnectivity[i].read();
        updatedMetrics.shellDecomposition[i] = shellSizes[i].read();
    }

    // Calculate additional shell statistics
    var totalShellSize: atomic int;
    var nonEmptyShells: atomic int;
    
    forall i in 0..metrics.coreNumber with (ref totalShellSize, ref nonEmptyShells) {
        if shellSizes[i].read() > 0 {
            totalShellSize.add(shellSizes[i].read());
            nonEmptyShells.add(1);
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nShell Analysis Results:");
        writeln("Total vertices in shells: ", totalShellSize.read());
        writeln("Number of non-empty shells: ", nonEmptyShells.read());
        writeln("Shell density range: ", 
               min reduce [i in 0..metrics.coreNumber] shellDensities[i].read(), " to ",
               max reduce [i in 0..metrics.coreNumber] shellDensities[i].read());
        writeln("==== Shell Metrics Calculation Complete ====\n");
    }

    return updatedMetrics;
}
/* Calculate hierarchical metrics with parallel processing and sampling */
proc calculateHierarchicalMetrics(ref metrics: coreMetrics,
                                ref cluster: set(int, parSafe=false),
                                vertexShells: [] atomic int,
                                shellMembers: [] set(int, parSafe=true)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Hierarchical Metrics Calculation ====");
        writeln("Cluster size: ", cluster.size);
        writeln("Number of shells: ", metrics.coreNumber + 1);
    }

    var updatedMetrics = metrics;
    
    // Handle sampling for large clusters
    var analysisCluster = cluster;
    if cluster.size > 100000 {
        const sampleSize = if cluster.size <= 500000 then (cluster.size * 0.1): int
                     else if cluster.size <= 1000000 then (cluster.size * 0.05): int
                     else (cluster.size * 0.01): int;

        if logLevel == LogLevel.DEBUG {
            writeln("Large cluster detected, using sampling");
            writeln("Sample size: ", sampleSize);
        }
        analysisCluster = sampleClusterVertices(cluster, sampleSize);
    }

    // Calculate hierarchy depth (number of non-empty shells)
    var nonEmptyShells: atomic int;
    forall i in 0..metrics.coreNumber {
        if shellMembers[i].size > 0 {
            nonEmptyShells.add(1);
        }
    }
    updatedMetrics.coreHierarchyDepth = nonEmptyShells.read();

    // Calculate hierarchy balance
    var expectedShellSize = analysisCluster.size: real / (metrics.coreNumber + 1): real;
    var sizeVariance: atomic real;

    if logLevel == LogLevel.DEBUG {
        writeln("Expected shell size: ", expectedShellSize);
        writeln("Calculating shell size variations");
    }

    forall i in 0..metrics.coreNumber with (ref sizeVariance) {
        var sizeDiff = shellMembers[i].size: real - expectedShellSize;
        sizeVariance.add(sizeDiff * sizeDiff);
    }

    // Calculate normalized hierarchy balance
    updatedMetrics.hierarchyBalance = 1.0 - sqrt(sizeVariance.read()) / analysisCluster.size;

    // Calculate core-degree correlation
    if logLevel == LogLevel.DEBUG {
        writeln("Calculating core-degree correlation");
    }

    // Arrays for correlation calculation
    const clusterDomain: domain(int, parSafe=true) = analysisCluster.toArray();
    var sumX: atomic real;  // sum of degrees
    var sumY: atomic real;  // sum of shell numbers
    var sumXY: atomic real; // sum of products
    var sumX2: atomic real; // sum of squared degrees
    var sumY2: atomic real; // sum of squared shell numbers
    var n = analysisCluster.size;

    forall v in analysisCluster with (ref sumX, ref sumY, ref sumXY, ref sumX2, ref sumY2) {
        var degree = (neighborsSetGraphG1[v] & analysisCluster).size: real;
        var shell = vertexShells[v].read(): real;

        sumX.add(degree);
        sumY.add(shell);
        sumXY.add(degree * shell);
        sumX2.add(degree * degree);
        sumY2.add(shell * shell);
    }

    // Calculate correlation coefficient
    var numerator = n * sumXY.read() - sumX.read() * sumY.read();
    var denominatorX = n * sumX2.read() - sumX.read() * sumX.read();
    var denominatorY = n * sumY2.read() - sumY.read() * sumY.read();
    var denominator = sqrt(denominatorX * denominatorY);

    updatedMetrics.coreDegreeCorrelation = if denominator != 0.0 then
                                          numerator / denominator
                                          else 0.0;

    if logLevel == LogLevel.DEBUG {
        writeln("\nHierarchical Analysis Results:");
        writeln("Core Hierarchy Depth: ", updatedMetrics.coreHierarchyDepth);
        writeln("Hierarchy Balance: ", updatedMetrics.hierarchyBalance);
        writeln("Core-Degree Correlation: ", updatedMetrics.coreDegreeCorrelation);
        writeln("==== Hierarchical Metrics Calculation Complete ====\n");
    }

    return updatedMetrics;
}
/* Calculate quality metrics with parallel processing and sampling */
proc calculateQualityMetrics(metrics: coreMetrics,
                           ref cluster: set(int),
                           ref shellMembers: [] set(int, parSafe=true)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Quality Metrics Calculation ====");
        writeln("Cluster size: ", cluster.size);
        writeln("Maximum shell: ", metrics.coreNumber);
    }

    var updatedMetrics = metrics;
    var maxShell = metrics.coreNumber;
    var coreVertices = shellMembers[maxShell];

    // Handle sampling for large clusters
    var analysisCluster = cluster;
    if cluster.size > 100000 {
        const sampleSize = if cluster.size <= 500000 then (cluster.size * 0.1): int
                     else if cluster.size <= 1000000 then (cluster.size * 0.05): int
                     else (cluster.size * 0.01): int;

        if logLevel == LogLevel.DEBUG {
            writeln("Large cluster detected, using sampling");
            writeln("Sample size: ", sampleSize);
        }
        analysisCluster = sampleClusterVertices(cluster, sampleSize);
    }

    // Atomic counters for parallel computation
    var internalEdges: atomic int;
    var externalEdges: atomic int;
    var boundaryVertices: atomic int;

    if logLevel == LogLevel.DEBUG {
        writeln("Starting core cohesion calculation");
        writeln("Core size: ", coreVertices.size);
    }

    // Calculate core cohesion and separation in parallel
    forall v in coreVertices with (ref internalEdges,
                                  ref externalEdges,
                                  ref boundaryVertices) {
        var neighbors = neighborsSetGraphG1[v] & analysisCluster;
        var internalNeighbors = neighbors & coreVertices;
        var externalNeighbors = neighbors - coreVertices;
        
        internalEdges.add(internalNeighbors.size);
        externalEdges.add(externalNeighbors.size);
        
        if externalNeighbors.size > 0 {
            boundaryVertices.add(1);
        }

        if logLevel == LogLevel.DEBUG {
            writeln("Vertex ", v, ": internal=", internalNeighbors.size, 
                   " external=", externalNeighbors.size);
        }
    }

    // Calculate final metrics
    var finalInternalEdges = internalEdges.read() / 2;  // Each edge counted twice
    var finalExternalEdges = externalEdges.read();
    var totalEdges = finalInternalEdges + finalExternalEdges;

    // Calculate core cohesion (internal density)
    var maxPossibleInternalEdges = (coreVertices.size * (coreVertices.size - 1)) / 2;
    updatedMetrics.coreCohesion = if maxPossibleInternalEdges > 0 then
                                 finalInternalEdges:real / maxPossibleInternalEdges:real
                                 else 0.0;

    // Calculate core separation
    updatedMetrics.coreSeparation = if totalEdges > 0 then
                                   finalInternalEdges:real / totalEdges:real
                                   else 0.0;

    // Calculate core compactness
    var boundarySize = boundaryVertices.read();
    var interiorSize = coreVertices.size - boundarySize;
    updatedMetrics.coreCompactness = if coreVertices.size > 0 then
                                    interiorSize:real / coreVertices.size:real
                                    else 0.0;

    if logLevel == LogLevel.DEBUG {
        writeln("\nQuality Metrics Results:");
        writeln("Internal Edges: ", finalInternalEdges);
        writeln("External Edges: ", finalExternalEdges);
        writeln("Boundary Vertices: ", boundarySize);
        writeln("Core Cohesion: ", updatedMetrics.coreCohesion);
        writeln("Core Separation: ", updatedMetrics.coreSeparation);
        writeln("Core Compactness: ", updatedMetrics.coreCompactness);
        writeln("==== Quality Metrics Calculation Complete ====\n");
    }

    return updatedMetrics;
}
/* Calculate stability metrics with parallel processing and sampling */
proc calculateStabilityMetrics(metrics: coreMetrics,
                            ref cluster: set(int),
                            vertexShells: [] atomic int,
                            shellMembers: [] set(int, parSafe=true)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Stability Metrics Calculation ====");
        writeln("Cluster size: ", cluster.size);
        writeln("Maximum shell: ", metrics.coreNumber);
    }

    var updatedMetrics = metrics;
    const trials = 10;
    const maxShell = metrics.coreNumber;

    // Handle sampling for large clusters
    var analysisCluster = cluster;
    if cluster.size > 100000 {
        const sampleSize = if cluster.size <= 500000 then (cluster.size * 0.1): int
                     else if cluster.size <= 1000000 then (cluster.size * 0.05): int
                     else (cluster.size * 0.01): int;

        if logLevel == LogLevel.DEBUG {
            writeln("Large cluster detected, using sampling");
            writeln("Sample size: ", sampleSize);
        }
        analysisCluster = sampleClusterVertices(cluster, sampleSize);
    }

    // Calculate core stability through random vertex removal
    var stabilityScores: [1..trials] atomic real;
    const removalFraction = 0.1; // Remove 10% of vertices
    const removalSize = max(1, (analysisCluster.size * removalFraction): int);

    if logLevel == LogLevel.DEBUG {
        writeln("Starting stability trials");
        writeln("Removal size per trial: ", removalSize);
    }

    // Run stability trials in parallel
    forall t in 1..trials with (ref analysisCluster) {
        var trialCluster: set(int) = analysisCluster;
        var removedVertices = sampleClusterVertices(analysisCluster, removalSize);
        trialCluster -= removedVertices;
        
        var trialMetrics = calculateCoreNumbers(trialCluster);
        stabilityScores[t].write(trialMetrics.coreNumber:real / maxShell:real);

        if logLevel == LogLevel.DEBUG {
            writeln("Trial ", t, " score: ", stabilityScores[t].read());
        }
    }

    // Calculate average stability score
    var totalStability = + reduce [s in stabilityScores] s.read();
    updatedMetrics.coreStability = totalStability / trials;

    if logLevel == LogLevel.DEBUG {
        writeln("\nCalculating core persistence and overlap");
    }

    // Calculate persistence and overlap between consecutive cores
    forall k in 0..min(10, maxShell) with (ref updatedMetrics, ref analysisCluster) {
        var kCore = getKCore(analysisCluster, k, vertexShells);
        var nextKCore = getKCore(analysisCluster, k+1, vertexShells);

        // Calculate persistence (fraction of vertices retained in next core)
        updatedMetrics.corePersistence[k] = if kCore.size > 0 then
                                          nextKCore.size:real / kCore.size:real
                                          else 0.0;

        // Calculate overlap (Jaccard similarity)
        var intersection = kCore & nextKCore;
        var unions = kCore | nextKCore;
        updatedMetrics.coreOverlap[k] = if unions.size > 0 then
                                       intersection.size:real / unions.size:real
                                       else 0.0;

        if logLevel == LogLevel.DEBUG {
            writeln("Shell ", k, ":");
            writeln("  Persistence: ", updatedMetrics.corePersistence[k]);
            writeln("  Overlap: ", updatedMetrics.coreOverlap[k]);
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("\nStability Metrics Results:");
        writeln("Core Stability: ", updatedMetrics.coreStability);
        writeln("Average Persistence: ", 
               (+ reduce updatedMetrics.corePersistence) / (min(11, maxShell + 1)));
        writeln("Average Overlap: ",
               (+ reduce updatedMetrics.coreOverlap) / (min(11, maxShell + 1)));
        writeln("==== Stability Metrics Calculation Complete ====\n");
    }

    return updatedMetrics;
}
/* Extract k-core from shell decomposition */
proc getKCore(in cluster: set(int, parSafe=false), 
              k: int, 
              vertexShells: [] atomic int) {
    var kCore: set(int, parSafe=true);
    forall v in cluster with(ref kCore) {
        if vertexShells[v].read() >= k {
            kCore.add(v);
        }
    }
    return kCore;
}

/* Assortativity calculation */
proc calculateAssortativity(ref cluster: set(int), ref basicStats, in metrics: connectivityMetrics) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Assortativity Calculation ====");
        writeln("Cluster size: ", cluster.size);
    }

    var updatedMetrics = metrics;
    
    // Convert cluster to array and create proper domain
    var clusterArr = cluster.toArray();
    if logLevel == LogLevel.DEBUG {
        writeln("Created cluster array of size: ", clusterArr.size);
    }

    // Create domain based on array indices
    const clusterDomain = {0..#clusterArr.size};
    if logLevel == LogLevel.DEBUG {
        writeln("Created domain with bounds: ", clusterDomain);
    }
    
    // Arrays to store local contributions
    var localNums: [clusterDomain] real;
    var localDen1s: [clusterDomain] real;
    var localDen2s: [clusterDomain] real;

    if logLevel == LogLevel.DEBUG {
        writeln("Initialized arrays for calculations");
        writeln("Starting local contributions calculation");
    }
    
    // Calculate local contributions
    forall i in clusterDomain with (ref localNums, ref localDen1s, ref localDen2s) {
        var v = clusterArr[i];
        var v_deg = basicStats.degrees[v];
        var neighbors = neighborsSetGraphG1[v] & cluster;
        
        var localNum = 0.0;
        var localDen1 = 0.0;
        var localDen2 = 0.0;
        
        for u in neighbors {
            var u_deg = basicStats.degrees[u];
            localNum += v_deg * u_deg;       // Product of degrees for connected nodes
            localDen1 += v_deg * v_deg;      // Square of node degree
            localDen2 += v_deg;              // Sum of node degree
        }
        
        localNums[i] = localNum;
        localDen1s[i] = localDen1;
        localDen2s[i] = localDen2;

        if logLevel == LogLevel.DEBUG && i == 0 {
            writeln("Sample calculation for first vertex:");
            writeln("  Vertex: ", v, " Degree: ", v_deg);
            writeln("  Number of neighbors: ", neighbors.size);
            writeln("  Local contributions: ", localNum, ", ", localDen1, ", ", localDen2);
        }
    }
    
    // Calculate final metrics
    var M = basicStats.n_edges;
    if M > 0 {
        var numerator = + reduce localNums;
        var denominator1 = + reduce localDen1s;
        var denominator2 = + reduce localDen2s;
        
        if logLevel == LogLevel.DEBUG {
            writeln("\nFinal calculations:");
            writeln("Total edges (M): ", M);
            writeln("Numerator sum: ", numerator);
            writeln("Denominator1 sum: ", denominator1);
            writeln("Denominator2 sum: ", denominator2);
        }

        var den2 = (denominator2 / (2 * M)) ** 2;
        // Add check for division by zero
        var denominator = (denominator1/(2*M) - den2);
        if denominator != 0 {
            updatedMetrics.assortativity = (numerator/(2*M) - den2) / denominator;
        } else {
            updatedMetrics.assortativity = 0.0;  // or another appropriate default value
            if logLevel == LogLevel.DEBUG {
                writeln("Warning: Unable to calculate assortativity (division by zero)");
            }
        }
        
        if logLevel == LogLevel.DEBUG {
            writeln("Assortativity coefficient: ", updatedMetrics.assortativity);
            writeln("==== Assortativity Calculation Complete ====\n");
        }
    }
    
    return updatedMetrics;
}

proc calculateViecutMincut(ref cluster: set(int), in metrics: connectivityMetrics) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Viecut Mincut Calculation ====");
        writeln("Cluster size: ", cluster.size);
    }
    
    var updatedMetrics = metrics;

    // Handle empty or singleton clusters
    if cluster.size <= 1 {
        if logLevel == LogLevel.DEBUG {
            writeln("Empty or singleton cluster detected");
        }
        updatedMetrics.ViecutMincut = 0;
        updatedMetrics.ViecutInPartiotionSize = 0;
        updatedMetrics.ViecutOutPartitionSize = 0;
        return updatedMetrics;
    }

    var (src, dst, mapper) = getEdgeList(cluster);

    // If the generated edge list is empty, then return.
    if src.size < 1 {
        if logLevel == LogLevel.DEBUG {
            writeln("Generated edge list is empty");
        }
        updatedMetrics.ViecutMincut = 0;
        updatedMetrics.ViecutInPartiotionSize = 0;
        updatedMetrics.ViecutOutPartitionSize = 0;
        return updatedMetrics;
    }


    var n = mapper.size;
    var m = src.size;

    var partitionArr: [{0..<n}] int;
    var cut = c_computeMinCut(partitionArr, src, dst, n, m);

    if logLevel == LogLevel.DEBUG {
        writeln("cluster passed to Viecut and cut_size is: ", cut);
    }

    var cluster1, cluster2 = new set(int);
        
    // Separate vertices into two partitions.
    for (v,p) in zip(partitionArr.domain, partitionArr) {
        if p == 1 then cluster1.add(mapper[v]);
        else cluster2.add(mapper[v]);
    }

    updatedMetrics.ViecutMincut = cut;
    updatedMetrics.ViecutInPartiotionSize = cluster1.size;
    updatedMetrics.ViecutOutPartitionSize = cluster2.size;

    if logLevel == LogLevel.DEBUG {
        writeln("Viecut Mincut size: ", updatedMetrics.ViecutMincut);
        writeln("In Partiotion size: ", updatedMetrics.ViecutInPartiotionSize);
        writeln("Out Partition size: ", updatedMetrics.ViecutOutPartitionSize);
        writeln("==== Viecut Mincut Calculation Complete ====\n");
    }
    return updatedMetrics;
}

    proc initializeEmptyMetrics() {
    var metrics = new clusterMetricsRecord();
    
    // Initialize connectivity metrics
    metrics.connectivity.minDegree = 0;
    metrics.connectivity.maxDegree = 0;
    metrics.connectivity.avgDegree = 0.0;
    metrics.connectivity.totalInternalEdges = 0;
    metrics.connectivity.edgeConnectivityLowerBound = 0;
    metrics.connectivity.degreeVariance = 0.0;
    metrics.connectivity.degreeSkewness = 0.0;
    metrics.connectivity.assortativity = 0.0;
    metrics.connectivity.effectiveDiameter = 0.0;
    metrics.connectivity.avgBetweenness = 0.0;
    metrics.connectivity.maxBetweenness = 0.0;

    // Initialize density metrics
    metrics.density.density = 0.0;
    metrics.density.sparsity = 1.0;
    // metrics.density.internalEdges = 0;
    metrics.density.maxPossibleEdges = 0;
    metrics.density.triangleCount = 0;
    metrics.density.globalClusteringCoeff = 0.0;
    metrics.density.avgLocalClusteringCoeff = 0.0;
    metrics.density.edgeDensityDistribution = 0.0;
    metrics.density.localDensityVariance = 0.0;
    metrics.density.densityCorrelation = 0.0;

    // Initialize spectral metrics
    metrics.spectral.lambda2Lower = 0.0;
    metrics.spectral.lambda2Upper = 0.0;
    metrics.spectral.lambda2Estimate = 0.0;
    metrics.spectral.conductance = 0.0;
    
    // Initialize diameter metrics
    metrics.connectivity.diameter = 0;
    metrics.connectivity.diameterLowerBound = 0;
    metrics.connectivity.diameterUpperBound = 0;
    metrics.connectivity.exactDiameter = true;
    
    return metrics;
}


proc printClusterAnalysis(metrics: clusterMetricsRecord, clusterSize: int) {
    writeln("\n========== Cluster Analysis Report ==========");
    writeln("Cluster Size: ", clusterSize, " vertices");
    
    writeln("\n----- Connectivity Metrics -----");
    writeln("Basic Connectivity:");
    writeln("  Number of vertices: ", metrics.connectivity.n_vertices);
    writeln("  Number of Edges: ", metrics.connectivity.totalInternalEdges);

    writeln("  Minimum Degree: ", metrics.connectivity.minDegree);
    writeln("  Maximum Degree: ", metrics.connectivity.maxDegree);
    writeln("  Average Degree: ", metrics.connectivity.avgDegree);
    writeln("  Edge Connectivity Lower Bound: ", metrics.connectivity.edgeConnectivityLowerBound, " Mader's theorem bound");
    writeln("  Cluster Volume: ", metrics.connectivity.clusterVolume);
    writeln("  Cluster CutEdges: ", metrics.connectivity.clusterCutEdges);

    writeln("\nDegree Distribution:");
    writeln("  Degree Variance: ", metrics.connectivity.degreeVariance);
    writeln("  Degree Skewness: ", metrics.connectivity.degreeSkewness);
    writeln("  Degree Second Moment: ", metrics.connectivity.degreeSecondMoment);
    writeln("  Assortativity: ", metrics.connectivity.assortativity);

    writeln("\n----- Density Metrics -----");
    writeln("Basic Density:");
    writeln("  Density: ", metrics.density.density);
    writeln("  Sparsity: ", metrics.density.sparsity);
    writeln("  Maximum Possible Edges: ", metrics.density.maxPossibleEdges);

    writeln("\nClustering Metrics:");
    writeln("  Triangle Count: ", metrics.density.triangleCount);
    writeln("  Global Clustering Coefficient: ", metrics.density.globalClusteringCoeff);
    writeln("  Average Local Clustering Coefficient: ", metrics.density.avgLocalClusteringCoeff);

    writeln("\n----- Spectral Metrics -----");
    writeln("  Conductance: ", metrics.spectral.conductance);
    writeln("  λ2 Lower Bound: ", metrics.spectral.lambda2Lower);
    writeln("  λ2 Upper Bound: ", metrics.spectral.lambda2Upper);
    writeln("  λ2 Estimate: ", metrics.spectral.lambda2Estimate);
    
    writeln("\n----- Transitivity Metrics -----");
    writeln("  Wedge Count: ", metrics.transitivity.wedgeCount);
    writeln("  Triangle-to-Wedge Ratio: ", metrics.transitivity.triangleToWedgeRatio);
    writeln("  Global Transitivity: ", metrics.transitivity.globalTransitivity);

    writeln("\n----- Triangle Distribution Metrics -----");
    writeln("  Triangle Density: ", metrics.density.triangleDensity);
    writeln("  Participation Rate: ", metrics.density.participationRate);
    writeln("  Max Local Triangles: ", metrics.density.maxLocalTriangles);
    writeln("  Average Triangles Per Vertex: ", metrics.density.avgTrianglesPerVertex);

    // writeln("\n----- Path-based Metrics -----");
    // writeln("  Local/Global Transitivity Ratio: ", metrics.paths.localGlobalRatio);
    // writeln("  Cohesion Score: ", metrics.paths.cohesionScore);
    // writeln("  Path Distribution: ");
    // writeln("HERE ", metrics.paths.pathDistribution);
    // for i in metrics.paths.pathDistribution.domain {
    //     writeln("    Length ", i, ": ", metrics.paths.pathDistribution[i]);
    // }

    writeln("\n----- Diameter and Eccentricity Metrics -----");
    writeln("  Diameter: ", metrics.connectivity.diameter);
    if !metrics.connectivity.exactDiameter {
        writeln("  Lower Bound: ", metrics.connectivity.diameterLowerBound);
        writeln("  Upper Bound: ", metrics.connectivity.diameterUpperBound);
        writeln("  (Approximated using sampling)");
    } else {
        writeln("  (Exact calculation)");
    }
    writeln("  Radius: ", metrics.eccentricity.radius);
    writeln("  Number of Center Vertices: ", metrics.eccentricity.centerVertices.size);
    if metrics.eccentricity.centerVertices.size <= 20 {
        writeln("  Center Vertices: ", metrics.eccentricity.centerVertices);
    }
    writeln("  Number of Peripheral Vertices: ", metrics.eccentricity.peripheralVertices.size);
    if metrics.eccentricity.peripheralVertices.size <= 20 {
        writeln("  Peripheral Vertices: ", metrics.eccentricity.peripheralVertices);
    }
    writeln("  Average Eccentricity: ", metrics.eccentricity.avgEccentricity);

    writeln("\n----- Distribution Statistics -----");
    writeln("Degree Distribution:");
    writeln("  Mean: ", metrics.degreeDistribution.mean);
    writeln("  Median: ", metrics.degreeDistribution.median);
    writeln("  Standard Deviation: ", metrics.degreeDistribution.standardDev);
    writeln("  Skewness: ", metrics.degreeDistribution.skewness);
    writeln("  Kurtosis: ", metrics.degreeDistribution.kurtosis);
    writeln("  Key Percentiles:");
    writeln("    25th: ", metrics.degreeDistribution.percentiles[25]);
    writeln("    50th: ", metrics.degreeDistribution.percentiles[50]);
    writeln("    75th: ", metrics.degreeDistribution.percentiles[75]);
    writeln("    90th: ", metrics.degreeDistribution.percentiles[90]);
    
    writeln("\nTriangle Distribution:");
    writeln("  Mean: ", metrics.triangleDistribution.mean);
    writeln("  Median: ", metrics.triangleDistribution.median);
    writeln("  Standard Deviation: ", metrics.triangleDistribution.standardDev);
    writeln("  Skewness: ", metrics.triangleDistribution.skewness);
    writeln("  Kurtosis: ", metrics.triangleDistribution.kurtosis);
    writeln("  Key Percentiles:");
    writeln("    25th: ", metrics.triangleDistribution.percentiles[25]);
    writeln("    50th: ", metrics.triangleDistribution.percentiles[50]);
    writeln("    75th: ", metrics.triangleDistribution.percentiles[75]);
    writeln("    90th: ", metrics.triangleDistribution.percentiles[90]);
    
    // writeln("\nPath Length Distribution:");
    // writeln("  Mean: ", metrics.pathDistribution.mean);
    // writeln("  Median: ", metrics.pathDistribution.median);
    // writeln("  Standard Deviation: ", metrics.pathDistribution.standardDev);
    // writeln("  Skewness: ", metrics.pathDistribution.skewness);
    // writeln("  Kurtosis: ", metrics.pathDistribution.kurtosis);
    // writeln("  Key Percentiles:");
    // writeln("    25th: ", metrics.pathDistribution.percentiles[25]);
    // writeln("    50th: ", metrics.pathDistribution.percentiles[50]);
    // writeln("    75th: ", metrics.pathDistribution.percentiles[75]);
    // writeln("    90th: ", metrics.pathDistribution.percentiles[90]);
    writeln("\n----- MinCut Metrics (Viecut cactus)-----");
    writeln("  Cut size: ", metrics.connectivity.ViecutMincut);
    writeln("  In Partiotion size: ", metrics.connectivity.ViecutInPartiotionSize);
    writeln("  Out Partition size: ", metrics.connectivity.ViecutOutPartitionSize);

    writeln("\n----- Core Decomposition Metrics -----");
    writeln("Basic Core Structure:");
    writeln("  Core Number: ", metrics.core.coreNumber);
    writeln("  Core Size: ", metrics.core.coreSize);
    writeln("  Core Density: ", metrics.core.coreDensity);
    writeln("  Maximum Core Size: ", metrics.core.maxCoreSize);

    writeln("\nCore-Periphery Structure:");
    writeln("  Core-Periphery Score: ", metrics.core.corePeripheryScore);
    writeln("  Core Strength: ", metrics.core.coreStrength);
    writeln("  Periphery Size: ", metrics.core.peripherySize);

    writeln("\nHierarchical Structure:");
    writeln("  Core Hierarchy Depth: ", metrics.core.coreHierarchyDepth);
    writeln("  Core-Degree Correlation: ", metrics.core.coreDegreeCorrelation);
    writeln("  Hierarchy Balance: ", metrics.core.hierarchyBalance);

    writeln("\nCore Quality Metrics:");
    writeln("  Core Cohesion: ", metrics.core.coreCohesion);
    writeln("  Core Separation: ", metrics.core.coreSeparation);
    writeln("  Core Compactness: ", metrics.core.coreCompactness);

    writeln("\nCore Stability Metrics:");
    writeln("  Core Stability: ", metrics.core.coreStability);
    writeln("  Core Persistence:");
    for i in 0..#min(metrics.core.coreNumber + 1, 11) {
        if metrics.core.corePersistence[i] > 0.0 {
            writeln("    Shell ", i, ": ", metrics.core.corePersistence[i]);
        }
    }
    writeln("  Core Overlap:");
    for i in 0..#min(metrics.core.coreNumber + 1, 11) {
        if metrics.core.coreOverlap[i] > 0.0 {
            writeln("    Shell ", i, ": ", metrics.core.coreOverlap[i]);
        }
    }

    writeln("\nShell Structure:");
    for i in 0..#min(metrics.core.coreNumber + 1, 11) {
        if metrics.core.shellDecomposition[i] > 0 {
            writeln("  Shell ", i, ":");
            writeln("    Size: ", metrics.core.shellDecomposition[i]);
            writeln("    Density: ", metrics.core.shellDensities[i]);
            if i < metrics.core.coreNumber {
                writeln("    Connectivity to next shell: ", metrics.core.shellConnectivity[i]);
            }
        }
    }

    // Add summary statistics
    writeln("\nCore Structure Summary:");
    writeln("  Average Shell Density: ", 
            (+ reduce metrics.core.shellDensities[0..#min(metrics.core.coreNumber + 1, 11)]) / 
            (metrics.core.coreNumber + 1));
    writeln("  Average Core Persistence: ", 
            (+ reduce metrics.core.corePersistence[0..#min(metrics.core.coreNumber + 1, 11)]) / 
            (metrics.core.coreNumber + 1));
    writeln("  Average Shell Connectivity: ", 
            (+ reduce metrics.core.shellConnectivity[0..#min(metrics.core.coreNumber, 11)]) / 
            metrics.core.coreNumber);

    writeln("\n===========================================");
}
/* Configuration record for controlling metric calculations */
record MetricsConfig {
    // Basic Metrics - usually fast to compute
    var computeBasicConnectivity: bool = true;     // Degrees, edges, basic network structure
    var computeDensity: bool = true;               // Basic density metrics
    
    // Advanced Metrics - more computationally intensive
    var computeTriangles: bool = false;            // Triangle-based metrics including:
                                                  // - Local/global clustering coefficients
                                                  // - Triangle counts and distribution
                                                  // - Triangle density
    
    var computeTransitivity: bool = false;         // Transitivity metrics
    var computeSpectral: bool = false;             // Spectral metrics and conductance
    var computeDiameter: bool = false;             // Diameter and eccentricity
    
    // Distribution Statistics
    var computeDegreeDistribution: bool = false;   // Distribution of vertex degrees
    var computeTriangleDistribution: bool = false; // Distribution of triangle participation
    
    var computeTriangleCentrality: bool = false;   // Triangle-based centrality metrics

    // Core Metrics
    var computeCoreMetrics: bool = false;  // k-core decomposition
    // var computePathDistribution: bool = false;

    /* Validate configuration and dependencies */
    proc validate() {
        // Triangle distribution needs triangle computation
        if this.computeTriangleDistribution && !this.computeTriangles {
            this.computeTriangles = true;
        }
        
        // Triangle centrality needs triangle computation
        if this.computeTriangleCentrality && !this.computeTriangles {
            this.computeTriangles = true;
        }
    }
    /* Create preset configurations */
    proc getBasicConfig() {
        // var configs = new MetricsConfig();
        // Only enable basic metrics, everything else false
        this.computeBasicConnectivity = true;
        this.computeDensity = true;
        return;
    }
    
    /* Create preset configurations */
    proc getCoreMetrics() {
        // var configs = new MetricsConfig();
        // Only enable core metrics, everything else false
        this.computeCoreMetrics = true;
        return;
    }

    proc getAllMetrics() {
        //var configs = new MetricsConfig();
        // Enable all metrics
        this.computeBasicConnectivity = true;
        this.computeDensity = true;
        this.computeTriangles = true;
        this.computeTransitivity = true;
        this.computeSpectral = true;
        this.computeDiameter = true;
        this.computeDegreeDistribution = true;
        this.computeTriangleDistribution = true;
        this.computeCoreMetrics = true;
        // this.computePathDistribution = true;
        return;
    }
}
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////


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

      //forall key in newClusters.keysToArray() with (ref newClusters) {
      for key in newClusters.keysToArray() {
        ref clusterToAdd = newClusters[key];
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Processing cluster " + key:string + " which is a subcluster of " 
                    + newClusterIdToOriginalClusterId[key]:string + ".";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        // if key == 1 then 
        var conf = new MetricsConfig();
        // conf.computeBasicConnectivity=true;
        // conf.computeTriangleDistribution=true;
        // conf.getAllMetrics();
        conf.getCoreMetrics();
        analyzeCluster(clusterToAdd, key, conf);
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