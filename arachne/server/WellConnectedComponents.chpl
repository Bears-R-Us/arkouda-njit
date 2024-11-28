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
/* Triangle distribution metrics */
record triangleDistMetrics {
    var triangleDensity: real;           // triangles/possible triangles
    var participationRate: real;         // % of vertices in triangles
    var maxLocalTriangles: int;          // max triangles for any vertex
    var avgTrianglesPerVertex: real;     // average triangles per vertex
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
}
record densityMetrics {
    // Basic density
    var density: real;
    var sparsity: real;
    // var internalEdges: int;
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
    
    // Add new metric records
    var triangleDist: triangleDistMetrics;
    var paths: pathMetrics;
    var eccentricity: eccentricityMetrics;
    
    // Add statistical distributions
    var degreeDistribution: distributionStats;
    var triangleDistribution: distributionStats;
    var pathDistribution: distributionStats;
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

/* Wrapper for analyzing cluster with ID */
proc analyzeCluster(ref cluster: set(int), clusterId: int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\nAnalyzing cluster ", clusterId, " (Original cluster: ", 
                newClusterIdToOriginalClusterId[clusterId], ")");
        writeln("Cluster vertices:", cluster); 

    }
    return analyzeCluster(cluster);
}

/* Main analysis function for cluster metrics */
proc analyzeCluster(ref cluster: set(int)) throws {
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
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Basic Connectivity Metrics -----");
        }
        metrics.connectivity = calculateBasicConnectivity(cluster);
        
        // Advanced connectivity metrics (including assortativity)
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Advanced Connectivity Metrics -----");
        }
        var advancedMetrics = calculateAdvancedConnectivity(cluster);
        
        // Update connectivity metrics with advanced calculations
        metrics.connectivity.assortativity = advancedMetrics.assortativity;
        metrics.connectivity.effectiveDiameter = advancedMetrics.effectiveDiameter;
        metrics.connectivity.avgBetweenness = advancedMetrics.avgBetweenness;
        metrics.connectivity.maxBetweenness = advancedMetrics.maxBetweenness;

        // Calculate density and clustering metrics
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Density and Clustering Metrics -----");
        }
        var n = cluster.size;
        metrics.density.maxPossibleEdges = (n * (n-1)) / 2;
        metrics.density.density = if metrics.density.maxPossibleEdges > 0 
            then metrics.connectivity.totalInternalEdges:real / metrics.density.maxPossibleEdges:real
            else 0.0;
        metrics.density.sparsity = 1.0 - metrics.density.density;
        // metrics.density.internalEdges = metrics.connectivity.totalInternalEdges;

        // Add clustering coefficient calculation
        metrics.density = calculateClusteringCoefficients(cluster, metrics.density);
        
        // Calculate spectral bounds based on conductance
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Spectral Metrics -----");
        }
        var (conductance, volumeCluster, outEdges)  = calculateConductance(cluster);

        metrics.connectivity.clusterVolume = volumeCluster;
        metrics.connectivity.clusterCutEdges = outEdges;
        
        metrics.spectral = calculateSpectralBounds(conductance);
        metrics.spectral.conductance = conductance;

        // Calculate triangle centrality 
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Triangle Centrality -----");
        }
        var tcMetrics = calculateTriangleCentrality(cluster);
        metrics.connectivity.triangleCentrality = tcMetrics.triangleCentralities;

        if logLevel == LogLevel.DEBUG {
          writeln("\n----- Computing Transitivity Metrics -----");
        }
        metrics.transitivity = calculateTransitivityMetrics(cluster);

       // Calculate diameter after basic connectivity metrics
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Diameter Metrics -----");
        }
        var diameterMetrics = calculateDiameter(cluster);
        
        // Update connectivity metrics with diameter results
        metrics.connectivity.diameter = diameterMetrics.estimatedDiameter;
        metrics.connectivity.diameterLowerBound = diameterMetrics.lowerBound;
        metrics.connectivity.diameterUpperBound = diameterMetrics.upperBound;
        metrics.connectivity.exactDiameter = diameterMetrics.exactDiameter;

        // Calculate triangle distribution metrics
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Triangle Distribution Metrics -----");
        }
        metrics.triangleDist = calculateTriangleDistribution(cluster, metrics.density.triangleCount);

        // Calculate path metrics
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Path Metrics -----");
        }
        metrics.paths = calculatePathMetrics(cluster, 
                                   metrics.transitivity.globalTransitivity,
                                   metrics.density.avgLocalClusteringCoeff,
                                   metrics.density.density);  // rememebr to Pass existing density

        // Calculate eccentricity metrics once diameter is fixed?!
        // Wait until we have diameter calculation
        if metrics.connectivity.diameter > 0 {
            if logLevel == LogLevel.DEBUG {
                writeln("\n----- Computing Eccentricity Metrics -----");
            }
            metrics.eccentricity = calculateEccentricityMetrics(cluster, metrics.connectivity.diameter);
        }
        // Calculate statistical distributions
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Distribution Statistics -----");
        }
        
        // Get degree distribution
        var degrees = [v in cluster] (neighborsSetGraphG1[v] & cluster).size: real;
        metrics.degreeDistribution = calculateDistributionStats(degrees);
        
        // Get triangle distribution
        var trianglesPerVertex = [v in cluster] countLocalTriangles(v, neighborsSetGraphG1[v] & cluster): real;
        metrics.triangleDistribution = calculateDistributionStats(trianglesPerVertex);
        
        // Get path length distribution (from BFS results)
        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Computing Path Length Distribution -----");
        }
        var pathLengths = getPathLengths(cluster);
        metrics.pathDistribution = calculateDistributionStats(pathLengths);

        if logLevel == LogLevel.DEBUG {
            writeln("\n----- Analysis Complete -----");
        }

    } catch e {
        writeln("Error in analyzeCluster: ", e.message());
        metrics = initializeEmptyMetrics();
    }

    // Print final analysis
    //if logLevel == LogLevel.DEBUG {
        printClusterAnalysis(metrics, cluster.size);
    //}
    
    return metrics;
}

/* Get path lengths distribution in the cluster */
proc getPathLengths(ref cluster: set(int)) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Getting Path Lengths Distribution ====");
        writeln("Cluster size: ", cluster.size);
    }

    // Convert cluster to array and create proper domain
    var clusterArray = cluster.toArray();
    var clusterDomain: domain(int, parSafe=true) = clusterArray;
    
    // Create array to store all path lengths
    var pathLengths: list(real, parSafe=true);

    // Sample vertices for large clusters
    var verticesToProcess = cluster;
    if cluster.size > 10000 {
        const sampleSize = if cluster.size <= 50000 then (cluster.size * 0.2): int
                     else if cluster.size <= 100000 then (cluster.size * 0.1): int
                     else (cluster.size * 0.05): int;
        
        if logLevel == LogLevel.DEBUG {
            writeln("Large cluster, using sampling");
            writeln("Sample size: ", sampleSize);
        }
        verticesToProcess = sampleClusterVertices(cluster, sampleSize);
    }

    // Run BFS from each vertex and collect path lengths
    forall v in verticesToProcess with(ref cluster, ref pathLengths) {
        var (_, depths) = enhancedBFS(v, cluster);
        for u in cluster {
            if depths[u] != -1 {  // Only include reachable vertices
                pathLengths.pushBack(depths[u]: real);
            }
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Collected ", pathLengths.size, " path lengths");
        writeln("==== Path Lengths Collection Complete ====\n");
    }

    return pathLengths.toArray();
}


/* Calculate distribution statistics */
proc calculateDistributionStats(ref data: [] real) {
    var stats = new distributionStats();
    
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Calculating Distribution Statistics ====");
        writeln("Sample size: ", data.size);
    }

    // Calculate mean
    stats.mean = + reduce data / data.size;
    
    // Calculate median and percentiles
    var sortedData = data;
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
    stats.standardDev = sqrt(variance / (data.size - 1));
    
    // Calculate higher moments (skewness and kurtosis)
    var m3 = 0.0, m4 = 0.0;
    forall x in data with (+ reduce m3, + reduce m4) {
        var diff = x - stats.mean;
        var diff2 = diff * diff;
        m3 += diff * diff2;
        m4 += diff2 * diff2;
    }
    
    stats.skewness = m3 / (data.size * stats.standardDev ** 3);
    stats.kurtosis = m4 / (data.size * stats.standardDev ** 4) - 3.0;
    
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

/* Calculate triangle distribution metrics */
proc calculateTriangleDistribution(ref cluster: set(int), triangleCount: int) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Triangle Distribution Analysis ====");
        writeln("Cluster size: ", cluster.size);
        writeln("Total triangles: ", triangleCount);
    }

    // Convert cluster to array and create proper domain
    var clusterArray = cluster.toArray();
    var clusterDomain: domain(int, parSafe=true) = clusterArray;
    
    if logLevel == LogLevel.DEBUG {
        writeln("Created domain from cluster");
    }

    var metrics = new triangleDistMetrics();
    var totalEdges = 0;
    var participatingVertices: atomic int;
    var maxTriangles = 0;
    var totalTrianglesPerVertex = 0;

    forall v in clusterDomain with (+ reduce totalEdges, 
                                  max reduce maxTriangles,
                                  + reduce totalTrianglesPerVertex) {
        var neighbors = neighborsSetGraphG1[v] & cluster;
        var localTriangleCount = 0;
        
        // Count triangles for this vertex
        for u in neighbors {
            if u > v {  // Process each edge once
                var u_neighbors = neighborsSetGraphG1[u] & cluster;
                for w in (u_neighbors & neighbors) {
                    if w > u {  // Maintain ordering v < u < w
                        localTriangleCount += 1;
                    }
                }
            }
        }

        // Update metrics
        if localTriangleCount > 0 {
            participatingVertices.add(1);
        }
        maxTriangles = max(maxTriangles, localTriangleCount);
        totalTrianglesPerVertex += localTriangleCount;
        totalEdges += neighbors.size;
    }

    // Calculate final metrics
    totalEdges = totalEdges / 2;  // Each edge was counted twice
    
    // Triangle density = number of triangles / number of possible triangles
    // For an undirected graph, possible triangles = (n * (n-1) * (n-2)) / 6
    var possibleTriangles = (cluster.size * (cluster.size-1) * (cluster.size-2)) / 6;
    metrics.triangleDensity = if possibleTriangles > 0 
                             then triangleCount:real / (totalEdges:real)
                             else 0.0;
    
    metrics.participationRate = participatingVertices.read():real / cluster.size:real;
    metrics.maxLocalTriangles = maxTriangles;
    metrics.avgTrianglesPerVertex = totalTrianglesPerVertex:real / cluster.size:real;

    if logLevel == LogLevel.DEBUG {
        writeln("\nTriangle Distribution Results:");
        writeln("Total edges: ", totalEdges);
        writeln("Triangle density: ", metrics.triangleDensity);
        writeln("Participation rate: ", metrics.participationRate);
        writeln("Max triangles per vertex: ", metrics.maxLocalTriangles);
        writeln("Average triangles per vertex: ", metrics.avgTrianglesPerVertex);
        writeln("==== Triangle Distribution Analysis Complete ====\n");
    }

    return metrics;
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
    const SAMPLE_THRESHOLD = 10000; 
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


/* Optimized triangle counting for a vertex */
proc countLocalTriangles(v: int, neighbors: set(int)) {
    if logLevel == LogLevel.DEBUG {
        writeln("\nCounting triangles for vertex ", v);
        writeln("Neighbors: ", neighbors);
    }

    var triangleCount = 0;
    var v_neighbors = neighborsSetGraphG1[v];
    
    // Only process neighbors with higher IDs to avoid counting triangles multiple times
    for u in neighbors {
        if u > v {  // Process only higher ID neighbors
            var u_neighbors = neighborsSetGraphG1[u];
            
            // Find common neighbors (forming triangles) between v and u
            for w in u_neighbors {
                if w > u && v_neighbors.contains(w) {  // Ensure ordered counting v < u < w
                    if logLevel == LogLevel.DEBUG {
                        writeln("Found triangle: ", v, "-", u, "-", w);
                    }
                    triangleCount += 1;
                }
            }
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Total triangles for vertex ", v, ": ", triangleCount);
    }

    return triangleCount;
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
/* Calculate clustering coefficients using minimum search strategy */
proc calculateClusteringCoefficients(ref cluster: set(int), ref metrics: densityMetrics) throws {
    if logLevel == LogLevel.DEBUG {
        writeln("\n==== Starting Clustering Coefficients Calculation ====");
        writeln("Original cluster size: ", cluster.size);
    }

    var updatedMetrics = metrics;
    var analysisCluster = cluster;

    // Handle sampling for large clusters
    if cluster.size > 10000 {
        const sampleSize = if cluster.size <= 50000 then (cluster.size * 0.2): int
                     else if cluster.size <= 100000 then (cluster.size * 0.1): int
                     else (cluster.size * 0.05): int;

        if logLevel == LogLevel.DEBUG {
            writeln("Using sampling for large cluster");
            writeln("Sample size: ", sampleSize);
        }
        analysisCluster = sampleClusterVertices(cluster, sampleSize);
    }

    // Convert to array and create domain
    var clusterArray = analysisCluster.toArray();
    var clusterDomain: domain(int) = clusterArray;

    // Atomic counters for parallel computation
    var totalTriangles: atomic int;
    var totalWedges: atomic int;
    var sumLocalCC: atomic real;
    var validVertices: atomic int;

    if logLevel == LogLevel.DEBUG {
        writeln("Starting triangle and wedge counting");
    }

    // Process vertices in parallel
    forall v in clusterDomain {
        var v_neighbors = neighborsSetGraphG1[v] & analysisCluster;
        var v_deg = v_neighbors.size;
        
        if v_deg >= 2 {
            validVertices.add(1);
            var localTriangles = 0;
            var possibleTriangles = (v_deg * (v_deg - 1)) / 2;
            totalWedges.add(possibleTriangles);

            // Count triangles for this vertex
            for u in v_neighbors {
                for w in v_neighbors {
                    if u != w && u > v && w > u {  // Avoid counting same triangle multiple times
                        if (neighborsSetGraphG1[u] & analysisCluster).contains(w) {
                            localTriangles += 1;
                        }
                    }
                }
            }

            totalTriangles.add(localTriangles);

            // Calculate local clustering coefficient
            var localCC = if possibleTriangles > 0 
                         then localTriangles:real / possibleTriangles:real
                         else 0.0;
            sumLocalCC.add(localCC);

            if logLevel == LogLevel.DEBUG {
                writeln("Vertex ", v, " stats:");
                writeln("  Degree: ", v_deg);
                writeln("  Local triangles: ", localTriangles);
                writeln("  Possible triangles: ", possibleTriangles);
                writeln("  Local CC: ", localCC);
            }
        }
    }

    // Calculate final metrics
    var finalTriangles = totalTriangles.read();
    var finalWedges = totalWedges.read();
    var numValidVertices = validVertices.read();
    
    // Scale up if sampling was used
    if cluster.size > 10000 {
        var scaleFactor = cluster.size:real / analysisCluster.size:real;
        finalTriangles = (finalTriangles:real * scaleFactor):int;
        finalWedges = (finalWedges:real * scaleFactor):int;
    }
    
    updatedMetrics.triangleCount = finalTriangles;
    
    // Calculate average local clustering coefficient (only for vertices with degree >= 2)
    updatedMetrics.avgLocalClusteringCoeff = if numValidVertices > 0
                                            then sumLocalCC.read() / numValidVertices:real
                                            else 0.0;
    
    // Calculate global clustering coefficient (same as transitivity)
    updatedMetrics.globalClusteringCoeff = if finalWedges > 0
                                          then (3.0 * finalTriangles:real) / finalWedges:real
                                          else 0.0;

    if logLevel == LogLevel.DEBUG {
        writeln("\nFinal Results:");
        writeln("Total triangles: ", updatedMetrics.triangleCount);
        writeln("Total wedges: ", finalWedges);
        writeln("Valid vertices (degree >= 2): ", numValidVertices);
        writeln("Sum of local CCs: ", sumLocalCC.read());
        writeln("Average local clustering: ", updatedMetrics.avgLocalClusteringCoeff);
        writeln("Global clustering: ", updatedMetrics.globalClusteringCoeff);
        writeln("==== Clustering Coefficients Calculation Complete ====\n");
    }

    return updatedMetrics;
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

/* Assortativity calculation */
proc calculateAssortativity(ref cluster: set(int), ref basicStats, ref metrics: connectivityMetrics) throws {
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
    writeln("  Minimum Degree: ", metrics.connectivity.minDegree);
    writeln("  Maximum Degree: ", metrics.connectivity.maxDegree);
    writeln("  Average Degree: ", metrics.connectivity.avgDegree);
    writeln("  Total Internal Edges: ", metrics.connectivity.totalInternalEdges);
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
    writeln("  Triangle Density: ", metrics.triangleDist.triangleDensity);
    writeln("  Participation Rate: ", metrics.triangleDist.participationRate);
    writeln("  Max Local Triangles: ", metrics.triangleDist.maxLocalTriangles);
    writeln("  Average Triangles Per Vertex: ", metrics.triangleDist.avgTrianglesPerVertex);

    writeln("\n----- Path-based Metrics -----");
    writeln("  Local/Global Transitivity Ratio: ", metrics.paths.localGlobalRatio);
    writeln("  Cohesion Score: ", metrics.paths.cohesionScore);
    writeln("  Path Distribution: ");
    for i in metrics.paths.pathDistribution.domain {
        writeln("    Length ", i, ": ", metrics.paths.pathDistribution[i]);
    }

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
    if metrics.eccentricity.centerVertices.size <= 10 {
        writeln("  Center Vertices: ", metrics.eccentricity.centerVertices);
    }
    writeln("  Number of Peripheral Vertices: ", metrics.eccentricity.peripheralVertices.size);
    if metrics.eccentricity.peripheralVertices.size <= 10 {
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
    
    writeln("\nPath Length Distribution:");
    writeln("  Mean: ", metrics.pathDistribution.mean);
    writeln("  Median: ", metrics.pathDistribution.median);
    writeln("  Standard Deviation: ", metrics.pathDistribution.standardDev);
    writeln("  Skewness: ", metrics.pathDistribution.skewness);
    writeln("  Kurtosis: ", metrics.pathDistribution.kurtosis);
    writeln("  Key Percentiles:");
    writeln("    25th: ", metrics.pathDistribution.percentiles[25]);
    writeln("    50th: ", metrics.pathDistribution.percentiles[50]);
    writeln("    75th: ", metrics.pathDistribution.percentiles[75]);
    writeln("    90th: ", metrics.pathDistribution.percentiles[90]);

    writeln("\n===========================================");
}



///////////////////////////////////////////////////////////////////////////////////////////////
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
        analyzeCluster(clusterToAdd, key);
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