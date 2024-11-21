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
  use Heap;
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

      writeln("meanDegreeGraph: ", meanDegreeGraph);
      writeln();
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
      writeln("*****************removeDegreeOne called***********************");

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
    /*
    An O(m) Algorithm for Cores Decomposition of Networks
    Vladimir Batagelj and Matjaz Zaversnik, 2003.
    https://arxiv.org/abs/cs.DS/0310049
    
    // Currently, k_max is passed as a parameter but not utilized within the function.
 */


    // Define the kCoreDecomposition function
    proc kCoreDecomposition(ref clusterNodes: set(int), k_max: int) : set(int) throws {
        writeln("/////////////////////////kCoreDecomposition///////////////////////");
        writeln("clusterNodes: ", clusterNodes);
        // writeln("k_max: ", k_max);

        // Domain and degree initialization
        const coreKDomain: domain(int) = clusterNodes.toArray();
        var degrees: [coreKDomain] int = 0;  // Degree of each node
        var cores: [coreKDomain] int = 0;    // Core number of each node
        var maxDegree = 0;

        // Step 1: Calculate degrees and determine max degree
        // writeln("\nStep 1: Calculating degrees for each node...");
        for v in coreKDomain {
            degrees[v] = calculateClusterDegree(clusterNodes, v);
            if degrees[v] > maxDegree then maxDegree = degrees[v];
        }
        // writeln("Degrees of nodes: ", degrees);
        // writeln("Max degree: ", maxDegree);

        // Step 2: Initialize bins and fill bins based on degrees
        // writeln("\nStep 2: Initializing bins based on degrees...");
        var bins: [0..maxDegree] list(int);

        for v in coreKDomain {
            bins[degrees[v]].pushBack(v);  // Place each node in the appropriate bin based on its degree
        }
        // writeln("Initial bins: ", bins);

        // Step 3: Set up degree counters and cumulative start positions in bin array
        // writeln("\nStep 3: Setting up degree counters and bin start positions...");
        var degreeCount: [0..maxDegree] int = 0;

        // Count the number of vertices with each degree
        for d in 0..maxDegree {
            degreeCount[d] = bins[d].size;
        }
        // writeln("degreeCount: ", degreeCount);

        // Calculate cumulative starting positions for each degree in vert
        var binStart: [0..maxDegree] int = 1;  // Initialize all to 1
        for d in 1..maxDegree {
            binStart[d] = binStart[d-1] + degreeCount[d-1];
        }
        // writeln("Bin start positions: ", binStart);

        // Step 4: Initialize vert and pos arrays and populate with vertices ordered by degree
        // writeln("\nStep 4: Initializing vert and pos arrays...");
        // Extend vert array to n +1 to prevent out-of-bounds access
        var vert: [1..clusterNodes.size +1] int;  // 1..9 in your case
        var pos: [coreKDomain] int;

        // Populate vert and pos arrays
        for d in 0..maxDegree {
            for v in bins[d] {
                pos[v] = binStart[d];         // Store position of vertex v
                vert[binStart[d]] = v;        // Place vertex v in vert array at the start position
                binStart[d] += 1;             // Increment start position for the next vertex of the same degree
            }
        }
        // writeln("Initial vert array (vertices ordered by degree): ", vert);
        // writeln("Initial pos array (positions of vertices in vert): ", pos);

        // Step 4.1: Restore bin start positions to original
        //writeln("\nStep 4.1: Restoring bin start positions...");
        for d in 0..maxDegree {
            binStart[d] = binStart[d] - degreeCount[d];
        }
        // writeln("Restored bin start positions: ", binStart);

        // Step 5: Core decomposition process
        // writeln("\nStep 5: Starting core decomposition process...");
        for i in 1..clusterNodes.size {
            const v = vert[i];
            cores[v] = degrees[v];  // Assign core number based on degree
            // writeln("Processing vertex ", v, " with initial core value: ", cores[v]);

            // Update degrees of neighbors with higher degree
            const ref neighbors = neighborsSetGraphG1[v];
            for u in neighbors {
                if clusterNodes.contains(u) && degrees[u] > degrees[v] {
                    const du = degrees[u];
                    const pu = pos[u];
                    const pw = binStart[du];
                    const w = vert[pw];

                    // **Added Bounds Check: Ensure pw and pu are within valid range**
                    if (pw < 1 || pw > clusterNodes.size +1) {
                        // writeln("Error: 'pw' (", pw, ") is out of bounds for 'vert' array.");
                        continue;  // Skip this neighbor if index is out of bounds
                    }
                    if (pu < 1 || pu > clusterNodes.size +1) {
                        // writeln("Error: 'pu' (", pu, ") is out of bounds for 'vert' array.");
                        continue;  // Skip this neighbor if index is out of bounds
                    }

                    // Swap u and w in vert and update positions
                    if u != w {
                        pos[u] = pw;
                        vert[pu] = w;
                        pos[w] = pu;
                        vert[pw] = u;
                        // writeln("Swapped vertices ", u, " and ", w, " in vert array.");
                    }

                    // Increment start position in bin and decrease degree of u
                    binStart[du] += 1;
                    degrees[u] -= 1;

                    // writeln("Updated degree of neighbor ", u, " to ", degrees[u]);
                    // writeln("Updated pos[" , u, "] = ", pos[u], ", vert[" , pw, "] = ", u);
                }
            }
        }

        //writeln("\nFinal cores: ", cores);

        // Step 6: Populate coresSet with core numbers
        var coresSet: set(int);
        var peripherySet: set(int);
        //writeln("cores: ",cores);
        //writeln("cores domain: ",cores.domain);
        for v in coreKDomain {
            if cores[v] >= k_max{
              coresSet.add(v);
            }else{
              peripherySet.add(v);/////////////////I added but I should check correctness!!!!!!!!!!
            }
        }
        writeln("coresSet: ", coresSet);
        writeln("peripherySet: ", peripherySet);
        writeln("/////////////////////////kCoreDecomposition ENDED!///////////////////////");
        //Find Edges Connecting Periphery to Core
        // writeln("Edges connecting periphery to core:");
        // for edge in connectingEdges {
        //     writeln("Edge between Node ", edge(0), " and Node ", edge(1));
        return coresSet;
    } // end of kCoreDecomposition
    ///////////////////////////////////cluster metrics /////////////////////////////////////////
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
    //var flow: flowMetrics;
    //var robustness: robustnessMetrics;
    var conductanceData:[0..2] real;  
}
    /* Main analysis function */
    proc analyzeCluster(ref cluster: set(int)) throws {
      var metrics = new clusterMetricsRecord();
        
      // Handle empty or singleton clusters
      if cluster.size <= 1 {
        metrics = initializeEmptyMetrics();
        printClusterAnalysis(metrics, cluster.size);
        return metrics;
      }
        
      // Basic Metrics
      metrics.connectivity = calculateBasicConnectivity(cluster);
      metrics.density = calculateInternalDensity(cluster);
      metrics.conductanceData = calculateConductance(cluster)[0];
      writeln("we are here after calculateConductance");  
      // Advanced Connectivity Metrics
      var advConnectivity = calculateAdvancedConnectivity(cluster);
      writeln("we are here after calculateAdvancedConnectivity");  
      writeln(advConnectivity);

      metrics.connectivity.degreeVariance = advConnectivity.degreeVariance;
      metrics.connectivity.degreeSkewness = advConnectivity.degreeSkewness;
      metrics.connectivity.assortativity = advConnectivity.assortativity;
      metrics.connectivity.effectiveDiameter = advConnectivity.effectiveDiameter;
    
    // // Advanced Density Metrics
    var advDensity = calculateAdvancedDensity(cluster);
    writeln("we are here after calculateAdvancedDensity");  

    // metrics.density.triangleCount = advDensity[1]: int;
    // metrics.density.globalClusteringCoeff = advDensity[2];
    // metrics.density.avgLocalClusteringCoeff = advDensity[3];
    
    // // Spectral Metrics
    calculateSpectralBounds(metrics.conductanceData);

    
    // // Core Structure
    calculateCoreNumbers(cluster);
    // var advCore = calculateAdvancedCore(cluster);
    // metrics.core.corePeripheryScore = advCore[1];
    // metrics.core.coreDegreeCorrelation = advCore[2];
    
    // Print comprehensive analysis
    //printClusterAnalysis(metrics, cluster.size);
    
    return metrics;
}
/* Initialize empty metrics with proper default values */
proc initializeEmptyMetrics() {
    var metrics = new clusterMetricsRecord();
    
    // Initialize connectivityMetrics
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
    
    // Initialize densityMetrics
    metrics.density.density = 0.0;
    metrics.density.sparsity = 1.0;
    metrics.density.internalEdges = 0;
    metrics.density.maxPossibleEdges = 0;
    metrics.density.triangleCount = 0;
    metrics.density.globalClusteringCoeff = 0.0;
    metrics.density.avgLocalClusteringCoeff = 0.0;
    metrics.density.edgeDensityDistribution = 0.0;
    metrics.density.localDensityVariance = 0.0;
    metrics.density.densityCorrelation = 0.0;
    
    
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
/* Helper function for efficient sampling in large graphs with multiple strategies */
/*
// For large graphs, recommended sample size is O(log2(n)) where n is cluster size
var sampleSize = max(2, ceil(log2(cluster.size) * 10): int);
var sampledVertices = sampleVerticesForBetweenness(cluster, sampleSize);
var (avgBetweenness, maxBetweenness) = calculateBetweennessCentrality(cluster, sampledVertices);
*/
/* Helper function for optimized sampling specifically for betweenness centrality */
proc sampleVertices(ref cluster: set(int), sampleSize: int) {
    if cluster.isEmpty() {
        // writeln("Warning: Empty cluster provided");
        return cluster;
    }
    
    var effectiveSampleSize = min(sampleSize, cluster.size);
    if effectiveSampleSize <= 0 {
        writeln("Warning: Invalid sample size requested");
        return cluster;
    }
    
    var sampledVertices: set(int);
    var clusterArray = cluster.toArray();
    
    if clusterArray.size == 0 {
        // writeln("Warning: Failed to convert cluster to array");
        return cluster;
    }
    
    // writeln("Debug: Initial cluster size=", cluster.size, " sampleSize=", effectiveSampleSize);
    
    var seed = 42;
    var rng = new randomStream(real, seed);
    
    var weights: [clusterArray.domain] real;
    var maxDegree = 0;
    
    // First pass: find max degree and calculate initial weights
    for i in clusterArray.domain {
        var vertex = clusterArray[i];
        if !neighborsSetGraphG1.domain.contains(vertex) {
            // writeln("Warning: Vertex ", vertex, " not found in graph");
            continue;
        }
        var degree = neighborsSetGraphG1[vertex].size;
        maxDegree = max(maxDegree, degree);
        weights[i] = degree: real;
    }
    
    // writeln("Debug: Max degree found: ", maxDegree);
    
    if maxDegree == 0 {
        // writeln("Warning: All vertices have degree 0");
        return cluster;
    }

    // This adjusts the weights using sqrt to balance between high and low degree vertices
    var totalWeight = 0.0;
    for i in weights.domain {
        weights[i] = sqrt(weights[i] / maxDegree: real);
/*
        To Oliver:
        Remove the sqrt to favor high-degree vertices more strongly
        Use weights[i] = (degree: real) ** 0.25 to reduce the bias towards high-degree vertices
        Use uniform weights (weights[i] = 1.0) for completely random sampling
*/
        totalWeight += weights[i];
    }
    
    // writeln("Debug: Total weight before normalization: ", totalWeight);
    
    if totalWeight <= 0.0 {
        // writeln("Warning: Invalid total weight");
        return cluster;
    }
    
    for i in weights.domain {
        weights[i] /= totalWeight;
    }
    
    var available = cluster;
    var iterCount = 0;
    const maxIterations = cluster.size * 2;
    
    // writeln("Debug: Starting vertex selection loop. Target size=", effectiveSampleSize);
    
    while (sampledVertices.size < effectiveSampleSize && 
           available.size > 0 && 
           iterCount < maxIterations) {
        
        var r = rng.getNext();
        var cumSum = 0.0;
        var vertexSelected = false;
        
        // writeln("Debug: iteration ", iterCount, 
        //         " sampledSize=", sampledVertices.size,
        //         " targetSize=", effectiveSampleSize,
        //         " available=", available.size,
        //         " random=", r);
        
        for i in clusterArray.domain {
            var vertex = clusterArray[i];
            if available.contains(vertex) {
                cumSum += weights[i];
                // writeln("Debug:   considering vertex ", vertex, " cumSum=", cumSum);
                if r <= cumSum {
                    sampledVertices.add(vertex);
                    available.remove(vertex);
                    vertexSelected = true;
                    // writeln("Debug:   selected vertex ", vertex);
                    break;
                }
            }
        }
        
        // Always increment the counter
        iterCount += 1;
        
        // Force selection if we're getting stuck
        if !vertexSelected && iterCount > maxIterations / 2 {
            for vertex in available {
                sampledVertices.add(vertex);
                available.remove(vertex);
                // writeln("Debug: force selected vertex ", vertex);
                break;
            }
        }
    }
    
    // writeln("Debug: Finished main selection loop. Selected=", sampledVertices.size);
    
    // Handle remaining vertices if needed
    if sampledVertices.size < effectiveSampleSize && available.size > 0 {
        var remainingCount = min(effectiveSampleSize - sampledVertices.size, available.size);
        var remainingVertices: [0..#remainingCount] (int, int);
        var idx = 0;
        
        // writeln("Debug: Handling remaining vertices. Need ", remainingCount, " more");
        
        for vertex in available {
            if idx >= remainingCount then break;
            if neighborsSetGraphG1.domain.contains(vertex) {
                remainingVertices[idx] = (vertex, neighborsSetGraphG1[vertex].size);
                idx += 1;
            }
        }
        
        if idx > 0 {
            sort(remainingVertices[0..#idx], comparator=new ReverseComparator());
            
            for i in 0..#idx {
                var (vertex, _) = remainingVertices[i];
                sampledVertices.add(vertex);
                // writeln("Debug: Added remaining vertex ", vertex);
                if sampledVertices.size >= effectiveSampleSize then break;
            }
        }
    }
    
    // writeln("Betweenness Sampling Statistics:");
    // writeln("  Final sample size: ", sampledVertices.size);
/*
To Oliver: Do Not remove it as long as we are testing the codes!
Everything after this is just my analysis/reporting code that checks how well our 
sampling performed. 
It doesn't modify the sampled vertices at all - 
it just calculates statistics to tell us about the quality of our sample.



    if sampledVertices.size > 0 {
        writeln("Debug: Starting degree statistics calculation");
        var sampleDegrees: [0..sampledVertices.size-1] int;
        var validDegrees = 0;
        var totalSampleDegree = 0;
        var totalClusterDegree = 0;
        var validClusterVertices = 0;
        
        writeln("Debug: Calculating sample degrees");
        var vertexList = sampledVertices.toArray();  // Convert set to array for indexing
        for i in 0..#sampledVertices.size {
            var vertex = vertexList[i];
            if neighborsSetGraphG1.domain.contains(vertex) {
                sampleDegrees[i] = neighborsSetGraphG1[vertex].size;
                totalSampleDegree += sampleDegrees[i];
                validDegrees += 1;
                writeln("Debug: Processed vertex ", vertex, " with degree ", sampleDegrees[i]);
            }
        }
        
        writeln("Debug: Calculating cluster degrees");
        for vertex in cluster {
            if neighborsSetGraphG1.domain.contains(vertex) {
                totalClusterDegree += neighborsSetGraphG1[vertex].size;
                validClusterVertices += 1;
            }
        }
        
        if validDegrees > 0 && validClusterVertices > 0 {
            var avgSampleDegree = totalSampleDegree: real / validDegrees: real;
            var avgClusterDegree = totalClusterDegree: real / validClusterVertices: real;
            
            writeln("  Degree Statistics:");
            writeln("    Sample average degree: ", avgSampleDegree);
            writeln("    Cluster average degree: ", avgClusterDegree);
            writeln("    Degree representation ratio: ", 
                  if avgClusterDegree != 0.0 then avgSampleDegree/avgClusterDegree else 0.0);
        } else {
            writeln("  Warning: Unable to calculate degree statistics - insufficient valid vertices");
        }
    }
*/
    return sampledVertices;
}

 /* Helper function for betweenness centrality calculation with sampling 
Betweenness Centrality Formula:

BC(v) = ∑(s≠v≠t) [σst(v) / σst]

Where:
- σst is the total number of shortest paths from node s to node t
- σst(v) is the number of those paths that pass through vertex v

This measures how often a vertex v lies on shortest paths between other vertices,
indicating its importance as a bridge between different parts of the graph.
The algorithm is "Brandes' Algorithm" for betweenness centrality:
Reference: Brandes, U. (2001). "A faster algorithm for betweenness centrality." 
Journal of Mathematical Sociology, 25(2):163-177.
*/

//proc calculateBetweennessCentrality(ref nodes: set(int), sampledVertices) throws {

        proc calculateBetweennessCentrality(ref nodes: set(int), ref sampledVertices: set(int)) {
            const nodesDomain:domain(int) = nodes.toArray();
            var betweenness: [nodesDomain] real = 0.0;

            // // Sample k nodes if k is less than total nodes
            // var processNodes: set(int);
            //     processNodes = sampledVertices;
            if sampledVertices.size == 0 || nodes.size == 0{
                return (0.0, 0.0);
            }

            // Process each node //To Oliver: here is the best place to make it parallel. I think we should remove the singleSourceShortestPathBasic!!

            for s in sampledVertices {
                debug("\nProcessing source node: ", s);
                var (S, P, sigma, _) = singleSourceShortestPathBasic(s, nodes);
                accumulateBasic(betweenness, S, P, sigma, s);
            }

            // Rescale the betweenness values
            rescale(betweenness, nodes.size, sampledVertices.size);

            // Calculate average and maximum betweenness
            for idx in betweenness.domain do writeln("for ", idx,": betweenness is: ",betweenness[idx] );
            var maxBetweenness: real = 0.0;
            var avgBetweenness: real = 0.0;

            maxBetweenness = max reduce betweenness;
            avgBetweenness = + reduce betweenness / nodes.size;
            writeln("maxBetweenness: ", maxBetweenness);
            writeln("avgBetweenness: ", avgBetweenness);
            
            return (avgBetweenness, maxBetweenness);
        }

        const DEBUG = false;  // Global debug flag

        // Helper function to print debug messages
        proc debug(msg...) {
            if DEBUG {
                writeln("DEBUG: ", (...msg));
            }
        }

        // Helper function for single source shortest path using BFS
        proc singleSourceShortestPathBasic(s: int, nodes: set(int)) {
            debug("Starting _singleSourceShortestPathBasic for source node ", s);

            const nodesDomain:domain(int) = nodes.toArray();
            var S: list(int);
            var P: [nodesDomain] list(int);
            var sigma: [nodesDomain] real = 0.0;
            var D: [nodesDomain] int = -1;  // Use -1 as infinity

            sigma[s] = 1.0;
            D[s] = 0;
            var Q: list(int);
            Q.pushBack(s);
            var front = 0;  // Initialize front index for the queue

            // debug("Initial state:");
            // debug("  Source node: ", s);
            // debug("  Initial Q: ", Q);

            while front < Q.size {
                var v = Q[front];
                front += 1;  // Move front index forward
                S.pushBack(v);
                var Dv = D[v];
                var sigmav = sigma[v];

                // debug("Processing node ", v);
                // debug("  Current distance (Dv): ", Dv);
                // debug("  Current sigma (sigmav): ", sigmav);

                var neighborInCluster = neighborsSetGraphG1[v] & nodes;
                for w in neighborInCluster {
                    debug("    Examining neighbor ", w);
                    // First time seeing w
                    if D[w] == -1 {
                        debug("      First time seeing node ", w);
                        Q.pushBack(w);
                        D[w] = Dv + 1;
                        debug("      Updated distance D[", w, "] = ", D[w]);
                    }
                    // If this is a shortest path, count paths
                    if D[w] == Dv + 1 {
                        debug("      Found shortest path to ", w, " through ", v);
                        sigma[w] += sigmav;
                        P[w].pushBack(v);
                        debug("      Updated sigma[", w, "] = ", sigma[w]);
                        debug("      Updated predecessors P[", w, "] = ", P[w]);
                    }
                }
                debug("  Current Q: ", Q);
            }

            // debug("Finished _singleSourceShortestPathBasic");
            // debug("Final S: ", S);
            // debug("Final sigma: ", sigma);
            return (S, P, sigma, D);
        }


        // Helper function for accumulation
        proc accumulateBasic(ref betweenness: [?D] real, S: list(int), P: [?D2] list(int), 
                            sigma: [?D3] real, s: int) {
            debug("Starting _accumulateBasic for source node ", s);
            var delta: [D] real = 0.0;
            
            debug("Initial betweenness: ", betweenness);
            
            // Process vertices in reversed order
            var idx = S.size - 1;
            while idx >= 0 {
                var w = S[idx];
                debug("Processing node ", w, " in reverse order");
                var coeff = (1.0 + delta[w]) / sigma[w];
                debug("  Coefficient for node ", w, ": ", coeff);
                
                for v in P[w] {
                    debug("    Processing predecessor ", v, " of node ", w);
                    delta[v] += sigma[v] * coeff;
                    debug("    Updated delta[", v, "] = ", delta[v]);
                }
                if w != s {
                    betweenness[w] += delta[w];
                    debug("  Updated betweenness[", w, "] = ", betweenness[w]);
                }
                idx -= 1;
            }
            
            debug("Final betweenness after accumulation: ", betweenness);
            return betweenness;
        }

        // Helper function for rescaling
        proc rescale(ref betweenness: [?D] real, n: int, k: int) {
            // debug("Starting _rescale");
            // debug("Initial betweenness: ", betweenness);
            // debug("n = ", n, ", k = ", k);
            
            var scale: real;
            if n <= 2 {
                debug("No normalization needed (n <= 2)");
                return betweenness;
            }
            
            scale = 1.0 / ((n-1) * (n-2));
            debug("Base scale factor: ", scale);
            
            // Adjust scale if using sampling (not applicable here since k = n)
            if k != n {
                scale = scale * n / k;
                debug("Adjusted scale factor for sampling: ", scale);
            }
            
            // scale *= 0.5;
            // debug("Final scale factor: ", scale);
            
            forall v in D {
                betweenness[v] *= scale;
            }
            
            // debug("Final betweenness after rescaling: ", betweenness);
            return betweenness;
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
/*
To Oliver: for future:// based on bartozs outputs will be adjusted
proc calculateSampleSize(ref cluster: set(int), graphDensity: real) {
    var n = cluster.size;
    var baseSampleSize: int;
    
    // Basic size calculation
    if n < 1000 {
        baseSampleSize = max(30, (n * 2) / 10);  // 20%
    } else if n < 10000 {
        baseSampleSize = max(100, n / 10);       // 10%
    } else {
        baseSampleSize = max(300, ceil(sqrt(n:real)):int);
    }
    
    // Density adjustment
    var densityFactor = if graphDensity < 0.1 then 1.5
                       else if graphDensity < 0.3 then 1.2
                       else 1.0;
    
    var adjustedSize = (baseSampleSize:real * densityFactor):int;
    
    // Bounds checking
    return min(max(adjustedSize, 10), n);
}
*/
/* Advanced connectivity metrics */
proc calculateAdvancedConnectivity(ref cluster: set(int)) throws {
    var metrics: connectivityMetrics;
    //const SAMPLE_SIZE = min(cluster.size, floor(sqrt(cluster.size: real) * log2(cluster.size: real)): int);
    // For large graphs, recommended sample size is O(log(n)) where n is cluster size
    const SAMPLE_SIZE = max(2, ceil(log2(cluster.size) * 10): int);
    // For these test SAMPLE_SIZE = cluster size
    //const SAMPLE_SIZE = cluster.size;
    // Get basic stats first
    var basicStats = calculateBasicStats(cluster);
    writeln("$$$$$$ basicStats calculated");
    // Calculate assortativity in separate steps
    metrics = calculateAssortativity(cluster, basicStats, metrics);
    writeln("$$$$$$$$$$$$$$ Assortativity calculated");
    writeln(metrics);
    // Calculate diameter and betweenness
    metrics = calculateDiameterAndBetweenness(cluster, SAMPLE_SIZE, metrics);
    writeln("$$$$$$$$$DiameterAndBetweenness calculated");
    writeln(metrics);

    return metrics;
}

/* Helper function for assortativity calculation using reductions 
1. Definition:
- Measures the tendency of nodes to connect to other nodes with similar degrees
- Ranges from -1 to 1
- Similar to correlation coefficient but for network connections

2-Interpreting Degree Assortativity Values
----Positive Assortativity (Close to +1):

Indicates that high-degree nodes (hubs) are more likely to connect to other high-degree nodes, and low-degree 
nodes are more likely to connect to other low-degree nodes.
Common in social networks, where people with many connections tend to connect with others who also have many 
connections (e.g., friendships, professional networks).
Example: r=0.8
----Negative Assortativity (Close to -1):

Indicates that high-degree nodes tend to connect to low-degree nodes.
Common in technological or biological networks such as the Internet or neural networks, where hubs serve as connectors to many smaller nodes.
Example: r=−0.7
----Neutral Assortativity (Close to 0):

Indicates no significant correlation between the degrees of connected nodes.
Connections in such networks appear more random, with no preference for similar or dissimilar degrees.
Example: r=0.0

*/
proc calculateAssortativity(ref cluster: set(int), ref basicStats, ref metrics: connectivityMetrics) throws{
    var updatedMetrics = metrics;
    const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();

    // Arrays to store local contributions
    var localNums: [clusterDomain] real;
    var localDen1s: [clusterDomain] real;
    var localDen2s: [clusterDomain] real;
    
    // Calculate local contributions
    forall v in cluster {
        var v_deg = basicStats.degrees[v];
        var neighbors = neighborsSetGraphG1[v] & cluster;
        
        // Initialize local sums
        localNums[v] = 0.0;
        localDen1s[v] = 0.0;
        localDen2s[v] = 0.0;
        
        // Calculate local contributions
        for u in neighbors {
            var u_deg = basicStats.degrees[u];
            localNums[v] += v_deg * u_deg;
            localDen1s[v] += v_deg * v_deg;
            localDen2s[v] += v_deg;
        }
    }
    
    // Use reductions to sum up all contributions
    var numerator = + reduce localNums;
    var denominator1 = + reduce localDen1s;
    var denominator2 = + reduce localDen2s;
    
    // Calculate final metrics
    var M = basicStats.n_edges;
    if M > 0 {
        var den2 = (denominator2 / (2 * M)) ** 2;
        updatedMetrics.assortativity = (numerator/(2*M) - den2) / 
                                     (denominator1/(2*M) - den2);
    }
    writeln("Degree Assortativity Coefficient: ", updatedMetrics.assortativity);
    return updatedMetrics;
}

/* Helper function for diameter and betweenness calculations */
proc calculateDiameterAndBetweenness(ref cluster: set(int), SAMPLE_SIZE: int, ref metrics: connectivityMetrics) throws {
    var updatedMetrics = metrics;
    var sampledVertices = sampleVertices(cluster, SAMPLE_SIZE);
    // var sampledVertices = sampleVerticesForBetweenness(cluster, sampleSize);

    // Calculate effective diameter
    var (lowerBound, estimatedDiameter, effectiveDiam) = calculateDiameterBounds(cluster, sampledVertices);
    writeln("after calculateDiameterBounds.");
    updatedMetrics.effectiveDiameter = effectiveDiam;
    writeln("effectiveDiam: ", effectiveDiam);
    writeln("lowerBound: ", lowerBound);
    writeln("estimatedDiameter: ", estimatedDiameter);

    // Calculate betweenness
    var (avgBetweenness, maxBetweenness) = calculateBetweennessCentrality(cluster, sampledVertices);
    writeln("$$$$ after calculateBetweennessCentrality.");
    writeln("avgBetweenness: ", avgBetweenness);
    writeln("maxBetweenness: ", maxBetweenness);
    updatedMetrics.avgBetweenness = avgBetweenness;
    updatedMetrics.maxBetweenness = maxBetweenness;
    
    return updatedMetrics;
}

/*
Algorithm based on: "On the Diameter of Real-World Networks" (2014)
Authors: C. Magnien, M. Latapy, M. Habib
Published in: ACM Transactions on Algorithms

Runtime Analysis:
- Full diameter computation: O(|V| * (|V| + |E|))
- With sampling (k vertices): O(k * (|V| + |E|))
  where k is the sample size, |V| is number of vertices, |E| is number of edges

Space Complexity: O(|V|) for distance array

Key Benefits:
- Provides guaranteed lower bound
- Estimates both exact and effective diameter
- Theoretical bounds for estimation accuracy
- Highly parallelizable

Lower Bound: This is a guaranteed minimum diameter
Effective Diameter:The distance at which 90% of all pairs of nodes can reach each other
Estimated Diameter (True Diameter):Attempts to estimate the actual maximum shortest path

Why we need all three:

Lower bound: Gives certainty
Effective diameter: Shows typical behavior
Estimated diameter: Tries to find true maximum

*/

/* Efficient BFS implementation */
proc efficientBFS(start: int, ref cluster: set(int)) throws {
    writeln("Starting BFS from vertex ", start);
    
    const clusterDomain: domain(int, parSafe=true) = cluster.toArray();
    var distances: [clusterDomain] int = -1;
    var maxDist = 0;
    
    if !cluster.contains(start) {
        writeln("Warning: Start vertex ", start, " not in cluster");
        return (distances, maxDist);
    }
    
    var frontier: set(int);
    var nextFrontier: set(int);
    var level = 0;
    
    distances[start] = 0;
    frontier.add(start);
    
    while frontier.size > 0 {
        writeln("  Level ", level, ": Processing frontier of size ", frontier.size);
        nextFrontier.clear();
        
        for v in frontier {
            var neighbors = neighborsSetGraphG1[v] & cluster;
            var newNodes = 0;
            
            for n in neighbors {
                if distances[n] == -1 {
                    distances[n] = distances[v] + 1;
                    maxDist = max(maxDist, distances[n]);
                    nextFrontier.add(n);
                    newNodes += 1;
                }
            }
            
            if newNodes > 0 {
                writeln("    Vertex ", v, " discovered ", newNodes, " new nodes");
            }
        }
        
        frontier = nextFrontier;
        level += 1;
    }
    
    writeln("BFS from ", start, " complete. Max distance found: ", maxDist);
    writeln("Number of vertices reached: ", 
            + reduce(distances >= 0), " out of ", cluster.size);
    
    return (distances, maxDist);
}

proc calculateDiameterBounds(ref cluster: set(int), sampledVertices: set(int)) throws {
    writeln("===================   calculateDiameterBounds   =========================");
    // writeln("Cluster size: ", cluster.size);
    // writeln("Sample size: ", sampledVertices.size);
    
    var globalLowerBound: atomic int;
    var pathLengths: [0..cluster.size] atomic int;
    
    // writeln("\nPhase 1: Processing sampled vertices");
    forall v in sampledVertices with (ref cluster) {
        // writeln("  Processing sample vertex: ", v);
        var (distances, maxDist) = efficientBFS(v, cluster);
        
        // Update lower bound atomically
        var currentLower = globalLowerBound.read();
        while (maxDist > currentLower && 
               !globalLowerBound.compareAndSwap(currentLower, maxDist)) {
            currentLower = globalLowerBound.read();
        }
        
        // writeln("  Current lower bound: ", globalLowerBound.read());
        
        // Count path lengths for effective diameter
        var distCounts: [0..maxDist] int;
        for d in distances {
            if d > 0 {  // only count non-zero distances
                distCounts[d] += 1;
                pathLengths[d].add(1);
            }
        }
        
        // writeln("  Distance distribution from vertex ", v, ":");
        for i in 0..maxDist {
            if distCounts[i] > 0 {
                // writeln("    Distance ", i, ": ", distCounts[i], " vertices");
            }
        }
    }
    
    var finalLowerBound = globalLowerBound.read();
    // writeln("\nPhase 2: Calculating effective diameter");
    
    // Calculate total number of paths (excluding distance 0)
    var totalPossiblePaths = 0;
    for i in 1..finalLowerBound {
        totalPossiblePaths += pathLengths[i].read();
    }
    
    var targetPaths = (totalPossiblePaths * 0.9): int;  // 90% of actual paths
    // writeln("Total paths found: ", totalPossiblePaths);
    // writeln("Target paths for 90th percentile: ", targetPaths);
    
    var accumulatedPaths = 0;
    var effectiveDiam = 1;  // start at 1 since we want actual path lengths
    
    for i in 1..finalLowerBound {
        accumulatedPaths += pathLengths[i].read();
        // writeln("  Cumulative paths at distance ", i, ": ", accumulatedPaths);
        
        if accumulatedPaths >= targetPaths {
            effectiveDiam = i;
            // writeln("  Found effective diameter: ", effectiveDiam);
            break;
        }
    }
    
    // Calculate estimated diameter using Magnien's bound
    var estimatedDiameter = max(finalLowerBound, 
                               (effectiveDiam * (1.0 + 1.0/log(cluster.size))): int);
    
    writeln("\nFinal Results:");
    writeln("Lower bound: ", finalLowerBound);
    writeln("Estimated diameter: ", estimatedDiameter);
    writeln("Effective diameter (90th percentile): ", effectiveDiam);
    
    return (finalLowerBound, estimatedDiameter, effectiveDiam);
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
        metrics.triangleCount = calculateTriangles(cluster);
        writeln("\n metrics: ", metrics);
        return metrics;
    }


/* Advanced density metrics including clustering coefficients */
proc calculateAdvancedDensity(ref cluster: set(int)) throws {
    var metrics = calculateInternalDensity(cluster);  // Get basic metrics first
    writeln("===================   calculateAdvancedDensity   =================================");
    // Handle small clusters
    if cluster.size <= 2 {
        metrics = initializeEmptyDensityMetrics(metrics);
        return metrics;
    }
    
    // Calculate clustering coefficients
    metrics = calculateClusteringCoefficients(cluster, metrics);
    //writeln(" ClusteringCoefficients metrics: ", metrics);
    //Calculate density distributions
    metrics = calculateDensityDistributions(cluster, metrics);
    
    return metrics;
}

/* Initialize empty density metrics */
proc initializeEmptyDensityMetrics(ref metrics) {
    metrics.globalClusteringCoeff = 0.0;
    metrics.avgLocalClusteringCoeff = 0.0;
    metrics.edgeDensityDistribution = 0.0;
    metrics.localDensityVariance = 0.0;
    metrics.densityCorrelation = 0.0;
    return metrics;
}

/* Calculate clustering coefficients */
proc calculateClusteringCoefficients(ref cluster: set(int), metrics) {
    var updatedMetrics = metrics;
    const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
    var localCCs: [clusterDomain] real;
    writeln("====================== calculateClusteringCoefficients =======================");
    // Use atomic variables for shared counters
    var totalPossibleTriangles: atomic int;
    var actualTriangles: atomic int;
    var sumLocalCC: atomic real;
    
    // First pass: calculate local clustering coefficients
    forall v in cluster {
        var neighbors = neighborsSetGraphG1[v] & cluster;
        var degree = neighbors.size;
        
        if degree >= 2 {
            var possibleTriangles = (degree * (degree - 1)) / 2;
            
            // Count triangles for this vertex
            var localTriangles = countLocalTriangles(v, neighbors);
            
            // Update atomic counters
            totalPossibleTriangles.add(possibleTriangles);
            actualTriangles.add(localTriangles);
            
            // Calculate and store local clustering coefficient
            var localCC = if possibleTriangles > 0 then 
                         localTriangles: real / possibleTriangles: real
                         else 0.0;
            
            localCCs[v] = localCC;
            sumLocalCC.add(localCC);
        }
    }
    
    // Calculate final coefficients
    updatedMetrics.avgLocalClusteringCoeff = sumLocalCC.read() / cluster.size;
    updatedMetrics.globalClusteringCoeff = if totalPossibleTriangles.read() > 0 then
                                          actualTriangles.read(): real / totalPossibleTriangles.read(): real
                                          else 0.0;
    writeln("updatedMetrics: ", updatedMetrics);
    return updatedMetrics;
}


/* Calculate local triangles */
proc countLocalTriangles(v: int, ref neighbors) {
    var localTriangles = 0;
    for u in neighbors {
        var commonNeighbors = neighbors & neighborsSetGraphG1[u];
        localTriangles += commonNeighbors.size;
    }
    return localTriangles / 2;  // Each triangle counted twice
}

/* Calculate density distributions */
proc calculateDensityDistributions(ref cluster: set(int), metrics) {
    var updatedMetrics = metrics;
    const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
    var localDensities: [clusterDomain] real;
    
    // First pass: calculate local densities
    forall v in cluster {
        var neighbors = neighborsSetGraphG1[v] & cluster;
        var degree = neighbors.size;
        
        if degree >= 1 {
            
            var localNeighborhood = neighbors;
            localNeighborhood.add(v);
            var localEdges = calculateLocalEdges(localNeighborhood);
            var maxLocalEdges = (degree + 1) * degree / 2;
            localDensities[v] = if maxLocalEdges > 0 then 
                               localEdges: real / maxLocalEdges: real
                               else 0.0;
        }
    }
    
    // Calculate mean density
    var totalDensity = + reduce localDensities;
    var meanDensity = totalDensity / cluster.size;
    updatedMetrics.edgeDensityDistribution = meanDensity;
    
    // Calculate variance
    var sumSquaredDiff = 0.0;
    forall d in localDensities {
        var diff = d - meanDensity;
        sumSquaredDiff += diff * diff;
    }
    updatedMetrics.localDensityVariance = sumSquaredDiff / cluster.size;
    
    // Calculate density correlation
    updatedMetrics = calculateDensityCorrelation(cluster, localDensities, updatedMetrics);
    
    return updatedMetrics;
}

/* Calculate local edges */
proc calculateLocalEdges(ref localNeighborhood) {
    var localEdges = 0;
    for u in localNeighborhood {
        localEdges += (neighborsSetGraphG1[u] & localNeighborhood).size;
    }
    return localEdges / 2;
}

/* Calculate density correlation using reductions */
proc calculateDensityCorrelation(ref cluster: set(int), 
                                       ref localDensities: [] real, 
                                       metrics) {
    var updatedMetrics = metrics;
    
    // Arrays to store local contributions
    const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
    var localNums: [clusterDomain] real;
    var localDen1s: [clusterDomain] real;
    var localDen2s: [clusterDomain] real;
    
    // Calculate local contributions
    forall v in cluster {
        var v_density = localDensities[v];
        var neighbors = neighborsSetGraphG1[v] & cluster;
        
        // Calculate local values
        localNums[v] = 0.0;
        for u in neighbors {
            localNums[v] += v_density * localDensities[u];
        }
        
        localDen1s[v] = v_density * v_density;
        localDen2s[v] = v_density;
    }
    
    // Use reductions to sum up contributions
    var num = + reduce localNums;
    var den1 = + reduce localDen1s;
    var den2 = + reduce localDen2s;
    
    // Calculate final correlation
    if updatedMetrics.internalEdges > 0 {
        var M = updatedMetrics.internalEdges;
        den2 = (den2 / (2 * M)) ** 2;
        updatedMetrics.densityCorrelation = (num/(2*M) - den2) / 
                                          (den1/(2*M) - den2);
    } else {
        updatedMetrics.densityCorrelation = 0.0;
    }
    
    return updatedMetrics;
}
/* Triangle Counting Implementation with Edge Sampling
   Based on: "Colorful Triangle Counting and a MapReduce Implementation" 
   (Pagh and Tsourakakis, 2012)
   
   Key features:
   - Adaptive sampling based on graph size
   - Hash-based deterministic sampling for parallel efficiency
   - Direct counting for small clusters
   - Memory efficient single-pass implementation
   
   Input: cluster - connected component as set of vertices
   Output: number of triangles in the component
   
   Time complexity: 
   - Small graphs: O(|V| * d^2) where d is average degree
   - Large graphs: O(|V| * d * p) where p is sampling probability
*/

proc calculateTriangles(ref cluster: set(int), debug: bool = true) throws {
    writeln("=====================  calculateTriangles ==================================");
    if cluster.size <= 2 then return 0;
    
    const SAMPLING_THRESHOLD = 10000;
    var triangleCount = 0;
    
    if debug then writeln("Processing cluster of size: ", cluster.size);
    
    if cluster.size > SAMPLING_THRESHOLD {
        var actualEdges = + reduce [v in cluster] (neighborsSetGraphG1[v] & cluster).size / 2;
        var samplingProb = min(1.0, sqrt(actualEdges:real) / cluster.size);
        
        if debug {
            writeln("Actual edges: ", actualEdges);
            writeln("Sampling probability: ", samplingProb);
            writeln("Starting sampling-based counting...");
        }
        
        var sampledEdgeCount = 0;
        forall v in cluster with (+ reduce triangleCount, + reduce sampledEdgeCount) {
            var neighbors = neighborsSetGraphG1[v] & cluster;
            //if debug then writeln("Node ", v, " has ", neighbors.size, " neighbors");
            
            for u in neighbors do
                if v < u {
                    var hash = v * 31 + u;
                    if (hash % 1000000) / 1000000.0 < samplingProb {
                        var commonNeighbors = (neighbors & neighborsSetGraphG1[u]).size;
                        triangleCount += commonNeighbors;
                        sampledEdgeCount += 1;
                        
                        //if debug then writeln("Edge (", v, ",", u, ") sampled, common neighbors: ", commonNeighbors);
                    }
                }
        }
        
        // if debug {
        //     writeln("Sampled edges: ", sampledEdgeCount);
        //     writeln("Raw triangle count: ", triangleCount);
        // }
        
        triangleCount = (triangleCount:real / (samplingProb ** 3)):int;
        
        // if debug then writeln("Scaled triangle count: ", triangleCount);
    } else {
        // if debug then writeln("Using exact counting method");
        
        forall v in cluster with (+ reduce triangleCount) {
            var neighbors = neighborsSetGraphG1[v] & cluster;
            for u in neighbors do
                if v < u {
                    var commonNeighbors = (neighbors & neighborsSetGraphG1[u]).size;
                    triangleCount += commonNeighbors;
                    // if debug then 
                        // writeln("Node pair (", v, ",", u, ") has ", commonNeighbors, " common neighbors");
                }
        }
    }
    
    var finalCount = triangleCount / 3;
    if debug then writeln("Final triangle count: ", finalCount);
    return finalCount;
}
/* Basic spectral bounds based on conductance */
proc calculateSpectralBounds(conductance: real) throws {
    var metrics: spectralMetrics;
    writeln("==================== calculateSpectralBounds ======================");

    // Basic Cheeger inequality bounds
    metrics.lambda2Lower = (conductance * conductance) / 2;
    metrics.lambda2Upper = 2 * conductance;
    metrics.lambda2Estimate = (metrics.lambda2Lower + metrics.lambda2Upper) / 2;
    
    return metrics;
}

/* Basic core numbers calculation */
proc calculateCoreNumbers(ref cluster: set(int)) throws {
    var metrics: coreMetrics;
    writeln("========================== calculateCoreNumbers  ========================");
    // Handle empty or singleton clusters
    if cluster.size <= 1 {
        metrics.coreNumber = 0;
        metrics.coreDensity = 0.0;
        metrics.coreSize = cluster.size;
        return metrics;
    }

    // Create domain and arrays for tracking degrees and shells
    const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
    var degrees: [clusterDomain] int;
    var vertexShells: [clusterDomain] int;  // Store shell number for each vertex
    var currentCore = cluster;
    
    // Initialize degrees
    forall v in cluster with(ref cluster) {
        degrees[v] = calculateClusterDegree(cluster, v);
    }
    
    // Initialize bin-sort arrays for efficient core decomposition
    var maxDegree = max reduce degrees;
    var vertexBins: [0..maxDegree] list(int);  // Vertices binned by degree
    var vertexPos: [clusterDomain] int;        // Position of vertices in their bins
    
    // Populate bins
    for v in cluster {
        var d = degrees[v];
        vertexPos[v] = vertexBins[d].size;
        vertexBins[d].pushBack(v);
    }
    
    // Core decomposition with bin-sorting
    var k = 0;
    var remainingVertices = cluster.size;
    
    while remainingVertices > 0 {
        // Find smallest non-empty bin
        while k <= maxDegree && vertexBins[k].size == 0 do k += 1;
        
        if k > maxDegree then break;
        
        // Process vertices with current minimum degree
        while vertexBins[k].size > 0 {
            var v = vertexBins[k].popBack();
            vertexShells[v] = k;  // Record shell number
            remainingVertices -= 1;
            
            // Update neighbors
            var neighbors = neighborsSetGraphG1[v] & currentCore;
            for u in neighbors {
                var d = degrees[u];
                if d > k {  // Only process neighbors with higher degree
                    // Remove u from its current bin
                    var pos = vertexPos[u];
                    var lastVertex = vertexBins[d].popBack();
                    if lastVertex != u {
                        vertexBins[d].insert(pos, lastVertex);
                        vertexPos[lastVertex] = pos;
                    }
                    
                    // Decrease degree and add to new bin
                    degrees[u] -= 1;
                    vertexPos[u] = vertexBins[d-1].size;
                    vertexBins[d-1].pushBack(u);
                }
            }
        }
    }
    
    // Set basic core metrics
    metrics.coreNumber = max reduce vertexShells;
    var maxCoreVertices: set(int);
    
    for v in cluster {
        if vertexShells[v] == metrics.coreNumber {
            maxCoreVertices.add(v);
        }
    }
    
    metrics.coreSize = maxCoreVertices.size;
    
    // Calculate core density if core exists
    if maxCoreVertices.size > 1 {
        var densityMetrics = calculateInternalDensity(maxCoreVertices);
        metrics.coreDensity = densityMetrics.density;
    } else {
        metrics.coreDensity = 0.0;
    }
    writeln(metrics);
    return metrics;
}


/* Enhanced core analysis implementation */
proc calculateAdvancedCore(ref cluster: set(int)) throws {
    var metrics: coreMetrics;
    
    // Basic initialization and checks
    if cluster.size <= 1 {
        return initializeEmptyCoremetrics();
    }
    
    // Get basic core decomposition first
    metrics = calculateCoreNumbers(cluster);
    
    // Create necessary data structures
    const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
    var vertexShells: [clusterDomain] int;
    var shellMembers: [0..metrics.coreNumber] set(int);
    
    // Perform enhanced core decomposition
    (vertexShells, shellMembers) = calculateShellDecomposition(cluster);
    
    // 1. Core-Periphery Analysis
    metrics = calculateCorePeripheryMetrics(metrics, cluster, vertexShells, shellMembers);
    
    // 2. Shell Analysis
    metrics = calculateShellMetrics(metrics, cluster, vertexShells, shellMembers);
    
    // 3. Hierarchical Analysis
    metrics = calculateHierarchicalMetrics(metrics, cluster, vertexShells, shellMembers);
    
    // 4. Stability Analysis
    metrics = calculateStabilityMetrics(metrics, cluster, vertexShells, shellMembers);
    
    // 5. Quality Analysis
    metrics = calculateQualityMetrics(metrics, cluster, vertexShells, shellMembers);
    
    return metrics;
}

/* Helper function for shell decomposition */
proc calculateShellDecomposition(ref cluster: set(int)) throws {
    const clusterDomain: domain(int,  parSafe=true) = cluster.toArray();
    var vertexShells: [clusterDomain] int;
    var maxShell = 0;
    var remainingVertices = cluster;
    
    // Calculate degrees
    var degrees: [clusterDomain] int;
    forall v in cluster {
        degrees[v] = calculateClusterDegree(cluster, v);
    }
    
    // Bin sort for efficient decomposition
    var maxDegree = max reduce degrees;
    var vertexBins: [0..maxDegree] list(int);
    
    for v in cluster {
        vertexBins[degrees[v]].pushBack(v);
    }
    
    // Decomposition
    var shellMembers: [0..maxDegree] set(int);
    var k = 0;
    
    while remainingVertices.size > 0 {
        var currentShell: set(int);
        var minDegree = max(int);
        
        // Find minimum degree vertices
        for d in 0..maxDegree {
            if vertexBins[d].size > 0 {
                minDegree = d;
                break;
            }
        }
        
        // Process vertices of minimum degree
        var bin = vertexBins[minDegree];
        while bin.size > 0 {
            var v = bin.pop();
            if remainingVertices.contains(v) {
                currentShell.add(v);
                vertexShells[v] = k;
                remainingVertices.remove(v);
                
                // Update neighbors
                var neighbors = neighborsSetGraphG1[v] & remainingVertices;
                for u in neighbors {
                    var oldDeg = degrees[u];
                    degrees[u] -= 1;
                    var newDeg = degrees[u];
                    
                    // Move to new bin
                    if oldDeg != newDeg {
                        vertexBins[oldDeg].remove(u);
                        vertexBins[newDeg].pushBack(u);
                    }
                }
            }
        }
        
        shellMembers[k] = currentShell;
        k += 1;
        maxShell = k;
    }
    
    return (vertexShells, shellMembers);
}

/* Core-Periphery metrics calculation */
proc calculateCorePeripheryMetrics(metrics: coreMetrics, 
                                         ref cluster: set(int),
                                         vertexShells: [] int,
                                         shellMembers: [] set(int)) throws {
    var updatedMetrics = metrics;
    var maxShell = metrics.coreNumber;
    
    // Calculate core strength
    var coreVertices = shellMembers[maxShell];
    var coreEdges = 0;
    var peripheryEdges = 0;
    var crossEdges = 0;
    
    forall v in cluster with (+ reduce coreEdges,
                            + reduce peripheryEdges,
                            + reduce crossEdges) {
        var neighbors = neighborsSetGraphG1[v] & cluster;
        var vInCore = vertexShells[v] == maxShell;
        
        for u in neighbors {
            var uInCore = vertexShells[u] == maxShell;
            if vInCore && uInCore {
                coreEdges += 1;
            } else if !vInCore && !uInCore {
                peripheryEdges += 1;
            } else {
                crossEdges += 1;
            }
        }
    }
    
    coreEdges /= 2;  // Each edge counted twice
    peripheryEdges /= 2;
    
    updatedMetrics.coreStrength = if (coreEdges + crossEdges) > 0 then
                                 coreEdges: real / (coreEdges + crossEdges): real
                                 else 0.0;
    
    updatedMetrics.peripherySize = cluster.size - coreVertices.size;
    
    return updatedMetrics;
}

/* Shell metrics calculation */
proc calculateShellMetrics(metrics: coreMetrics,
                                 ref cluster: set(int),
                                 vertexShells: [] int,
                                 shellMembers: [] set(int)) throws {
    var updatedMetrics = metrics;
    
    // Calculate shell densities and connectivity
    for i in 0..metrics.coreNumber {
        if shellMembers[i].size > 1 {
            var shellDensityMetrics = calculateInternalDensity(shellMembers[i]);
            updatedMetrics.shellDensities[i] = shellDensityMetrics.density;
            
            // Calculate connectivity to next shell if it exists
            if i < metrics.coreNumber {
                var crossEdges = countCrossEdges(shellMembers[i], shellMembers[i+1]);
                var maxPossibleCross = shellMembers[i].size * shellMembers[i+1].size;
                updatedMetrics.shellConnectivity[i] = if maxPossibleCross > 0 then
                                                    crossEdges: real / maxPossibleCross: real
                                                    else 0.0;
            }
        }
    }
    
    return updatedMetrics;
}

/* Hierarchical metrics calculation */
proc calculateHierarchicalMetrics(metrics: coreMetrics,
                                        ref cluster: set(int),
                                        vertexShells: [] int,
                                        shellMembers: [] set(int)) throws {
    var updatedMetrics = metrics;
    
    // Calculate hierarchy balance
    var expectedShellSize = cluster.size: real / (metrics.coreNumber + 1): real;
    var sizeVariance = 0.0;
    
    for i in 0..metrics.coreNumber {
        var diff = shellMembers[i].size: real - expectedShellSize;
        sizeVariance += diff * diff;
    }
    
    updatedMetrics.hierarchyBalance = 1.0 - sqrt(sizeVariance) / cluster.size;
    
    return updatedMetrics;
}

/* Stability metrics calculation */
proc calculateStabilityMetrics(metrics: coreMetrics,
                                     ref cluster: set(int),
                                     vertexShells: [] int,
                                     shellMembers: [] set(int)) throws {
    var updatedMetrics = metrics;
    const SAMPLE_SIZE = min(cluster.size, 100);
    
    // Estimate core stability through random vertex removal
    var stabilityScore = 0.0;
    var trials = 10;
    
    for t in 1..trials {
        var modifiedCluster = cluster;
        var removedVertices = sampleVertices(cluster, SAMPLE_SIZE);
        modifiedCluster -= removedVertices;
        
        var newMetrics = calculateCoreNumbers(modifiedCluster);
        stabilityScore += newMetrics.coreNumber: real / metrics.coreNumber: real;
    }
    
    updatedMetrics.coreStability = stabilityScore / trials;
    
    // Calculate core persistence and overlap
    for k in 0..min(10, metrics.coreNumber) {
        var kCore = getKCore(cluster, k, vertexShells);
        var nextKCore = getKCore(cluster, k+1, vertexShells);
        
        // Persistence: ratio of vertices remaining in higher cores
        updatedMetrics.corePersistence[k] = if kCore.size > 0 then
                                          nextKCore.size: real / kCore.size: real
                                          else 0.0;
        
        // Overlap: Jaccard similarity between consecutive cores
        var intersection = kCore & nextKCore;
        var unions = kCore | nextKCore;
        updatedMetrics.coreOverlap[k] = if unions.size > 0 then
                                       intersection.size: real / unions.size: real
                                       else 0.0;
    }
    
    return updatedMetrics;
}

/* Quality metrics calculation */
proc calculateQualityMetrics(metrics: coreMetrics,
                                   ref cluster: set(int),
                                   vertexShells: [] int,
                                   shellMembers: [] set(int)) throws {
    var updatedMetrics = metrics;
    var maxShell = metrics.coreNumber;
    var coreVertices = shellMembers[maxShell];
    
    // Calculate core cohesion (internal connectivity)
    if coreVertices.size > 1 {
        var cohesionMetrics = calculateInternalDensity(coreVertices);
        updatedMetrics.coreCohesion = cohesionMetrics.density;
    }
    
    // Calculate core separation (external connectivity)
    var internalEdges = 0;
    var externalEdges = 0;
    
    forall v in coreVertices with (+ reduce internalEdges,
                                 + reduce externalEdges) {
        var neighbors = neighborsSetGraphG1[v] & cluster;
        for u in neighbors {
            if coreVertices.contains(u) {
                internalEdges += 1;
            } else {
                externalEdges += 1;
            }
        }
    }
    
    internalEdges /= 2;  // Each internal edge counted twice
    
    updatedMetrics.coreSeparation = if (internalEdges + externalEdges) > 0 then
                                   internalEdges: real / (internalEdges + externalEdges): real
                                   else 0.0;
    
    // Calculate core compactness
    var maxPossibleEdges = (coreVertices.size * (coreVertices.size - 1)) / 2;
    updatedMetrics.coreCompactness = if maxPossibleEdges > 0 then
                                    internalEdges: real / maxPossibleEdges: real
                                    else 0.0;
    
    return updatedMetrics;
}

/* Helper functions */
proc countCrossEdges(ref set1: set(int), ref set2: set(int)) {
    var count = 0;
    forall v in set1 with (+ reduce count) {
        count += (neighborsSetGraphG1[v] & set2).size;
    }
    return count;
}

proc getKCore(ref cluster: set(int), k: int, vertexShells: [] int) {
    var kCore: set(int);
    for v in cluster {
        if vertexShells[v] >= k {
            kCore.add(v);
        }
    }
    return kCore;
}
/* Helper function for core-periphery score calculation */
proc calculateCorePeripheryScore(vertexShells: [] int, maxShell: int, ref cluster: set(int)) throws {
    if maxShell == 0 then return 0.0;
    
    var score = 0.0;
    var totalPairs = 0;
    
    // Calculate score based on shell differences between connected vertices
    forall v in cluster with (+ reduce score, + reduce totalPairs) {
        var neighbors = neighborsSetGraphG1[v] & cluster;
        for u in neighbors {
            var shellDiff = abs(vertexShells[v] - vertexShells[u]);
            score += shellDiff: real / maxShell: real;
            totalPairs += 1;
        }
    }
    
    return if totalPairs > 0 then score / totalPairs else 0.0;
}

/* Helper function for core-degree correlation calculation */
proc calculateCoreDegreeCorrelation(vertexShells: [] int, ref cluster: set(int)) throws {
    var sumX = 0.0, sumY = 0.0, sumXY = 0.0, sumX2 = 0.0, sumY2 = 0.0;
    var n = cluster.size;
    
    forall v in cluster with (
        + reduce sumX, 
        + reduce sumY, 
        + reduce sumXY, 
        + reduce sumX2, 
        + reduce sumY2
    ) {
        var degree = (neighborsSetGraphG1[v] & cluster).size;
        var shell = vertexShells[v];
        
        sumX += degree;
        sumY += shell;
        sumXY += degree * shell;
        sumX2 += degree * degree;
        sumY2 += shell * shell;
    }
    
    var numerator = n * sumXY - sumX * sumY;
    var denominator = sqrt((n * sumX2 - sumX * sumX) * (n * sumY2 - sumY * sumY));
    
    return if denominator != 0.0 then numerator / denominator else 0.0;
}

/* Initialize empty core metrics */
proc initializeEmptyCoremetrics() {
    var metrics: coreMetrics;
    metrics.coreNumber = 0;
    metrics.coreDensity = 0.0;
    metrics.coreSize = 0;
    metrics.corePeripheryScore = 0.0;
    metrics.shellDecomposition = 0;
    metrics.maxCoreSize = 0;
    metrics.coreDegreeCorrelation = 0.0;
    metrics.coreHierarchyDepth = 0;
    return metrics;
}


/* Helper functions for interpretation */
proc interpretCommunityStrength(strength: real) {
    if strength > 0.8 then return "Excellent";
    else if strength > 0.6 then return "Good";
    else if strength > 0.4 then return "Moderate";
    else if strength > 0.2 then return "Weak";
    else return "Very Weak";
}

proc interpretMixingTime(mixingTime: int, clusterSize: int) {
    var logSize = log2(clusterSize: real);
    if mixingTime < logSize then return "Very Fast";
    else if mixingTime < 1.5 * logSize then return "Fast";
    else if mixingTime < 2 * logSize then return "Moderate";
    else return "Slow";
}

proc interpretPartitionResistance(resistance: real) {
    if resistance > 0.8 then return "Very Stable";
    else if resistance > 0.6 then return "Stable";
    else if resistance > 0.4 then return "Moderately Stable";
    else return "Unstable";
}
proc printClusterAnalysis(metrics: clusterMetricsRecord, clusterSize: int) throws {
    writeln("\n=================== Cluster Analysis (Size: ", clusterSize, ") ===================");
    
    writeln("\n1. Basic Connectivity Metrics:");
    writeln("   - Minimum Degree: ", metrics.connectivity.minDegree);
    writeln("   - Maximum Degree: ", metrics.connectivity.maxDegree);
    writeln("   - Average Degree: ", metrics.connectivity.avgDegree);
    //writeln("   - Edge Connectivity Lower Bound: ", metrics.connectivity.edgeConnectivityLowerBound);
    writeln("*/*/ (Mader's Theorem and Its Implications ): Cluster has a ", metrics.connectivity.edgeConnectivityLowerBound, "-edge-connected subgraph. in the best case!");
    writeln("   Advanced Connectivity:");
    writeln("   - Degree Variance: ", metrics.connectivity.degreeVariance);
    writeln("   - Degree Skewness: ", metrics.connectivity.degreeSkewness);
    writeln("   - Assortativity: ", metrics.connectivity.assortativity);
    writeln("   - Effective Diameter: ", metrics.connectivity.effectiveDiameter);
    writeln("   - Average Betweenness: ", metrics.connectivity.avgBetweenness);
    writeln("   - Maximum Betweenness: ", metrics.connectivity.maxBetweenness);
    
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
    writeln("   - Conductance: ", metrics.conductanceData[0]);
    writeln("   - External Edges: ", metrics.conductanceData[1]);
    
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
    writeln("   - k-core number: ", metrics.core.coreNumber);
    writeln("   - Core density: ", metrics.core.coreDensity);
    writeln("   - Core size: ", metrics.core.coreSize);
    writeln("   Advanced Core:");
    writeln("   - Core-Periphery Score: ", metrics.core.corePeripheryScore);
    writeln("   - Max Core Size: ", metrics.core.maxCoreSize);
    writeln("   - Core-Degree Correlation: ", metrics.core.coreDegreeCorrelation);
    writeln("   - Core Hierarchy Depth: ", metrics.core.coreHierarchyDepth);
    
    writeln("\n6. Flow and Boundary Properties:");
    writeln("   Basic Flow:");
    writeln("   - Edge boundary size: ", metrics.flow.edgeBoundarySize);
    writeln("   - Normalized boundary: ", metrics.flow.normalizedBoundarySize);
    writeln("   - Minimum cut estimate: ", metrics.flow.minCutEstimate);
    writeln("   Advanced Flow:");
    writeln("   - Edge Expansion: ", metrics.flow.edgeExpansion);
    writeln("   - Vertex Expansion: ", metrics.flow.vertexExpansion);
    writeln("   - Bottleneck Score: ", metrics.flow.bottleneckScore);
    writeln("   - Flow Centrality: ", metrics.flow.flowCentrality);
    writeln("   - Max Flow-Min Cut: ", metrics.flow.maxFlowMinCut);
    
    writeln("\n7. Robustness Properties:");
    writeln("   Basic Robustness:");
    writeln("   - Estimated diameter: ", metrics.robustness.estimatedDiameter);
    writeln("   - Average path length: ", metrics.robustness.avgPathLength);
    writeln("   - Robustness score: ", metrics.robustness.robustnessScore);
    writeln("   Advanced Robustness:");
    writeln("   - Local Efficiency: ", metrics.robustness.localEfficiency);
    writeln("   - Global Efficiency: ", metrics.robustness.globalEfficiency);
    writeln("   - Vulnerability Score: ", metrics.robustness.vulnerabilityScore);
    writeln("   - Edge Vulnerability: ", metrics.robustness.edgeVulnerability);
    writeln("   - Redundancy: ", metrics.robustness.redundancy);
    writeln("   - Percolation Threshold: ", metrics.robustness.percolationThreshold);

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
    if metrics.conductanceData[0] < 0.1 {
        writeln("   + Excellent cluster separation");
    } else if metrics.conductanceData[0] > 0.7 {
        writeln("   ! Poor cluster separation");
    }
    if metrics.core.coreNumber == 0 {
        writeln("   ! Critical: Disconnected structure");
    } else if metrics.core.corePeripheryScore > 0.8 {
        writeln("   + Strong core-periphery structure");
    }

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
writeln("   - Strength Score: ", (metrics.spectral.communityStrength * 100.0):int / 100.0, 
        " (", interpretCommunityStrength(metrics.spectral.communityStrength), ")");
writeln("   - Internal Communication Speed: ", 
        interpretMixingTime(metrics.spectral.mixingTime, clusterSize));
writeln("   - Structural Stability: ", 
        interpretPartitionResistance(metrics.spectral.partitionResistance));

    // 5. Flow Assessment
    writeln("\n5. Flow Quality:");
    if metrics.flow.bottleneckScore < 0.1 {
        writeln("   ! Significant bottleneck detected");
    }
    if metrics.flow.edgeExpansion > 0.5 {
        writeln("   + Good expansion properties");
    }

    // 6. Robustness Assessment
    writeln("\n6. Robustness Quality:");
    if metrics.robustness.vulnerabilityScore > 0.7 {
        writeln("   ! High vulnerability to node removal");
    }
    if metrics.robustness.localEfficiency > 0.8 {
        writeln("   + Excellent local efficiency");
    }

    // Overall Quality Score
    writeln("\nOverall Cluster Quality Score:");
    var qualityIssues = 0;
    // Connectivity Issues
    if metrics.connectivity.minDegree == 0 || metrics.connectivity.avgDegree < 2 then qualityIssues += 1;
    // Density Issues
    if metrics.density.density < 0.3 then qualityIssues += 1;
    // Structural Issues
    if metrics.conductanceData[0] > 0.5 || metrics.core.coreNumber < 2 then qualityIssues += 1;
    // Spectral Issues
    if metrics.spectral.lambda2Estimate < 0.1 then qualityIssues += 1;
    if (metrics.spectral.communityStrength < 0.3 || 
      metrics.spectral.partitionResistance < 0.2 || 
      metrics.spectral.subcommunityLikelihood > 0.8) {
      qualityIssues += 1;
    }
    // Flow Issues
    if metrics.flow.bottleneckScore < 0.1 then qualityIssues += 1;
    // Robustness Issues
    if metrics.robustness.vulnerabilityScore > 0.7 then qualityIssues += 1;

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


/* Record for storing evaluation results */
record clusterEvaluation {
   var isValid: bool;
   var qualityScore: real;
   var violations: int;
}

/* Calculate both bounds from the paper's inequality */
proc calculateBounds(ref cluster: set(int)) throws {
   writeln("\n================== Calculating Bounds for Cluster ====================");
   writeln("Cluster size: ", cluster.size);
   
   var bounds: (real, real);
   const clusterDomain: domain(int, parSafe=true) = cluster.toArray();
   var externalCutArray: [clusterDomain]int;

   if cluster.size == 0 {
       writeln("Empty cluster detected, returning (0.0, 0.0)");
       return (0.0, 0.0);
   }
   
   // Calculate external cut size
   forall v in cluster with(ref externalCutArray) {
       var neighbors = neighborsSetGraphG1[v];
       var outEdge = neighbors - cluster;
       externalCutArray[v] = outEdge.size;
   }
   var externalCut = + reduce externalCutArray;
   writeln("External cut size: ", externalCut);

   // Left bound calculation
   var leftBound = 0.0;
   if g1.n_vertices == cluster.size {
    writeln(" The cluster is the size of graph! we can say there is no cluster");
    
   } else {
    var leftBound: real = externalCut / (g1.n_vertices - cluster.size): real;
   }

   writeln("Left bound: ", leftBound);

   // Right bound calculation using N-I
   var (minCutValue, cuts) = findAllMinCutsNI(cluster, neighborsSetGraphG1);
   writeln("Minimum cut value: ", minCutValue);
   
   var minPartitionSize = max(int);
   for (cutSet, _) in cuts {
       minPartitionSize = min(minPartitionSize, min(cutSet.size, cluster.size - cutSet.size));
   }
   
   var rightBound = if minPartitionSize > 0 then minCutValue / minPartitionSize: real else 0.0;
   writeln("Right bound: ", rightBound);

   bounds = (leftBound, rightBound);
   return bounds;
}


/* Find valid alpha ranges for all clusters */
proc findAlphaRanges(ref clusters: map(int, set(int))) throws {
   writeln("\n=== Finding Alpha Ranges ===");

   var clustersDomain: domain(int) = clusters.keysToArray();
   var allRanges: [clustersDomain] (real, real);
   
   forall clusterId in clustersDomain {
       writeln("\nProcessing cluster ", clusterId);
       allRanges[clusterId] = calculateBounds(clusters[clusterId]);
       writeln("Range for cluster ", clusterId, ": ", allRanges[clusterId]);
   }

   return allRanges;
}

/* Find overall valid alpha range */
proc findValidAlphaRange(ref ranges: [] (real, real)) {
   writeln("\n=== Finding Valid Alpha Range ===");
   var maxLower = max reduce [r in ranges] r(1);
   var minUpper = min reduce [r in ranges] r(2);
   writeln("Max lower bound: ", maxLower);
   writeln("Min upper bound: ", minUpper);
   return (maxLower, minUpper);
}

/* Evaluate single cluster */
proc evaluateCluster(ref cluster: set(int), alpha: real) throws {
   writeln("\n=== Evaluating Cluster ===");
   writeln("Using alpha: ", alpha);
   
   var evaluation: clusterEvaluation;
   var (leftBound, rightBound) = calculateBounds(cluster);
   
   evaluation.isValid = leftBound <= alpha && alpha <= rightBound;
   evaluation.qualityScore = if rightBound > 0 then (rightBound - leftBound) / rightBound else 0.0;
   
   // Count violations of community property
   evaluation.violations = 0;
   for v in cluster {
       var internalNeigh = neighborsSetGraphG1[v] & cluster;
       var internal = internalNeigh.size;
       var external = neighborsSetGraphG1[v].size - internal;
       if external >= internal {
           evaluation.violations += 1;
           writeln("Violation at node ", v);
       }
   }
   
   writeln("Evaluation results:");
   writeln("- Valid: ", evaluation.isValid);
   writeln("- Quality score: ", evaluation.qualityScore);
   writeln("- Violations: ", evaluation.violations);
   
   return evaluation;
}

/* Find best alpha value */
proc findBestAlpha(ref clusters: [] set(int), alphaRange: (real, real), steps: int = 10) throws {
   writeln("\n=== Finding Best Alpha ===");
   writeln("Alpha range: ", alphaRange);
   writeln("Number of steps: ", steps);
   
   var (minAlpha, maxAlpha) = alphaRange;
   if maxAlpha <= minAlpha {
       writeln("Invalid range detected, returning minAlpha");
       return minAlpha;
   }
   
   var step = (maxAlpha - minAlpha) / steps;
   var bestAlpha = minAlpha;
   var bestScore = 0.0;
   
   for i in 0..steps {
       var currentAlpha = minAlpha + i * step;
       writeln("\nTesting alpha = ", currentAlpha);
       
       var validClusters = 0;
       var totalViolations = 0;
       
       forall c in clusters with (+ reduce validClusters, + reduce totalViolations) {
           var eval = evaluateCluster(c, currentAlpha);
           if eval.isValid then validClusters += 1;
           totalViolations += eval.violations;
       }
       
       var score = validClusters: real / clusters.size - 
                  (totalViolations: real / (g1.n_vertices * clusters.size));
       writeln("Score for alpha ", currentAlpha, ": ", score);
       
       if score > bestScore {
           bestScore = score;
           bestAlpha = currentAlpha;
           writeln("New best alpha found: ", bestAlpha);
       }
   }
   
   writeln("\nBest alpha found: ", bestAlpha);
   writeln("Best score: ", bestScore);
   return bestAlpha;
}

/* Main evaluation function */
proc evaluateClustering(ref clusters: [] set(int)) throws {
   writeln("\n====== Starting Clustering Evaluation ======");
   writeln("Number of clusters: ", clusters.size);
   writeln("Total graph vertices: ", g1.n_vertices);
   
   
   writeln("\n=== Phase 1: Finding Alpha Ranges ===");
   var ranges = findAlphaRanges(clusters);
   
   writeln("\n=== Phase 2: Finding Valid Alpha Range ===");
   var alphaRange = findValidAlphaRange(ranges);
   
   writeln("\n=== Phase 3: Finding Best Alpha ===");
   var bestAlpha = findBestAlpha(clusters, alphaRange);
   
   writeln("\n=== Phase 4: Final Evaluation ===");
   var results: [clusters.domain] clusterEvaluation;
   forall i in clusters.domain {
       writeln("\nEvaluating cluster ", i);
       results[i] = evaluateCluster(clusters[i], bestAlpha);
   }
   
   writeln("\n====== Evaluation Complete ======");
   
   return (bestAlpha, results);
}



    /* Function to calculate the conductance of a cluster */
    proc calculateConductance(ref cluster: set(int)) throws {
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

      return output;
    }// end of calculateConductance
    ////////////////////////////////////////////// find all mincut  ///////////////////////////

    /* Helper function to print graph */
    proc printGraph(members: set(int), adj: map(int, set(int))) throws {
        writeln("Graph:");
        writeln("Vertices: ", members);
        writeln("Edges:");
        for v in members {
            for u in adj[v] {
                if v < u then writeln(v, " -- ", u);
            }
        }
    }
    /* Main Stoer-Wagner implementation */
    proc stoerWagnerMinCut(ref members: set(int), ref adj: map(int, set(int))): (int, set(int), set((int, int))) throws {
        // Special cases
        if members.size == 0 || members.size == 1 {
            return (0, new set(int), new set((int, int)));
        }
        
        var minCutValue = max(int);
        var minCutSet = new set(int);
        var minCutEdges = new set((int, int));

        // Deep copy the adjacency lists
        var adjCopy = new map(int, set(int));
        for v in adj.keys() {
            adjCopy[v] = new set(int);
            adjCopy[v] = adj[v];
        }

        // Keep track of merged vertices
        var mergeMap = new map(int, set(int));
        for v in members {
            mergeMap[v] = new set(int);
            mergeMap[v].add(v);
        }

        // Working set of vertices
        var vertices = new set(int);
        vertices = members;

        writeln("Starting Stoer-Wagner with vertices: ", vertices);
        //writeln("Initial adjacency lists:");
        // for v in adjCopy.keys() {
        //     writeln(v, " -> ", adjCopy[v]);
        // }

        // Main algorithm loop
        while vertices.size > 1 {
            var inA = new set(int);
            var weights = new map(int, int);
            
            // Select first active vertex
            var first = -1;
            for v in vertices {
                first = v;
                break;
            }

            var prev = -1;
            var last = first;
            
            inA.add(first);
            //writeln("\nNew phase starting with first vertex: ", first);

            // Initialize weights
            for v in vertices {
                if v != first {
                    weights[v] = 0;
                    if adjCopy[first].contains(v) {
                        weights[v] = 1;
                    }
                }
            }
            //writeln("Initial weights: ", weights);

            // Main phase loop
            while inA.size < vertices.size {
                var maxWeight = -1;
                var maxVertex = -1;

                for v in vertices {
                    if !inA.contains(v) && weights[v] > maxWeight {
                        maxWeight = weights[v];
                        maxVertex = v;
                    }
                }

                if maxVertex == -1 {
                    writeln("Warning: No more connected vertices found");
                    break;
                }

                prev = last;
                last = maxVertex;
                inA.add(maxVertex);

                //writeln("Added vertex ", maxVertex, " with weight ", maxWeight);
                
                // Update weights
                for v in vertices {
                    if !inA.contains(v) {
                        if adjCopy[maxVertex].contains(v) {
                            weights[v] += 1;
                        }
                    }
                }
                //writeln("Updated weights: ", weights);
            }

            // Build cut set
            var cutSet = new set(int);
            for v in vertices {
                if v != last {
                    cutSet.add(v);
                }
            }

            // Calculate cut weight
            var cutWeight = 0;
            var currentCutEdges = new set((int, int));
            var lastVertices = mergeMap[last];
            var cutSetVertices = new set(int);
            for v in cutSet {
                cutSetVertices |= mergeMap[v];
            }

            // Count edges crossing the cut
            for v in cutSetVertices {
                for u in lastVertices {
                    if adj[v].contains(u) {
                        cutWeight += 1;
                        currentCutEdges.add((min(v,u), max(v,u)));
                    }
                }
            }

            // writeln("\nPhase complete.");
            // writeln("Cut weight: ", cutWeight, ", previous min: ", minCutValue);
            // writeln("Cut set: ", cutSet);

            // Update minimum cut if better
            if cutWeight < minCutValue {
                minCutValue = cutWeight;
                minCutSet.clear();
                minCutSet |= cutSetVertices;
                minCutEdges = currentCutEdges;

                // writeln("\nNew minimum cut found!");
                // writeln("Cut value: ", minCutValue);
                // writeln("Cut set: ", minCutSet);
                // writeln("Cut edges: ", minCutEdges);
            }
            // Merge vertices
            if prev != -1 && last != -1 && prev != last {
                // writeln("\nMerging vertex ", last, " into ", prev);
                // writeln("Before merge adjacency lists:");
                // for v in adjCopy.keys() {
                //     writeln(v, " -> ", adjCopy[v]);
                // }
                
                // Update merge tracking
                mergeMap[prev] |= mergeMap[last];
                mergeMap.remove(last);
                
                // Remove self-loops
                adjCopy[prev].remove(prev);
                adjCopy[prev].remove(last);
                
                // Merge adjacency lists
                for v in adjCopy[last] {
                    if v != prev {
                        adjCopy[prev].add(v);
                        adjCopy[v].remove(last);
                        adjCopy[v].add(prev);
                    }
                }
                
                // Remove merged vertex
                adjCopy.remove(last);
                vertices.remove(last);

                // writeln("\nAfter merge:");
                // writeln("Vertices remaining: ", vertices);
                // writeln("Updated adjacency lists:");
                // for v in adjCopy.keys() {
                //     writeln(v, " -> ", adjCopy[v]);
                // }
                // writeln("Merge map:", mergeMap);
            }
        }

        writeln("\nStoer-Wagner MinCut Final result:");
        writeln("Minimum cut value: ", minCutValue);
        writeln("Cut set: ", minCutSet);
        writeln("Cut edges: ", minCutEdges);

        return (minCutValue, minCutSet, minCutEdges);
    }
    /////////////////////////////////////////Nagamochi-Ibaraki Algorithm//////////////////////////


/* Nagamochi-Ibaraki Algorithm 
    // Phase 1: Forest Decomposition (same as original)
    // Phase 2: Modified Edge Contraction with cut tracking
        // Contract edge from first forest
    // Procedure to build cactus representation 
      // Add edges representing cut relationships
   Main execution
    // 1. Find edge connectivity
    
    // 2. Find all potential minimum cuts through contractions
    
    // 3. Find non-crossing minimum cuts

    
    // 4. Remove duplicate cuts and verify each is minimal
   
    // 5. Build cactus representation (optional)


- FOREST Decomposition
   With simple writeln debugging
   
   
   The key differences from the original algorithm are:

Cut Tracking


Instead of just finding the minimum cut value, we track all cuts of minimum value
We maintain a list of Cut records containing both the vertices and cut value


Modified Contraction Phase


When we find a vertex of minimum degree, we save its component as a potential minimum cut
We still contract edges but keep track of which vertices were merged


Additional Verification


We add a verification phase to ensure each candidate cut is actually minimal
This removes any false positives that might arise during the contraction process


Cactus Representation


Optionally builds a cactus graph representation of all minimum cuts
This is a compact way to represent all minimum cuts
Each cycle in the cactus corresponds to a family of minimum cuts

Key Properties:

Running Time: O(|E| + λ|V|² + αλ|V|)
where:

λ is the edge connectivity
α is the number of minimum cuts
|V| is number of vertices
|E| is number of edges


Space Complexity: O(α|V|)

We need to store all minimum cuts
The cactus representation can be more space-efficient


Correctness:


Finds all minimum cuts, not just one
Each cut returned is guaranteed to be minimal
No minimum cuts are missed

Key Applications:

Network reliability analysis
Clustering with minimum cuts
Finding redundant connections in networks
Network vulnerability analysis
   
   
   
    */

/* Record for edges */
record Edge {
  var u: int;
  var v: int;
  
  proc writeThis(fw) throws {
    fw.write("(", u, ",", v, ")");
  }
}

/* Helper function to create edge */
proc createEdge(u: int, v: int): Edge {
  if u <= v {
    writeln("Creating edge (", u, ",", v, ")");
    return new Edge(u, v);
  } else {
    writeln("Creating edge (", v, ",", u, ") [swapped]");
    return new Edge(v, u);
  }
}
/* New helper function to print working neighbors state */
proc printWorkingNeighbors(workingNeighbors: map(int, set(int)), vertices: set(int)) throws{
  writeln("\nCurrent Working Neighbors State:");
  for v in vertices {
    if workingNeighbors.contains(v) {
      writeln("  Node ", v, " -> ", workingNeighbors[v]);
    }
  }
  writeln();
}

/* Print current state of the decomposition */
proc printDecompositionState(nodeLabels: map(int, int), 
                           scannedNodes: set(int),
                           scannedEdges: set(Edge),
                           forestPartitions: map(Edge, int)) {
  writeln("\nCurrent State:");
  writeln("  Node labels: ", nodeLabels);
  writeln("  Scanned nodes: ", scannedNodes);
  writeln("  Number of scanned edges: ", scannedEdges.size);
  writeln("  Forest partitions: ", forestPartitions);
  writeln();
}

/* Main FOREST decomposition function */
proc FOREST(vertices: set(int)) throws{
  writeln("\n=== Starting FOREST decomposition ===");
  writeln("Input vertices: ", vertices);
  
  var forestPartitions: map(Edge, int);
  var nodeLabels: map(int, int);
  var scannedNodes: set(int);
  var scannedEdges: set(Edge);
  
  // Initialize node labels
  for v in vertices {
    nodeLabels[v] = 0;
    writeln("Initialized node ", v, " with label 0");
  }
  
  var iterCount = 0;
  while scannedNodes.size < vertices.size {
    iterCount += 1;
    writeln("\n--- Iteration ", iterCount, " ---");
    
    // Find unscanned node with largest label
    var maxLabel = -1;
    var selectedNode = -1;
    
    for v in vertices {
      if !scannedNodes.contains(v) {
        if nodeLabels.contains(v) && nodeLabels[v] > maxLabel {
          maxLabel = nodeLabels[v];
          selectedNode = v;
          writeln("Found better node ", v, " with label ", maxLabel);
        }
      }
    }
    
    if selectedNode == -1 {
      writeln("No more unscanned nodes found. Breaking.");
      break;
    }
    
    writeln("Selected node ", selectedNode, " with label ", maxLabel);
    
    // Process neighbors
    var neighs = neighborsSetGraphG1[selectedNode] & vertices;
    writeln("Neighbors of node ", selectedNode, ": ", neighs);
    
    for y in neighs {
      if !scannedNodes.contains(y) {
        var edge = createEdge(selectedNode, y);
        
        if !scannedEdges.contains(edge) {
          var forestNum = nodeLabels[y] + 1;
          forestPartitions[edge] = forestNum;
          nodeLabels[y] = forestNum;
          scannedEdges.add(edge);
          
          writeln("Added edge ", edge, " to forest ", forestNum);
          writeln("Updated label of node ", y, " to ", forestNum);
        } else {
          writeln("Edge ", edge, " already processed");
        }
      }
    }
    
    scannedNodes.add(selectedNode);
    writeln("Marked node ", selectedNode, " as scanned");
    writeln("Progress: ", scannedNodes.size, "/", vertices.size, " nodes processed");
    
    printDecompositionState(nodeLabels, scannedNodes, scannedEdges, forestPartitions);
  }
  
  writeln("\n=== FOREST decomposition completed ===");
  writeln("Final forest partitions:");

  for key in forestPartitions.keysToArray(){
//   for (edge, forestNum) in forestPartitions {
    writeln("  Edge ", key, " -> Forest ", forestPartitions[key]);
  }
          writeln("////////////////// FOREST //////////////////");

  return forestPartitions;
}

/* Helper function to get maximum forest number */
proc getMaxForestNum(forestPartitions: map(Edge, int)): int throws{
  var maxNum = 0;
  writeln("\n=== getMaxForestNum ===");

  for forestNum in forestPartitions.values() {
    maxNum = max(maxNum, forestNum);
  }
  writeln("maximum forest number: ",maxNum );
  return maxNum;
}

/* Helper function to get edges in a specific forest */
proc getEdgesInForest(forestPartitions: map(Edge, int), forestNum: int): set(Edge) throws{
  var edges = new set(Edge);
  writeln("\n=== getEdgesInForest ===");

  for edge in forestPartitions.keysToArray() {
    var num = forestPartitions[edge];
    if num == forestNum {
      edges.add(edge);
    }
  }
  writeln("Found ", edges.size, " edges in forest ", forestNum, ": ", edges);
  return edges;
}

/* Edge contraction phase of Nagamochi-Ibaraki algorithm with debug output */

/* Helper function to merge vertices during contraction */
proc contractEdge(ref vertices: set(int), edge: Edge, ref workingNeighbors: map(int, set(int))) throws {
 writeln("\n=== Starting Edge Contraction ===");
  writeln("Contracting edge ", edge);
  writeln("Initial vertices: ", vertices);
  writeln("Initial working neighbors:");
  printWorkingNeighbors(workingNeighbors, vertices);
  
  var newVertices = vertices;
  
  // Remove endpoints of the edge
  newVertices.remove(edge.u);
  newVertices.remove(edge.v);
  
  // Add new merged vertex (using smaller index as identifier)
  var mergedVertex = min(edge.u, edge.v);
  newVertices.add(mergedVertex);
  
  writeln("Removed vertices ", edge.u, " and ", edge.v);
  writeln("Added merged vertex ", mergedVertex);
  writeln("Resulting vertices: ", newVertices);
  
  return newVertices;
}

/* Helper function to update neighbors after contraction */
proc updateNeighbors(edge: Edge, ref workingNeighbors: map(int, set(int)), ref vertices: set(int)) throws {
  writeln("\n=== Updating Neighbors ===");
  writeln("Processing edge ", edge);
  
  var mergedVertex = min(edge.u, edge.v);
  var otherVertex = max(edge.u, edge.v);
  
  // Get neighbors from working set
  var neighbors1 = workingNeighbors[edge.u];
  var neighbors2 = workingNeighbors[edge.v];
  
  writeln("Current neighbors of ", edge.u, ": ", neighbors1);
  writeln("Current neighbors of ", edge.v, ": ", neighbors2);
  
  // Merge neighbor sets and remove contracted vertices
  var mergedNeighbors = neighbors1 | neighbors2;
  mergedNeighbors.remove(edge.u);
  mergedNeighbors.remove(edge.v);
  
  // Update working neighbors map
  workingNeighbors[mergedVertex] = mergedNeighbors;
  workingNeighbors.remove(otherVertex);
  
  writeln("Updated neighbors for merged vertex ", mergedVertex, ": ", mergedNeighbors);
  printWorkingNeighbors(workingNeighbors, vertices);
}



/* Find minimum degree vertex */
proc findMinDegreeVertex(ref vertices: set(int), ref workingNeighbors: map(int, set(int))) throws {
  writeln("\n=== Finding Minimum Degree Vertex ===");
  var minDegree = max(int);
  var minVertex = -1;
  
  for v in vertices {
    var degree = workingNeighbors[v].size;
    writeln("Vertex ", v, " has degree ", degree, " (neighbors: ", workingNeighbors[v], ")");
    if degree < minDegree {
      minDegree = degree;
      minVertex = v;
      writeln("New minimum found: vertex ", v, " with degree ", degree);
    }
  }
  
  writeln("Selected vertex ", minVertex, " with minimum degree ", minDegree);
  return (minVertex, minDegree);
}

/* Main edge contraction procedure */
proc contractEdgesPhase(ref vertices: set(int)) throws {
  writeln("\n=== Starting Edge Contraction Phase ===");
  writeln("Initial vertices: ", vertices);
  
  // Initialize working neighbors
  var workingNeighbors: map(int, set(int));
  for v in vertices {
    workingNeighbors[v] = neighborsSetGraphG1[v] & vertices;
  }
  writeln("Initial working neighbors:");
  printWorkingNeighbors(workingNeighbors, vertices);
  
  var currentVertices = vertices;
  var minCutValue = max(int);
  var minCutEdges: set(Edge);
  
  while currentVertices.size > 2 {
    writeln("\n--- Processing graph with ", currentVertices.size, " vertices ---");
    
    // Get forest decomposition
    var forests = FOREST(currentVertices);
    var maxForestNum = getMaxForestNum(forests);
    
    // Find minimum degree and update minCut if needed
    var (minVertex, minDegree) = findMinDegreeVertex(currentVertices, workingNeighbors);
    
    if minDegree < minCutValue {
      minCutValue = minDegree;
      writeln("Updated minimum cut value to ", minCutValue);
      
      // Store edges in the cut
      minCutEdges.clear();
      var neighs = workingNeighbors[minVertex];
      for n in neighs {
        minCutEdges.add(createEdge(minVertex, n));
      }
      writeln("Updated minimum cut edges: ", minCutEdges);
    }
    
    // Find edge to contract from first forest
    var firstForestEdges = getEdgesInForest(forests, 1);
    if firstForestEdges.size == 0 {
      writeln("No edges in first forest. Breaking.");
      break;
    }
    
    var idx: int = 0;
    var edgeToContract: Edge;
    for elem in firstForestEdges {
      if idx == 0 then edgeToContract = elem;
      idx += 1;
    }
    writeln("Selected edge for contraction: ", edgeToContract);
    
    // Perform contraction
    currentVertices = contractEdge(currentVertices, edgeToContract, workingNeighbors);
    updateNeighbors(edgeToContract, workingNeighbors, currentVertices);
    
    writeln("State after contraction:");
    writeln("  Vertices: ", currentVertices);
    writeln("  Working neighbors:");
    printWorkingNeighbors(workingNeighbors, currentVertices);
  }
  
  writeln("\n=== Edge Contraction Phase Completed ===");
  writeln("Final minimum cut value: ", minCutValue);
  writeln("Final minimum cut edges: ", minCutEdges);
  
  return (minCutValue, minCutEdges);
}

/* First: Data Structures and Helper Functions */
record Cut {
    var vertices: set(int);  // One side of the cut
    var cutValue: int;      // Size of the cut
    
    proc writeThis(fw) throws {
        fw.write("Cut(vertices: ", vertices, ", value: ", cutValue, ")");
    }
}

/* Track merged vertices during contractions */
record VertexMapping {
    var originalToContracted: map(int, int);  // original vertex -> contracted vertex
    var contractedToOriginal: map(int, set(int));  // contracted vertex -> set of original vertices
    
    proc init() {
        originalToContracted = new map(int, int);
        contractedToOriginal = new map(int, set(int));
    }
    
    /* Initialize with original vertices */
    proc initializeVertices(ref vertices: set(int)) {
        for v in vertices {
            originalToContracted[v] = v;
            contractedToOriginal[v] = new set(int);
            contractedToOriginal[v].add(v);
        }
    }
    
    /* Update mapping when contracting vertices */
    proc mergeVertices(u: int, v: int, mergedVertex: int) throws{
        // Get all original vertices from both u and v
        var originalsU = new set(int);  // Create empty set first
        var originalsV = new set(int);
        
        if contractedToOriginal.contains(u) then
            originalsU = contractedToOriginal[u];
        else
            originalsU.add(u);
            
        if contractedToOriginal.contains(v) then
            originalsV = contractedToOriginal[v];
        else
            originalsV.add(v);
        
        // Create new set of all original vertices for merged vertex
        var mergedOriginals = originalsU | originalsV;
        
        // Update mappings
        for orig in mergedOriginals {
            originalToContracted[orig] = mergedVertex;
        }
        contractedToOriginal[mergedVertex] = mergedOriginals;
        
        // Remove old mappings but keep the merged vertex mapping
        if u != mergedVertex then contractedToOriginal.remove(u);
        if v != mergedVertex then contractedToOriginal.remove(v);
        
        writeln("Merged ", u, " and ", v, " into ", mergedVertex);
        writeln("New mapping for ", mergedVertex, ": ", mergedOriginals);
    }
}
proc findCutComponent(startVertex: int, neighbors: map(int, set(int)), vertices: set(int)): list(set(int)) throws {
    writeln("\n=== Finding Cut Components ===");
    writeln("Start vertex: ", startVertex);
    writeln("All vertices: ", vertices);
    
    var cutComponents: list(set(int));
    var startNeighbors = neighbors[startVertex] & vertices;
    
    // Try combinations with each neighbor
    for n in startNeighbors {
        var cutSide: set(int);
        cutSide.add(startVertex);
        cutSide.add(n);
        
        // Only add if it makes a valid potential cut
        var otherVertices = vertices - cutSide;
        var isConnected = areVerticesConnected(otherVertices, neighbors);
        if isConnected {
            writeln("Found potential cut: ", cutSide);
            cutComponents.pushBack(cutSide);
        }
    }
    
    return cutComponents;
}

// Helper to check if vertices form a connected component
proc areVerticesConnected(vertices: set(int), neighbors: map(int, set(int))): bool throws{
    if vertices.size <= 1 then return true;
    
    var visited: set(int);
    var toVisit: list(int);
    
    // Start with first vertex
    var start = vertices.toArray()[0];
    visited.add(start);
    toVisit.pushBack(start);
    
    while toVisit.size > 0 {
        var current = toVisit.popBack();
        for n in neighbors[current] & vertices {
            if !visited.contains(n) {
                visited.add(n);
                toVisit.pushBack(n);
            }
        }
    }
    
    return visited.size == vertices.size;
}

proc validateCut(ref vertices: set(int), ref cutSide: set(int), ref neighbors: map(int, set(int)), ref minCutValue: int): bool throws {
    writeln("\n=== Validating Cut ===");
    writeln("Cut side: ", cutSide);
    writeln("Other side: ", vertices - cutSide);
    
    if cutSide.size == 0 || cutSide.size == vertices.size {
        writeln("Invalid cut: empty or full set");
        return false;
    }
    
    // Count crossing edges properly
    var crossingEdges = 0;
    for v in cutSide {
        var outsideNeighbors = neighbors[v] & (vertices - cutSide);
        writeln("Vertex ", v, " connects to outside vertices: ", outsideNeighbors);
        crossingEdges += outsideNeighbors.size;
    }
    
    writeln("Total crossing edges: ", crossingEdges);
    
    return crossingEdges == minCutValue;
}
/* Modified contraction phase to track all cuts without duplicate checking */
proc findAllMinCutsContraction(ref vertices: set(int)) throws {
    writeln("\n=== Starting All MinCuts Contraction Phase ===");
    
    var currentVertices = vertices;
    var workingNeighbors: map(int, set(int));
    var vertexMapping = new VertexMapping();
    var allCuts: list(Cut);
    var minCutValue = max(int);
    
    // Initialize
    vertexMapping.initializeVertices(vertices);
    writeln("After initialization - vertexMapping contents:");
    for key in vertexMapping.contractedToOriginal.keysToArray() {
        writeln("  ", key, " -> ", vertexMapping.contractedToOriginal[key]);
    }

    for v in vertices {
        workingNeighbors[v] = neighborsSetGraphG1[v] & vertices;
    }
    writeln("Initial workingNeighbors:");
    for v in vertices {
        writeln("  ", v, " -> ", workingNeighbors[v]);
    }
    
    while currentVertices.size > 2 {
        writeln("\n--- Processing graph with ", currentVertices.size, " vertices ---");
        writeln("Current vertices: ", currentVertices);
        
        var forests = FOREST(currentVertices);
        
        // Find minimum degree vertices
        for v in currentVertices {
            var degree = workingNeighbors[v].size;
            writeln("\nProcessing vertex ", v, " with degree ", degree);
            
            if degree == minCutValue || degree < minCutValue {
                if degree < minCutValue {
                    writeln("Found new minimum cut (degree < minCutValue)");
                    minCutValue = degree;
                    allCuts.clear();  // Only clear for new minimum
                } else {
                    writeln("Found equal minimum cut (degree == minCutValue)");
                }

                // Find all possible cut components
                var cutComponents = findCutComponent(v, workingNeighbors, currentVertices);
                writeln("\nProcessing ", cutComponents.size, " cut components");
                
                // Process each cut component
                for cutComponent in cutComponents {
                    var originalVertices: set(int);
                    
                    writeln("\nDEBUG - Processing cut component:");
                    writeln("Current vertex: ", v);
                    writeln("Cut component: ", cutComponent);

                    // Map contracted vertices back to original vertices
                    for contractedVertex in cutComponent {
                        if vertexMapping.contractedToOriginal.contains(contractedVertex) {
                            originalVertices |= vertexMapping.contractedToOriginal[contractedVertex];
                            writeln("Added original vertices for ", contractedVertex, ": ", 
                                  vertexMapping.contractedToOriginal[contractedVertex]);
                        } else {
                            writeln("WARNING: Contracted vertex ", contractedVertex, " not found in mapping!");
                        }
                    }
                    writeln("Final original vertices: ", originalVertices);

                    // If cut is valid, add it (no duplicate checking)
                    if validateCut(vertices, originalVertices, workingNeighbors, minCutValue) {
                        allCuts.pushBack(new Cut(originalVertices, degree));
                        writeln("Added cut: ", allCuts[allCuts.size-1]);
                    } else {
                        writeln("Cut validation failed - skipping");
                    }
                }
            }
        }
        
        // Contract edge from first forest
        var firstForestEdges = getEdgesInForest(forests, 1);
        if firstForestEdges.size == 0 {
            writeln("No edges in first forest. Breaking.");
            break;
        }
        var idx: int = 0;
        var edgeToContract: Edge;
        for elem in firstForestEdges {
            if idx == 0 then edgeToContract = elem;
            idx += 1;
        }
        writeln("\nContracting edge: ", edgeToContract);
        
        // Perform contraction
        var mergedVertex = min(edgeToContract.u, edgeToContract.v);
        writeln("Will merge into vertex: ", mergedVertex);
        currentVertices = contractEdge(currentVertices, edgeToContract, workingNeighbors);
        vertexMapping.mergeVertices(edgeToContract.u, edgeToContract.v, mergedVertex);
        writeln("Current vertices after contraction: ", currentVertices);
    }
    
    writeln("\n////////////////// findAllMinCutsContraction //////////////////");
    writeln("Final Results:");
    writeln("Number of cuts found: ", allCuts.size);
    writeln("All cuts: ", allCuts);

    return (minCutValue, allCuts);
}

/* Verify if a cut is minimal */
proc verifyMinCut(cut: Cut, workingNeighbors: map(int, set(int)), vertices: set(int)): bool throws{
    // Count edges crossing the cut
    var crossingEdges = 0;
    for v in cut.vertices {
        for n in workingNeighbors[v] {
            if !cut.vertices.contains(n) {
                crossingEdges += 1;
            }
        }
    }
    
    return crossingEdges == cut.cutValue;
}


/* Main function to find all minimum cuts */
proc findAllMinCuts(ref vertices: set(int)) throws {
    writeln("Finding ALL minimum cuts...");
    
    // Find cuts through contractions
    var (minCutValue, candidateCuts) = findAllMinCutsContraction(vertices);
    
    // Initialize working neighbors for verification
    var workingNeighbors: map(int, set(int));
    for v in vertices {
        workingNeighbors[v] = neighborsSetGraphG1[v] & vertices;
    }
    
    // Verify and remove duplicates
    var validatedCuts: list(Cut);
    for cut in candidateCuts {
        if verifyMinCut(cut, workingNeighbors, vertices) {
            validatedCuts.pushBack(cut);
        }
    }
    
   
    writeln("\nFound ", validatedCuts.size, " minimum validated cuts with value ", minCutValue);
    for cut in validatedCuts {
        writeln("  ", cut);
    }
    writeln("////////////////// findAllMinCuts //////////////////");
    return (minCutValue, validatedCuts);
}
    ///////////////////////////////////////findBridgesInCluster////////////////////////////////////////////////////////

    // /* Define the threshold for small subclusters */
    // const threshold = 10;

    /* DFS function implementing Tarjan's Algorithm on the cluster */
    //The time complexity of implementation is O(N + E), where:

    // N is the number of vertices (nodes) in the cluster.
    // E is the number of edges within the cluster.
    proc DFS(u: int, parentNode: int, ref members: set(int),
            ref disc: [?D1] int, ref low: [?D2] int,
            ref subtree_size: [?D3] int, ref bridges: list((int, int)),
            ref time: int, const total_nodes: int, const threshold:int,
            ref min_diff: int, ref best_bridge: (int, int, int, int),
            ref parent: [?D4] int) {

        time += 1;
        disc[u] = time;
        low[u] = time;
        subtree_size[u] = 1;                       // Initialize subtree size
        parent[u] = parentNode;                    // Record the parent node

        // Access neighbors within the cluster
        var neig = neighborsSetGraphG1[u];
        var neighbors = members & neig; //neighbors are in cluster

        for v in neighbors {
            if v == parentNode {
                continue;                           // Skip the parent node
            }
            if disc[v] == -1 {
                //DFS(v, u, members, disc, low, subtree_size, bridges, time, total_nodes);
                DFS(v, u, members, disc, low, subtree_size, bridges, time, total_nodes, threshold, min_diff, best_bridge, parent);

                low[u] = min(low[u], low[v]);
                subtree_size[u] += subtree_size[v];  // Update subtree size

                // Check for bridge
                if low[v] > disc[u] {
                    // Edge (u, v) is a bridge
                    var component_size_v = subtree_size[v];
                    var component_size_u = total_nodes - subtree_size[v];

                    // Compute the absolute difference
                    var diff = abs(component_size_u - component_size_v);

                    // Update min_diff and best_bridge if this bridge gives a smaller difference
                    if diff < min_diff {
                        min_diff = diff;
                        best_bridge = (u, v, component_size_u, component_size_v);
                    }
                    // Check if one component is a small subcluster
                    if component_size_v <= threshold || component_size_u <= threshold {
                      //writeln("(",u," ,",v,") added. component_size_u: ", component_size_u, " component_size_v: ", component_size_v);
                        bridges.pushBack((u, v));
                    }
                }
            } else {
                low[u] = min(low[u], disc[v]);
            }
        }
    }

    /* Function to collect nodes in a component after removing the bridge */
    proc collectComponent(u: int, ref members: set(int), ref component: set(int), 
                             const excludeNode: int, ref visited: [?D1] bool) {
        component.add(u);
        visited[u] = true;
        var neig = neighborsSetGraphG1[u];
        var neighbors = members & neig;

        for v in neighbors {
            if v == excludeNode {
                continue; // Skip the bridge edge
            }
            if !visited[v] {
                collectComponent(v, members, component, excludeNode, visited);
            }
        }
    }// end of collectComponent

    /* Function to find bridges and small subclusters in the cluster */
    proc findBridgesInCluster(ref members: set(int)) {
        const total_nodes = members.size;  // Declare total_nodes here
        const memberDomain: domain(int) = members.toArray();
        var disc: [memberDomain] int = -1;
        var low : [memberDomain] int = -1;
        var subtree_size: [memberDomain] int = 0;
        var bridges: list((int, int));
        var parent: [memberDomain] int = -1; // Array to store parent of each node
        var time = 0;
        const threshold = members.size;  // find a way to set the threshold. square root of m?

        // Variables to keep track of the minimum difference and the best bridge
        var min_diff = total_nodes;
        var best_bridge: (int, int, int, int) = (-1, -1, -1, -1); // (u, v, component_size_u, component_size_v)

        // Call DFS for each unvisited vertex in the cluster
        for u in members {
            if disc[u] == -1 {
                //DFS(u, -1, members, disc, low, subtree_size, bridges, time, total_nodes, threshold = 10);
                DFS(u, -1, members, disc, low, subtree_size, bridges, time, total_nodes, threshold, min_diff, best_bridge, parent);

            }
        }

        // Output the bridge with the minimum difference
        if best_bridge(0) != -1 {
            writeln("\nThe best bridge in this cluster is between ", best_bridge(0), " and ", best_bridge(1));
            writeln("Component sizes are ", best_bridge(2), " and ", best_bridge(3));
            //writeln("Minimum size difference is ", min_diff);
                    
            // Collect nodes in the component containing best_bridge(1)
            var component_v = new set(int);
            var visited: [memberDomain] bool = false;

            collectComponent(best_bridge(1), members, component_v, best_bridge(0), visited);

            // The other component is the remaining nodes
            var component_u = members - component_v;

            writeln("Nodes in component containing ", best_bridge(1), ": ", component_v);
            writeln("Nodes in component containing ", best_bridge(0), ": ", component_u);

        } else {
            writeln("\nNo bridges found.");
        }
    }
///////////////////////////////////////////////////////////////////////////////////////////////

    /* Recursive method that processes a given set of vertices (partition), denotes if it is 
       well-connected or not, and if not calls itself on the new generated partitions. */
    proc wccRecursiveChecker(ref vertices: set(int), id: int, depth: int) throws {
      writeln("*****************wccRecursiveChecker called***********************");
      writeln("****** Let's check the cluster METRICS: \n");
      //calculateConductance(vertices);
      var (src, dst, mapper) = getEdgeList(vertices);

      // If the generated edge list is empty, then return.
      if src.size < 1 then return;

      var n = mapper.size;
      var m = src.size;

      var partitionArr: [{0..<n}] int;
      var cut = c_computeMinCut(partitionArr, src, dst, n, m);
      writeln("cluster ",id, " passed to Viecut and cut_size is: ", cut);

      var criterionValue = criterionFunction(vertices.size, connectednessCriterionMultValue):int;
      if cut > criterionValue { // Cluster is well-connected.
        var currentId = globalId.fetchAdd(1);
      writeln("$$$$$$ cluster ",id," with currentId " ,currentId," at depth ", depth," with cut ", cut, " is well Connected. ", "memebers are: ", vertices);

        if outputType == "debug" then writeClustersToFile(vertices, id, currentId, depth, cut);
        else if outputType == "during" then writeClustersToFile(vertices, currentId);
        for v in vertices {
          finalVertices.pushBack(v);
          finalClusters.pushBack(currentId);
        }
        if logLevel == LogLevel.DEBUG {
          var outMsg = "Cluster " + id:string + " with depth " + depth:string + " and cutsize " 
                    + cut:string + " is well-connected with " + vertices.size:string + " vertices.";
          wccLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
        return;
      }
      else { // Cluster is not well-connected.
        var cluster1, cluster2 = new set(int);
        
        // Separate vertices into two partitions.
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.add(mapper[v]);
          else cluster2.add(mapper[v]);
        }
        
        // Make sure the partitions meet the minimum size denoted by postFilterMinSize.
        if cluster1.size > postFilterMinSize {
        //writeln("//////before clusterC2D///////// ");
        writeln("cluster1(",id,")"," with size: ", cluster1.size, " created!"," members: ", cluster1);
        //calculateConductance(cluster1);
        
        var inPartition = cluster1;
        //var inPartition = kCoreDecomposition(cluster1, 2);

        //var inPartition = removeDegreeOne(cluster1);
          //var inPartition = clusterC2D(cluster1);

        writeln("cluster1(",id,")"," with size: ", inPartition.size);
        //calculateConductance(inPartition);



          wccRecursiveChecker(inPartition, id, depth+1);
        }
        if cluster2.size > postFilterMinSize {
        writeln("cluster2(",id,")"," with size: ", cluster2.size, " created!"," members: ", cluster2);
        //calculateConductance(cluster2);
        var outPartition =cluster2;
        //var outPartition = kCoreDecomposition(cluster2, 2);

        //var outPartition = removeDegreeOne(cluster2);
          //var outPartition = clusterC2D(cluster2);

        writeln("cluster2(",id,")"," with size: ", outPartition.size);
        //calculateConductance(outPartition);
          wccRecursiveChecker(outPartition, id, depth+1);
        }
      }
      return;
    }

/* Helper to print cluster structure */
proc printClusterStructure(ref vertices: set(int), workingNeighbors: map(int, set(int))) throws{
  writeln("Cluster edge structure:");
  for v in vertices {
    writeln("Node ", v, " connects to: ", workingNeighbors[v]);
  }
}

/* Test FOREST decomposition */
proc testForestDecomposition(ref vertices: set(int)) throws {
  writeln("\n=== Testing FOREST Decomposition ===");
  
  var forests = FOREST(vertices);
  
  writeln("\nForest Decomposition Results:");
  var maxForests = getMaxForestNum(forests);
  writeln("Number of forests: ", maxForests);
  
  // Print edges in each forest
  for i in 1..maxForests {
    var edges = getEdgesInForest(forests, i);
    writeln("Forest ", i, ": ", edges);
  }
  
  return forests;
}

/* Test edge contraction */
proc testEdgeContraction(ref vertices: set(int)) throws {
  writeln("\n=== Testing Edge Contraction ===");
  
  // Initialize working neighbors
  var workingNeighbors: map(int, set(int));
  for v in vertices {
    workingNeighbors[v] = neighborsSetGraphG1[v] & vertices;
  }
  
  // Print initial structure
  writeln("\nInitial graph structure:");
  printClusterStructure(vertices, workingNeighbors);
  
  // Run contraction phase with working neighbors
  var (cutValue, cutEdges) = contractEdgesPhase(vertices);
  
  writeln("\nEdge Contraction Results:");
  writeln("Minimum cut value: ", cutValue);
  writeln("Minimum cut edges: ", cutEdges);
  
  return (cutValue, cutEdges);
}

/* Main test runner */
proc runAllTests(ref vertices: set(int)) throws {
  writeln("Starting Nagamochi-Ibaraki Algorithm Tests");
  writeln("=========================================");
  
  // Print initial cluster information
  writeln("Initial cluster: ", vertices);
  var initialNeighbors: map(int, set(int));
  for v in vertices {
    initialNeighbors[v] = neighborsSetGraphG1[v] & vertices;
  }
  printClusterStructure(vertices, initialNeighbors);
  
  // Test FOREST decomposition
  writeln("\nStep 1: Testing FOREST Decomposition");
  var forests = testForestDecomposition(vertices);
  
  // Test edge contraction
  writeln("\nStep 2: Testing Edge Contraction");
  var (cutValue, cutEdges) = testEdgeContraction(vertices);
  
  // Print final results
  writeln("\nFinal Results Summary");
  writeln("====================");
  var maxForests = getMaxForestNum(forests);
  writeln("1. Found ", maxForests, " forests");
  writeln("2. Minimum cut value: ", cutValue);
  writeln("3. Cut edges: ", cutEdges);
  
  // Verify results
  var verificationPassed = true;
  if cutValue > maxForests {
    writeln("\nWARNING: Cut value greater than number of forests!");
    verificationPassed = false;
  }
  
  var remainingVertices = vertices;
  for edge in cutEdges {
    if !initialNeighbors[edge.u].contains(edge.v) {
      writeln("\nWARNING: Cut edge (", edge.u, ",", edge.v, ") not in original graph!");
      verificationPassed = false;
    }
  }
  
  if verificationPassed {
    writeln("\nAll verification checks passed!");
  }
}

/* Optional: Add helper to run specific test cases */
proc runTestCase(testName: string, vertices: set(int)) throws {
  writeln("\nRunning test case: ", testName);
  writeln("-*-*-*-*-*-*-*-*-*-*");
  writeln("Testing cluster with vertices: ", vertices);
  runAllTests(vertices);
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
      
      // for key in originalClusters.keysToArray() {
      //   writeln("key: ",key,"originalClusters.size: ", originalClusters.size," cluster memebers: ", originalClusters);
      // }
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
        writeln("-*-*-*-*-*-*-*-*-*-*at the beginning for cluster(",key,")"," and has ", clusterToAdd);
        //calculateConductance(clusterToAdd);
        // findBridgesInCluster(clusterToAdd);
        //findAllMinCutsInCluster(clusterToAdd);
        //testStoerWagner();
        //runAllTests();
        //testWeightedStoerWagner();
        //testStoerWagner();
        //if key == 0 then testStoerWagner();
        // if key == 0{
        //   writeln("we are here");
        //   testNagamochiIbaraki();
        // }
        writeln("current cluster: ",clusterToAdd );
        writeln("Cluster edge structure:");
        for v in clusterToAdd {
            var neighbors = neighborsSetGraphG1[v] & clusterToAdd;
            writeln("Node ", v, " connects to: ", neighbors);
        }
        //var metrics = analyzeCluster(clusterToAdd);
        //calculateBetweennessCentrality(clusterToAdd,clusterToAdd);
// runAllTests(clusterToAdd);

    var (minCutValue, allCuts) = findAllMinCuts(clusterToAdd);
    
    writeln("Minimum cut value: ", minCutValue);
    writeln("Found ", allCuts.size, " minimum cuts:");
    for cut in allCuts {
        writeln(cut);
    }
        //wccRecursiveChecker(clusterToAdd, key, 0);
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