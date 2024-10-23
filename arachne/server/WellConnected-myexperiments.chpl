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
  use DistributedDeque;
  use CTypes;

  // Arachne modules.
  use GraphArray;
  use Utils;
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;

  // C header and object files.
  require "viecut_helpers/computeMinCut.h", 
          "viecut_helpers/computeMinCut.o",
          "viecut_helpers/logger.cpp.o";
          // "leiden_helpers/runLeiden.h",
          // "leiden_helpers/runLeiden.o";
  
  extern proc c_computeMinCut(partition_arr: [] int, src: [] int, dst: [] int, n: int, m: int): int;
  //  extern proc c_runLeiden(partition_arr: [] int,
  //                    src:[] int,
  //                    dst: []int,
  //                    n: int,
  //                    m: int,
  //                    partitionType: c_ptrConst(c_char),
  //                    resolution: real,
  //                    randomSeed: int,
  //                    iterations: int,
  //                    const original_node_ids: []int);

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
    //writeln("size.read(): ", size.read());
    return size.read();
  }

  proc runWCC (g1: SegGraph, st: borrowed SymTab, 
               inputcluster_filePath: string, outputPath: string, outputType: string, functionType: string) throws {
    var srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    var dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    var segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    var nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;
    var neighborsSetGraphG1 = toSymEntry(g1.getComp("NEIGHBORS_SET_SDI"), set(int)).a;
    
    var finalVertices = new list(int, parSafe=true);
    var finalClusters = new list(int, parSafe=true);
    var globalId:atomic int = 0;
    var functionTypePassed = if functionType != "none" then functionType:int else 10;
    
    writeln("functionType:", functionType);
    writeln("functionTypePassed:", functionTypePassed);

    writeln("/////////////////////runLeiden Called//////////////////////////////////");
    const src1: [0..77] int = [
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // Edges involving node 1
    2, 2, 2, 2,                         // Edges involving node 2
    3, 3, 3, 3,                         // Edges involving node 3
    4, 4, 4, 4,                             // Edges involving node 4
    5, 5, 5,                             // Edges involving node 5
    6, 6, 6,                             // Edges involving node 6
    7, 7,                             // Edges involving node 7
    9, 9, 9, 9,                            // Edges involving node 9
    10, 10, 10,                          // Edges involving node 10
    11, 11, 11,                              // Edges involving node 11
    12, 12,                              // Edges involving node 12
    13,                               // Edges involving node 13
    15,                               // Edges involving node 15
    16, 17, 17, 18, 19,                      // Edges involving nodes 16-19
    21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, // Edges involving node 21
    22, 22, 22, 22,                      // Edges involving node 22
    23, 23, 23,                          // Edges involving node 23
    24, 24,                              // Edges involving node 24
    25,                                  // Edge involving node 25
    26, 26, 26, 26, 26, 26       // Remaining edges
];

    const dst1: [0..77] int=  [
    2, 3, 4, 5, 6, 7, 8, 11, 12, 13, 17, // Edges involving node 1
    3, 4, 8,                                // Edges involving node 2
    14, 4, 8,                                // Edges involving node 3
    10, 14, 8,                                   // Edges involving node 4
    10, 12, 14,
    8, 11, 17,8,11,17,8,17,11,12,13,17,
12,13,17,12,13,17,13,17,17,18,18,18,19,19,20,22,23,24,25,26,27,28,29,30,
31,32,33,23,24,25,26,24,25,26,25,26,26,27,28,29,30,31,34

];
var partition_arr:[0..34] int = -1;
var original_node_ids:[0..34] int = 1..33;

    //c_runLeiden(partition_arr, src1, dst1, 34, 78, "Modularity", 0.001, 42, 100, original_node_ids);
    writeln("partition_arr: ", partition_arr);
    writeln("/////////////////////runLeiden Ended//////////////////////////////////");
///////////////////////////////////////Leiden//////////////////////////////////////////////////////////

/*
    // ----- Parameters -----
    var randomSeed = 42;                       // Seed for reproducibility
    var rng = new randStream(randomSeed);      // Random number generator
    var resolution = 1.0;                      // Resolution parameter for Modularity or CPM
    var partitionType = "Modularity";          // Partition type ("Modularity", "CPM", or "RBConfiguration")

    // Edge weights (assuming unweighted graph; all weights are 1.0)
    var weights: [0..g1.n_edges-1] real = 1.0;

    // Adjacency list and corresponding edge weights for each vertex
    var adjList: [0..g1.n_vertices-1] list(int);         // Adjacency list
    var adjWeights: [0..g1.n_vertices-1] list(real);     // Edge weights in adjacency list

    // Modularity-related metrics
    var communityInternalWeight: [0..g1.n_vertices-1] real;  // Sum of weights of edges inside the community
    var communityTotalWeight: [0..g1.n_vertices-1] real;     // Total weight of edges connected to the community
    var nodeWeightedDegree: [0..g1.n_vertices-1] real;               // Weighted degree of each node

    // Union-Find structure for community refinement
    var parent: [0..g1.n_vertices-1] int;                    // Parent array for Union-Find

// ----- Part 1: Build Adjacency List -----

// Build adjacency list from src[], dst[], and weights[] arrays AND Initialize the adjacency list and adjacency weights

// ----- Part 2: Modularity Optimization -----

    // Initialize modularity-related metrics
    proc initializeModularity(community: [] int) {
      // Reset arrays to zero
      communityInternalWeight = 0.0;
      communityTotalWeight = 0.0;
      nodeWeightedDegree = 0.0;

      var totalEdgeWeight = 0.0;

      // Compute node degrees and total edge weight
      forall vertex in 0..g1.n_vertices-1 {
        var deg = 0.0;
        const ref neighbors = neighborsSetGraphG1[vertex];

        for elem in neighbors { //Edge Weights for Node
          deg += getEdgeSrcDstWeight(vertex, elem);
        }
        nodeWeightedDegree[i] = deg;
        totalEdgeWeight += deg;
      }
      totalEdgeWeight /= 2.0;  // Each edge is counted twice in undirected graphs

      // Compute community metrics
      for node in 0..g1.n_vertices-1 {
        var comm = community[node];
        communityTotalWeight[comm] += nodeWeightedDegree[node];

        var idx = 0;
        for neighbor in adjList[node] {
          var weight = adjWeights[node][idx];
          if community[neighbor] == comm {
            communityInternalWeight[comm] += weight;
          }
          idx += 1;
        }
      }

  // Since each internal edge is counted twice, divide by 2
  forall comm in 0..numVertices-1 {
    communityInternalWeight[comm] /= 2.0;
  }
}

// Calculate the delta modularity (or other quality function) for moving a node to a new community
proc deltaQuality(node: int, currentCommunity: int, newCommunity: int, community: [] int, adjList: [] list(int), adjWeights: [] list(real), totalEdgeWeight: real): real {
  var nodeDeg = nodeDegree[node];

  // Compute k_i_in: sum of weights from node to the new community
  var k_i_in = 0.0;
  var idx = 0;
  for neighbor in adjList[node] {
    if community[neighbor] == newCommunity {
      k_i_in += adjWeights[node][idx];
    }
    idx += 1;
  }

  // Modularity quality function calculation
  if partitionType == "Modularity" {
    var sumTotC = communityTotalWeight[newCommunity];
    var deltaQ = (k_i_in - (nodeDeg * sumTotC) / (2.0 * totalEdgeWeight)) * (1.0 / totalEdgeWeight);
    return deltaQ;
  } else {
    halt("Partition type not implemented.");
  }
}

// Update community and node metrics after a node move
proc updateCommunityMetrics(node: int, currentCommunity: int, newCommunity: int, community: [] int, adjList: [] list(int), adjWeights: [] list(real)) {
  var nodeDeg = nodeDegree[node];

  // Update the total weight for both communities
  communityTotalWeight[currentCommunity] -= nodeDeg;
  communityTotalWeight[newCommunity] += nodeDeg;

  // Update internal weights for both communities
  var idx = 0;
  for neighbor in adjList[node] {
    var weight = adjWeights[node][idx];
    if community[neighbor] == currentCommunity {
      communityInternalWeight[currentCommunity] -= weight;
    }
    if community[neighbor] == newCommunity {
      communityInternalWeight[newCommunity] += weight;
    }
    idx += 1;
  }
}

// Perform modularity (or quality function) optimization by moving nodes between communities
proc optimizeModularity(community: [] int, adjList: [] list(int), adjWeights: [] list(real), rng: RandStream, totalEdgeWeight: real) {
  var improvement = true;

  // Create a list of node indices to shuffle
  var nodes: [0..numVertices-1] int = [i in 0..numVertices-1] i;

  // Iterate until no improvement is found
  while improvement {
    improvement = false;

    // Shuffle the node indices to randomize traversal
    rng.shuffle(nodes);

    // Loop over all shuffled nodes
    forall node in nodes {
      var currentCommunity = community[node];
      var bestCommunity = currentCommunity;
      var bestGain = 0.0;

      // Identify neighboring communities
      var neighboringCommunities = new set(int);
      var idx = 0;
      for neighbor in adjList[node] {
        neighboringCommunities.add(community[neighbor]);
        idx += 1;
      }

      // Try moving the node to each neighboring community
      for newCommunity in neighboringCommunities {
        if newCommunity == currentCommunity then continue;

        var gain = deltaQuality(node, currentCommunity, newCommunity, community, adjList, adjWeights, totalEdgeWeight);
        if gain > bestGain {
          bestGain = gain;
          bestCommunity = newCommunity;
        }
      }

      // Move the node to the best community if it improves modularity
      if bestCommunity != currentCommunity {
        updateCommunityMetrics(node, currentCommunity, bestCommunity, community, adjList, adjWeights);
        community[node] = bestCommunity;
        improvement = true;
      }
    }
  }
}

// ----- Part 3: Community Refinement (Union-Find) -----

// Union-Find 'find' operation with path compression
proc find(x: int): int {
  if parent[x] != x then
    parent[x] = find(parent[x]);  // Path compression
  return parent[x];
}

// Union operation to merge two communities
proc union(x: int, y: int) {
  var rootX = find(x);
  var rootY = find(y);
  if rootX != rootY then
    parent[rootX] = rootY;
}

// Initialize the Union-Find structure
proc initializeUnionFind() {
  forall i in 0..numVertices-1 {
    parent[i] = i;
  }
}

// Refine communities using Union-Find to ensure connectivity
proc refineCommunities(community: [] int, adjList: [] list(int)) {
  initializeUnionFind();

  // Merge nodes in the same community
  forall node in 0..numVertices-1 {
    var nodeComm = community[node];
    for neighbor in adjList[node] {
      if community[neighbor] == nodeComm {
        union(node, neighbor);
      }
    }
  }

  // Reassign nodes based on the Union-Find parent
  forall node in 0..numVertices-1 {
    community[node] = find(node);
  }
}

// ----- Part 4: Community Aggregation -----

// Aggregate nodes into super-nodes after refinement
proc aggregateCommunities(community: [] int, src: [] int, dst: [] int, weights: [] real): (list(int), list(int), list(real)) {
  var newSrc = new list(int);
  var newDst = new list(int);
  var newWeights = new list(real);

  // Map to store aggregated edge weights between communities
  var edgeMap = new associative dom((int, int));

  for i in 0..src.size-1 {
    var srcComm = community[src[i]];
    var dstComm = community[dst[i]];
    var weight = weights[i];

    // Edge between communities (could be self-loop)
    var edge = (srcComm, dstComm);

    // Aggregate weights of parallel edges
    if edgeMap.member(edge) {
      edgeMap[edge] += weight;
    } else {
      edgeMap.add(edge, weight);
    }
  }

  // Build new src, dst, and weights arrays from the edge map
  for (edge, weight) in edgeMap {
    newSrc.append(edge(0));
    newDst.append(edge(1));
    newWeights.append(weight);
  }

  return (newSrc, newDst, newWeights);
}
    // Assuming weights are provided; if not, default to 1 for unweighted graphs
    proc getEdgeIndexWeight(edgeIndex: int): real {
      // If the graph is unweighted, return 1.0 for all edges
      return 1.0;
    }    
    
    proc getEdgeSrcDstWeight(src: int, dst: int): real {
      // If the graph is unweighted, return 1.0 for all edges
      return 1.0;
    }
// ----- Part 5: Leiden Algorithm Iteration -----

    // Full Leiden algorithm combining all steps
    proc leidenAlgorithm( weights: [] real, numIterations: int, resolution: real, partitionType: string, randomSeed: int) {
      
      // Initialize random number generator
      var rng = new RandStream(randomSeed);

      // Compute total edge weight
      var totalEdgeWeight = 0.0;
      for edgeIndex in 0..g1.n_edges {
        totalEdgeWeight += getEdgeIndexWeight(edgeIndex);
      }

      for iteration in 1..numIterations {
        writeln("Iteration: ", iteration);

        // Step 1: Initialize each node to its own community
        var community: [0..g1.n_vertices-1] int = 0..g1.n_vertices;

        // Step 2: Initialize modularity metrics
        initializeModularity(community);

        // Step 3: Perform modularity optimization
        optimizeModularity(community, adjList, adjWeights, rng, totalEdgeWeight);

        // Step 4: Refine communities to ensure connectivity
        refineCommunities(community, adjList);

        // Step 5: Aggregate communities into super-nodes
        var (newSrc, newDst, newWeights) = aggregateCommunities(community, src, dst, weights);

        // Step 6: Check for convergence (termination condition)
        if newSrc.size == src.size && newDst.size == dst.size {
          writeln("No further improvement. Algorithm has converged.");
          break;
        }

    // Update src, dst, and weights for the next iteration
    src = newSrc;
    dst = newDst;
    weights = newWeights;

    // Update numVertices and numEdges based on new communities
    numVertices = community.unique().size;
    numEdges = src.size;

    // Rebuild adjacency list for the new graph
    adjList = [0..numVertices-1] list(int);
    adjWeights = [0..numVertices-1] list(real);
    buildAdjList(src, dst, weights, adjList, adjWeights);
  }
}

// Example of running the Leiden algorithm with custom parameters
leidenAlgorithm(src, dst, weights, numIterations=10, resolution=1.0, partitionType="Modularity", randomSeed=42);
*/

///////////////////////////////////////End of Leiden///////////////////////////////////////////////////
    var clusterArrtemp = wcc(g1);
    writeln("**********************************************************we reached here");
    //writeln("functionTypePassed:", functionTypePassed);
    const ref  clusterArr = clusterArrtemp; //cluster id
    
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
          if clusterID == 38{
            writeln("originalNode(",originalNode,")", "mapped to:",idx );
          }
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
          else writeln("originalNode which is not in graph: ", originalNode);
        }
      }
      reader.close();
      file.close();
      writeln("Number of clusters found: ", clusters.size);
      
      return clusters;
    }


 

    /* Returns the sorted and deduplicated edge list for a given set of vertices. */
    proc getEdgeList(ref vertices: set(int)) throws {
      // Initialize lists to collect edges
      var srcList = new list(int, parSafe=true);
      var dstList = new list(int, parSafe=true);

      // Map to assign new indices to vertices (mapper)
      var mapper = new map(int, int);
      var reverseMapper = new map(int, int); // For reverse mapping
      var idx = 0;
      for v in vertices {
        mapper[v] = idx;
        reverseMapper[idx] = v;
        idx += 1;
      }
      // Collect edges within the cluster
      for u in vertices {
        const ref neighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u + 1]];
        for v in neighbors {
          if mapper.contains(v) {
            srcList.pushBack(mapper[u]);
            dstList.pushBack(mapper[v]);
          }
        }
      }      
      // // Collect edges within the cluster
      // forall u in vertices with (ref srcList, ref dstList) {
      //   const ref neighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u + 1]];
      //   forall v in neighbors with (ref srcList, ref dstList){
      //     if mapper.contains(v) {
      //       srcList.pushBack(mapper[u]);
      //       dstList.pushBack(mapper[v]);
      //     }
      //   }
      // }
      // Convert lists to arrays
      var src = srcList.toArray();
      var dst = dstList.toArray();

      // Sort the edges
      var (sortedSrc, sortedDst) = sortEdgeList(src, dst);

      // Remove duplicate edges
      var (uniqueSrc, uniqueDst) = removeMultipleEdges(sortedSrc, sortedDst);

      // Create mapper array (original vertex IDs)
      var n = mapper.size;
      var mapperArray:[0..n - 1] int;

      for i in reverseMapper.keysToArray() {
        var originalV = reverseMapper[i];
        mapperArray[i] = originalV;
      }

      return (uniqueSrc, uniqueDst, mapperArray);
    }


   // Define a custom comparator record
    record TupleComparator {
        proc compare(a: (int, int), b: (int, int)) {
            if a(0) != b(0) then
                return a(0)-b(0);
            else
                return a(1)-b(1);
        }
    }
    /* Function to sort edge lists based on src and dst nodes */
    proc sortEdgeList(ref src: [] int, ref dst: [] int) {
      // Combine src and dst into a tuple array
      var edges: [0..<src.size] (int, int);
      for i in 0..<src.size do
        edges[i] = (src[i], dst[i]);

      var TupleComp: TupleComparator;

        // Sort the edges using the comparator
      sort(edges, comparator=TupleComp);
      // Extract sorted src and dst arrays
      var sortedSrc: [0..< src.size] int;
      var sortedDst: [0..< dst.size] int;
      for i in 0..<src.size {
        sortedSrc[i]= edges[i][0];
        sortedDst[i]= edges[i][1];
      }

      return (sortedSrc, sortedDst);
    }

        
    /* Function to remove duplicate edges from sorted edge lists */
    proc removeMultipleEdges(ref src: [] int, ref dst: [] int) {
      var uniqueSrc = new list(int);
      var uniqueDst = new list(int);

      if src.size == 0 then return (src, dst);

      uniqueSrc.pushBack(src[0]);
      uniqueDst.pushBack(dst[0]);

      for i in 1..<src.size {
        if src[i] != src[i - 1] || dst[i] != dst[i - 1] {
          uniqueSrc.pushBack(src[i]);
          uniqueDst.pushBack(dst[i]);
        }
      }

      // Convert lists to arrays
      var noDupsSrc = uniqueSrc.toArray();
      var noDupsDst = uniqueDst.toArray();

      return (noDupsSrc, noDupsDst);
    }




    /* Function to calculate the degree of a vertex within a component/cluster/community. */
    proc calculateClusterDegree(ref members: set(int), vertex: int) throws {

      const ref neighbors1 = neighborsSetGraphG1[vertex];
      var newWay = setIntersectionSize(neighbors1,members);
      // writeln("calculateClusterDegree NEW (",vertex,") -> ",newWay);

      // const ref neighbors = dstNodesG1[segGraphG1[vertex]..<segGraphG1[vertex+1]];
      // var neighborsSet: set(int);
      // // Insert array elements into the set
      // for elem in neighbors {
      //   neighborsSet.add(elem);  
      // }
      
      // var intersection: set(int);
      // intersection = neighborsSet & members;
      // writeln("calculateClusterDegree for (",vertex,") -> ",intersection.size);

      //assert(intersection.size == newWay, "Error: The degrees are not equal!");
      //return intersection.size;
      return newWay;
    }
    /* Write out the clusters to a file. */
    //proc writeClustersToFile(ref membersA:set(int), id: int, depth: int, cut: int, ref mapper:[] int) throws {
    proc writeClustersToFile(ref membersA:set(int), id: int, depth: int, cut: int) throws {
        var filename = outputPath + "/cluster_" + id:string + "_" + depth:string + "_" + membersA.size:string + "_" + cut:string + ".debugging";
        var file = open(filename, ioMode.cw);
        var fileWriter = file.writer(locking=false);
        var mappedArr = nodeMapGraphG1[membersA.toArray()];

        fileWriter.writeln("# cluster ID: " + id: string); 
        fileWriter.writeln("# cluster Depth: " + depth: string); 
        fileWriter.writeln("# number of members: " + membersA.size: string);
        fileWriter.writeln("# cutsize: " + cut: string);
        fileWriter.writeln("# members: " + mappedArr: string);
        
        try fileWriter.close();
        try file.close();
    }
    /* If given two lists with all vertices and cluster information, writes them out to file. */
    proc writeClustersToFile() throws {
      var filename = outputPath + "/cluster_"+".post";
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=false);

      for (v,c) in zip(finalVertices, finalClusters) do writer.writeln(nodeMapGraphG1[v], " ", c);

      writer.close();
      outfile.close();
    }

    /* If given only vertices belonging to one cluster, writes them out to file. */
    proc writeClustersToFile(ref vertices: set(int), cluster:int) throws {
      var filename = outputPath + "/cluster_"+".during";
      var outfile = open(filename, ioMode.cw);
      var writer = outfile.writer(locking=true);

      for v in vertices do writer.writeln(nodeMapGraphG1[v], " ", cluster);

      writer.close();
      outfile.close();
    }

    proc removeDegOne(ref partition:set(int)): set(int) throws{
      if partition.size <= 1{
        var zeroset = new set(int);
        return zeroset;
      }
      //var keepedVertices:set(int, parSafe = true);
      var partitionToPass = partition;
      for v in partition {
        var memberDegree = calculateClusterDegree(partition, v);
        //writeln("Degree ",v," = ", memberDegree);
        if memberDegree < 2 {
          partitionToPass.remove(v);
        }
      }
      return(partitionToPass);
    }
    /* Helper method to run the recursion. */
    /* Calls out to an external procedure that runs VieCut. */
    proc callMinCut(ref vertices: set(int), id: int, depth: int): list(int) throws {
      //writeln("///////////////////////callMinCut, received: ",vertices.size," vertices to CUT");
      var allWCC: list(int, parSafe=true);
      
      // If the vertices array is empty, do nothing and return an empty list
      if vertices.size < 2 {
        return allWCC;
      }

      var (src, dst, mapper) = getEdgeList(vertices);
      var n = mapper.size;
      var m = src.size;
      writeln("getEdgeList returned:");
      writeln("$$$$ n: ", n);
      writeln("$$$$ m: ", m);
      writeln("$$$$ src: ", src);
      writeln("$$$$ dst: ", dst);
      writeln("$$$$ mapper: ", mapper);
      // if m < 1 {
      //   return allWCC;
      // }
      var partitionArr: [{0..<n}] int;
      // Oliver why a new array? It should be reason for that. I removed it.
      // var newSrc: [{0..<m}] int = src;
      // var newDst: [{0..<m}] int = dst;
      // Call the external min-cut function
      var cut = c_computeMinCut(partitionArr, src, dst, n, m);
      //writeln("cutSize = ", cut);
      var functionCriteria: int = 0;
      
      if functionTypePassed == 1 {
        writeln("floor(0.01 * (vertices.size)): ", floor(0.01 * (vertices.size))," cutSize = ", cut);
        var funcret = floor(0.01 * (vertices.size));
        functionCriteria = funcret:int;
      } 

      if functionTypePassed == 5 {
        writeln("floor(sqrt(vertices.size:real)/5): ",floor(sqrt(vertices.size:real)/5)," cutSize = ", cut);

        var funcret = floor(sqrt(vertices.size:real)/5);
        functionCriteria = funcret:int;
      } 

      if functionTypePassed == 10 {
        writeln("floor(log10(vertices.size: real): ", floor(log10(vertices.size: real))," cutSize = ", cut);

        var logN = floor(log10(vertices.size: real));
        functionCriteria = logN:int;
      }      
      
      if functionTypePassed == 2 {
        writeln("floor(log2(vertices.size: real)): ", floor(log2(vertices.size: real)), " cutSize = ", cut);

        var logN = floor(log2(vertices.size: real));
        functionCriteria = logN:int;
      }

      // writeln("functionCriteria:", functionCriteria);

      // var logN = floor(log10(vertices.size: real));
      // var floorLog10N: int = logN:int;
      
      if cut > functionCriteria {// Check Well Connectedness
        allWCC.pushBack(id); //allWCC.pushBack(depth); allWCC.pushBack(vertices.size); allWCC.pushBack(cut);
        var currentId = globalId.fetchAdd(1);
        if outputType == "debug" then writeClustersToFile(vertices, id, depth, cut);
        else if outputType == "during" then writeClustersToFile(vertices, currentId);
        for v in vertices {
          finalVertices.pushBack(v);
          finalClusters.pushBack(currentId);
        }
        
        writeln("for cluster: ",id," in depth: ",depth," with cutsize: ", cut, " we found wcc with ",vertices.size," memebr!");
        writeln("finalVertices: ", finalVertices);
        writeln("finalClusters: ", finalClusters);
        return allWCC;
      }
      else{// Cluster is not WellConnected
        
        // Separate vertices into two partitions
        var cluster1, cluster2 = new set(int);
        for (v,p) in zip(partitionArr.domain, partitionArr) {
          if p == 1 then cluster1.add(mapper[v]);
          else cluster2.add(mapper[v]);
        }

        writeln("cluster1: ", cluster1);
        writeln("cluster2: ", cluster2);
        var newSubClusters: list(int, parSafe=true);
        
        // The partition size must be greater than 1, to be meaningful passing it to VieCut.
        //--------> The partition size must be greater than 11, George SAID ON SLACK.
        if cluster1.size >1 {
          var inPartition = removeDegOne(cluster1);
          newSubClusters = callMinCut(inPartition, id, depth+1);
        }
        if cluster2.size >1 {
          var outPartition = removeDegOne(cluster2);
          newSubClusters = callMinCut(outPartition, id, depth+1);
        }
        
        for findings in newSubClusters do allWCC.pushBack(findings);
      }
      return allWCC;
    }
    // TO OLIVER:
    /* Core 2 Decomposition. For some reasons that you know we didn't use it!*/
    proc clusterC2D(ref clusterNodes: set(int)): set(int) throws{
      // Create a copy of the input set to work with. Oliver is it a ref or copy?
      var coreMembers = clusterNodes;
      var coreDomain: domain(int, parSafe=true);
      
      for elem in coreMembers {
        coreDomain.add(elem);
      }

      // Map from vertex id to its degree within the cluster
      var degrees: [coreDomain] atomic int;

      // List of nodes with degree less than 2 to be removed
      var nodesToRemove = new list(int);

      // Initialize degrees and nodesToRemove
      forall vertex in coreMembers with (ref degrees, ref nodesToRemove, ref coreMembers) {
        degrees[vertex].write(calculateClusterDegree(coreMembers, vertex));
        if degrees[vertex].read() < 2 {
          nodesToRemove.pushBack(vertex);
        }
      }
      writeln("degrees: ", degrees);
      writeln("degrees.domain: ", degrees.domain);
      writeln("before while nodesToRemove: ", nodesToRemove);
      // Iteratively remove nodes with degree less than 2
      while !nodesToRemove.isEmpty() {
        // Collect node to be processed in this iteration
        var currentNodesToRemove = nodesToRemove.popBack();
        const ref neighbors = dstNodesG1[segGraphG1[currentNodesToRemove]..<segGraphG1[currentNodesToRemove+1]];
        writeln("currentNodesToRemove: ", currentNodesToRemove);
        writeln("it's neighbours: ", neighbors);

        for u in clusterNodes {
          if neighbors.find(u) != -1 && degrees[u].read() >= 2 {
            // update degrees
            degrees[u].sub(1);
            if degrees[u].read() < 2 then nodesToRemove.pushBack(u);
          }
        }
        // Mark currentNodesToRemove as removed.
        writeln("currentNodesToRemove checked: ", currentNodesToRemove);
        degrees[currentNodesToRemove].write(-1);
      }

      // Step 4: Collect nodes with degrees >= 2 and update cluster
      var newMembers = new set(int);
      for v in degrees.domain {
        if degrees[v].read() >= 2 {
          newMembers.add(v);
        }
      }
      writeln("core2Decomposition returned cluster with size:",newMembers.size);
      writeln("core2Decomposition returned cluster with size:",newMembers);
      return newMembers;
    }


    /* Kick off well-connected components. */
    proc wcc(g1: SegGraph): [] int throws {
      
      writeln("Graph loaded. It has: ",g1.n_vertices," vertices and ",g1.n_edges, ".");
      
      var results: list(int, parSafe=true);
      var clusters = readClustersFile(inputcluster_filePath);
      writeln("reading Clusters' File finished.");
      //writeln("clusters.keysToArray(): ", clusters.keysToArray());
      //writeln("clusters.keysToArray().domain: ", clusters.keysToArray().domain);
      
      forall key in clusters.keysToArray() with (ref results, ref clusters) {
      //for key in clusters.keysToArray() {
        ref clusterToAdd = clusters[key];
        writeln("Cluster ", key, ": ", clusterToAdd.size," vertices.");
        
        /*
        TO OLIVER: I changed my mind and commented this because there is a chance that at the first step we find
        a well connected cluster. PLEASE check the Min's code and MY STATEMENT on slack.
        //var clusterSetInit1 = removeDegOne(clusterToAdd);
        //writeln("clusterSetInit First *removeDegOne: ", clusterSetInit1.size);
        */

        if clusterToAdd.size > 1 && key== 38{ // The cluster is not a singleton.
          
          writeln("*-*-*-*-*-*-*-*-*-*-*-*-*-*");
          writeln("selected Cluster is:", key, " members are:",clusterToAdd );
          //To Oliver: I did it because of the warnings!
          var newResults:list(int, parSafe=true);
          newResults = callMinCut(clusterToAdd, key, 0); 
          for mapping in newResults do results.pushBack(mapping);
        }
      }
        var subClusterArrToReturn: [0..#results.size] int;
        subClusterArrToReturn = results.toArray();
        
        //To Oliver: I know it is expensive but I did it for my tests. We don't need it. Do we?
        sort(subClusterArrToReturn);
        if outputType == "post" then writeClustersToFile();

        return subClusterArrToReturn;
      } // end of wcc
    
    return clusterArr;
  } // end of runWCC
} // end of WellConnectedComponents module