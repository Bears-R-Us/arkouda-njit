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


class KavoshState {

    var n: int;
    var k: int;
    var maxDeg: int;
    const minSize: int = k;  // Minimum size for arrays

    var visited: domain(int , parSafe=false); // I changed it from (bool of array size n) to domain

    // Single flat array for all levels with dynamic resizing
    var arrayDomain: domain(1);  // Domain to control overall size
    var childSet: [arrayDomain] int;     // Single flat array for all levels
    var indexMap: [arrayDomain] int;     // Single flat array for all levels
    
    // Track size and capacity per level
    var levelSizes: [0..<k] int;         // Current size of each level
    var levelCapacities: [0..<k] int;    // Current capacity of each level
    var levelOffsets: [0..<k] int;       // Starting offset for each level

    // Fixed-size subgraph remains as is since it's small and fixed
    var subgraph: [0..<(k * (k+1))] int;  // Flattened fixed-size array

    var localsubgraphCount: int;
    var localmotifClasses: set(uint(64), parSafe=false);

    proc init(n: int, k: int) {
        this.n = n;
        this.k = k;
        this.visited = {1..0};
        
        // Initialize with minimum size for each level
        var totalSize = k * minSize;
        this.arrayDomain = {0..totalSize-1};
        
        // Initialize tracking arrays
        this.levelSizes = 0;
        this.levelCapacities = minSize;
        
        // Calculate initial offsets
        this.levelOffsets = 0;
        for i in 1..<k {
            this.levelOffsets[i] = this.levelOffsets[i-1] + minSize;
        }
        
        // Initialize data arrays
        this.childSet = 0;
        this.indexMap = 0;
        this.subgraph = 0;
        this.localsubgraphCount = 0;
    }

    // Helper functions for array access
    inline proc getChildSetIndex(level: int, idx: int): int {
        return levelOffsets[level] + idx;
    }

    proc getChildSetElement(level: int, idx: int): int {
        return childSet[getChildSetIndex(level, idx)];
    }

    proc setChildSetElement(level: int, idx: int, value: int) {
        childSet[getChildSetIndex(level, idx)] = value;
    }

    // Similar helpers for indexMap
    inline proc getIndexMapElement(level: int, idx: int): int {
        return indexMap[levelOffsets[level] + idx];
    }

    proc setIndexMapElement(level: int, idx: int, value: int) {
        indexMap[levelOffsets[level] + idx] = value;
    }

    // Resize specific level
    proc resizeLevel(level: int, requestedSize: int) {
        if requestedSize <= levelCapacities[level] then return;

        // Calculate new size with growth factor
        const growthFactor = 1.5;
        const newCapacity = max(requestedSize, 
                              minSize, 
                              (levelCapacities[level]: real * growthFactor): int);

        // Calculate new total size needed
        var newTotalSize = 0;
        for i in 0..<k {
            if i == level then
                newTotalSize += newCapacity;
            else
                newTotalSize += levelCapacities[i];
        }

        // Create new arrays
        var newDomain = {0..newTotalSize-1};
        var newChildSet: [newDomain] int;
        var newIndexMap: [newDomain] int;

        // Copy existing data with updated offsets
        var newOffset = 0;
        for i in 0..<k {
            const oldOffset = levelOffsets[i];
            const size = if i == level then newCapacity else levelCapacities[i];
            
            // Copy data for this level
            const copySize = min(levelSizes[i], size);
            for j in 0..<copySize {
                newChildSet[newOffset + j] = childSet[oldOffset + j];
                newIndexMap[newOffset + j] = indexMap[oldOffset + j];
            }
            
            // Update offset for next level
            levelOffsets[i] = newOffset;
            newOffset += size;
            
            // Update capacity if this is the level we're resizing
            if i == level then
                levelCapacities[i] = newCapacity;
        }

        // Update domain and arrays
        arrayDomain = newDomain;
        childSet = newChildSet;
        indexMap = newIndexMap;
    }

    // Helper for subgraph access (flattened 2D array)
    inline proc getSubgraphElement(level: int, idx: int): int {
        return subgraph[level * (k+1) + idx];
    }

    proc setSubgraphElement(level: int, idx: int, value: int) {
        subgraph[level * (k+1) + idx] = value;
    }

  }// End of KavoshState


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
    var n = g1.n_vertices;
    var k = motifSize; // Looking for motifs of size motifSize
    var nodeDegree: [0..<n] int;
    var nodeNeighbours: [0..<n] domain(int);

    forall v in 0..<n with (ref nodeDegree) {
      var neighbours: domain(int);

      const NeiIn = dstRG1[segRG1[v]..<segRG1[v+1]];
      const NeiOut = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

      neighbours += NeiIn;
      neighbours += NeiOut;

      nodeDegree[v] = neighbours.size;
      // Collect all neighbors (both in and out) in a domain
      nodeNeighbours[v] = neighbours;
    }
    var maxDeg = max reduce nodeDegree;
    
    if logLevel == LogLevel.DEBUG {
        writeln("Graph preprocessing complete");
    }

    // All motif counting and classify variables
    var globalMotifCount: atomic int;
    var globalClasses: set(uint(64), parSafe=true);
    // Initiate it to 0
    globalMotifCount.write(0);

    // Gathers unique valid neighbors for the current level.
    proc initChildSet(ref state: KavoshState, root: int, level: int) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("====== initChildSet called for level ", level, " and root ", root, " ======");
          writeln("Before collection - Current state:");
          writeln("  Level Sizes: ", state.levelSizes);
          writeln("  Level Capacities: ", state.levelCapacities);
          writeln("  Level Offsets: ", state.levelOffsets);
          writeln("  Visited Vertices: ", state.visited);
      }

      // Reset count for this level
      state.levelSizes[level] = 0;
      
      const parentsCount = state.getSubgraphElement(level-1, 0);

      if logLevel == LogLevel.DEBUG {
          writeln("\nParents at level ", level-1, ":");
          write("  Count: ", parentsCount, ", Vertices: ");
          for p in 1..parentsCount {
              write(state.getSubgraphElement(level-1, p), " ");
          }
          writeln();
      }

      // Calculate potential children
      var potentialChildren = 0;
      for p in 1..parentsCount {
          const parent = state.getSubgraphElement(level-1, p);
          potentialChildren += nodeNeighbours[parent].size;
      }

      if logLevel == LogLevel.DEBUG {
          writeln("\nPotential children calculation:");
          writeln("  Maximum possible children: ", potentialChildren);
          writeln("  Current capacity at level ", level, ": ", state.levelCapacities[level]);
      }

      // Ensure enough capacity
      if potentialChildren > state.levelCapacities[level] {
          if logLevel == LogLevel.DEBUG {
              writeln("\nResizing required for level ", level);
              writeln("  Old capacity: ", state.levelCapacities[level]);
          }
          
          state.resizeLevel(level, potentialChildren);
          
          if logLevel == LogLevel.DEBUG {
              writeln("  New capacity: ", state.levelCapacities[level]);
              writeln("  New offsets: ", state.levelOffsets);
          }
      }

      // Collect children
      if logLevel == LogLevel.DEBUG {
          writeln("\nCollecting children:");
      }

      for p in 1..parentsCount {
          const parent = state.getSubgraphElement(level-1, p);
          if logLevel == LogLevel.DEBUG {
              writeln("  Processing parent ", parent);
              writeln("  Neighbours: ", nodeNeighbours[parent]);
          }

          for neighbor in nodeNeighbours[parent] {
              if neighbor > root && !state.visited.contains(neighbor) {
                  state.levelSizes[level] += 1;
                  state.setChildSetElement(level, state.levelSizes[level], neighbor);
                  state.visited.add(neighbor);
                  
                  if logLevel == LogLevel.DEBUG {
                      writeln("    Added child ", neighbor, " at position ", state.levelSizes[level]);
                  }
              } else if logLevel == LogLevel.DEBUG {
                  if neighbor <= root {
                      writeln("    Skipped ", neighbor, " (not greater than root ", root, ")");
                  } else if state.visited.contains(neighbor) {
                      writeln("    Skipped ", neighbor, " (already visited)");
                  }
              }
          }
      }

      if logLevel == LogLevel.DEBUG {
          writeln("\nFinal state after collection:");
          writeln("  Found ", state.levelSizes[level], " valid children at level ", level);
          write("  Children: ");
          for i in 1..state.levelSizes[level] {
              write(state.getChildSetElement(level, i), " ");
          }
          writeln();
          writeln("  Updated visited set: ", state.visited);
          writeln("======================================================");
      }

    }// End of initChildSet

    proc prepareNaugtyArguments(ref state: KavoshState) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("===== prepareNaugtyArguments called =====");
      }

      // Build array of chosen vertices
      var chosenVerts: [1..state.k] int;
      var idx = 1;
      for i in 0..<state.k {
          for x in 1..state.getSubgraphElement(i, 0) {
              chosenVerts[idx] = state.getSubgraphElement(i, x);
              idx += 1;
          }
      }

      // Create adjacency matrix
      var adjMatrix: [0..#(state.k * state.k)] int = 0;

      forall i in 0..#state.k with (ref adjMatrix) {
          for j in 0..#state.k {
              if i != j {
                  var u = chosenVerts[i+1];
                  var w = chosenVerts[j+1];
                  var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                  if eid != -1 {
                      adjMatrix[i * state.k + j] = 1;
                  }
              }
          }
      }

      if logLevel == LogLevel.DEBUG {
          writeln("Chosen vertices: ", chosenVerts);
          writeln("Adjacency matrix:");
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
          writeln("Vertices: ", chosenVerts);
          writeln("Nauty labels: ", nautyLabels);
      }

      var pattern: uint(64) = 0;
      var pos = 0;

      for i in 0..#state.k {
          for j in 0..#state.k {
              if i != j {
                  var u = chosenVerts[nautyLabels[i] + 1];
                  var w = chosenVerts[nautyLabels[j] + 1];
                  var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                  if eid != -1 {
                      pattern |= 1:uint(64) << pos;
                  }
              }
              pos += 1;
          }
      }

      if logLevel == LogLevel.DEBUG {
          writeln("Generated pattern: ", pattern);
      }

      return pattern;

    }// End of generatePatternDirect

    // Explores subgraphs containing the root vertex,
    // expanding level by level until remainedToVisit = 0 (which means we have chosen k vertices).
    proc Explore(ref state: KavoshState, root: int, level: int, remainedToVisit: int) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("\n===== Explore called =====");
          writeln("Parameters:");
          writeln("  Root: ", root);
          writeln("  Current level: ", level);
          writeln("  Vertices remaining to visit: ", remainedToVisit);
          writeln("\nCurrent State:");
          writeln("  Visited vertices: ", state.visited);
          writeln("  Current subgraph structure by level:");
          for l in 0..<level {
              write("    Level ", l, " (count=", state.getSubgraphElement(l, 0), "): ");
              for x in 1..state.getSubgraphElement(l, 0) {
                  write(state.getSubgraphElement(l, x), " ");
              }
              writeln();
          }
          writeln("==========================");
      }

      // Base case: all k vertices chosen
      if remainedToVisit == 0 {
          state.localsubgraphCount += 1;
          
          if logLevel == LogLevel.DEBUG {
              writeln("\n!!! Found complete subgraph #", state.localsubgraphCount, " !!!");
              writeln("Final subgraph structure:");
              for l in 0..<state.k {
                  write("  Level ", l, " (count=", state.getSubgraphElement(l, 0), "): ");
                  for x in 1..state.getSubgraphElement(l, 0) {
                      write(state.getSubgraphElement(l, x), " ");
                  }
                  writeln();
              }
              writeln("Now preparing for motif classification...");
          }
          var (adjMatrix, chosenVerts) = prepareNaugtyArguments(state);

          // Oliver: This is the place that we should call nautyCaller from cpp. Based on
          // cuurent implenetation we should pass:
          // void nautyClassify(
          // int* subgraph,        // Adjacency matrix as flat array
          // int subgraphSize,     // Number of nodes
          // int* results,         // Output canonical labeling. 0-indexed
          // int performCheck      // Flag to perform nauty_check (1 to perform, else to skip)
          // )

          
          // For test purpose assume naugty returned this: 0, 1, 2, ..., K-1
          var results:[0..<state.k] int = 0..<state.k;

          var nautyLabels = results;
                            
          if logLevel == LogLevel.DEBUG {
            writeln("Nauty returned: ", nautyLabels," we are in the way to Classify!");
          }

          // Then we should Classify based on label that naugty will give.
          var pattern = generatePatternDirect(chosenVerts, nautyLabels, state);
          // assert(encodedID == pattern, 
          //                             "\nPattern mismatch!\n" +
          //                             "encodedID = " + encodedID:string + ")\n" +
          //                             "pattern   = " + pattern:string + ")");
  
          // Here we have an encodedID which for each class of motifs is unique!
          // I should decided how I should gather information. It should be something like VF2-PS
          // 2 things to consider First we have a recursion function, Second we are doing on parallel
          // So maybe we should change the state class. Do we needed it?
          state.localmotifClasses.add(pattern);
          writeln("state.localmotifClasses: ", state.localmotifClasses);
          return ;
        }
      if logLevel == LogLevel.DEBUG {
          writeln("\nInitiating child collection for level ", level);
      }

      // Get children for this level
      initChildSet(state, root, level);
      const childCount = state.levelSizes[level];

      if logLevel == LogLevel.DEBUG {
          writeln("Child collection complete:");
          writeln("  Total children found: ", childCount);
          writeln("  Remained to visit: ", remainedToVisit);
      }

      // Try all possible selection sizes
      for selSize in 1..remainedToVisit {
          if logLevel == LogLevel.DEBUG {
              writeln("\nAttempting selection of size ", selSize, " from ", childCount, " children");
          }

          if childCount < selSize {
              if logLevel == LogLevel.DEBUG {
                  writeln("WARNING: Not enough children (", childCount, ") to select ", 
                        selSize, " vertices at level ", level);
                  writeln("Cleaning up and returning...");
              }
              // Cleanup visited children
              for i in 1..childCount {
                  state.visited.remove(state.getChildSetElement(level, i));
              }
              return;
          }

          if logLevel == LogLevel.DEBUG {
              writeln("Making initial selection of size ", selSize, ":");
          }

          // Initial selection
          state.setSubgraphElement(level, 0, selSize);
          for i in 1..selSize {
              state.setSubgraphElement(level, i, state.getChildSetElement(level, i));
              state.setIndexMapElement(level, i, i);
              if logLevel == LogLevel.DEBUG {
                  writeln("  Selected vertex ", state.getChildSetElement(level, i), 
                        " at position ", i);
              }
          }

          if logLevel == LogLevel.DEBUG {
              writeln("\nRecursing with chosen selection:");
              writeln("  Next level: ", level+1);
              writeln("  Remaining vertices: ", remainedToVisit - selSize);
          }

          // Recurse with chosen selection
          Explore(state, root, level+1, remainedToVisit - selSize);

          if logLevel == LogLevel.DEBUG {
              writeln("\nGenerating other combinations using revolve-door algorithm");
              writeln("  Total children: ", childCount);
              writeln("  Selection size: ", selSize);
          }

          // Generate other combinations
          ForwardGenerator(childCount, selSize, root, level, remainedToVisit, selSize, state);
      }

      if logLevel == LogLevel.DEBUG {
          writeln("\nCompleting exploration at level ", level);
          writeln("Cleaning up visited children...");
      }

      // Cleanup
      for i in 1..childCount {
          state.visited.remove(state.getChildSetElement(level, i));
      }
      state.setSubgraphElement(level, 0, 0);

      if logLevel == LogLevel.DEBUG {
          writeln("Cleanup complete. Visited set after cleanup: ", state.visited);
          writeln("===== End Explore =====\n");
      }
    }// End of Explore

    // I read this for implementing revolving door 
    // https://encyclopediaofmath.org/wiki/Gray_code#Combinations.2C_partitions.2C_permutations.2C_and_other_objects.

    // swapping: Used by revolve-door Gray code generation to swap two elements
    // and then immediately Explore with the new combination.
    proc swapping(i: int, j: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("\n----- swapping called -----");
          writeln("Parameters:");
          writeln("  Swapping positions i=", i, " and j=", j);
          writeln("  At level: ", level);
          writeln("  Remained to visit: ", remainedToVisit);
          writeln("\nBefore swap:");
          writeln("  indexMap[", level, "][", i, "] = ", state.getIndexMapElement(level, i));
          writeln("  indexMap[", level, "][", j, "] = ", state.getIndexMapElement(level, j));
          writeln("  Current selection: ");
          for x in 1..m {
              write(state.getChildSetElement(level, x), " ");
          }
          writeln();
      }

      // Ensure array capacity
      const maxIdx = max(i, j);
      if maxIdx >= state.levelCapacities[level] {
          if logLevel == LogLevel.DEBUG {
              writeln("\nResizing required:");
              writeln("  Current capacity: ", state.levelCapacities[level]);
              writeln("  Required capacity: ", maxIdx + 1);
          }
          state.resizeLevel(level, maxIdx + 1);
          if logLevel == LogLevel.DEBUG {
              writeln("  New capacity: ", state.levelCapacities[level]);
          }
      }

      // Update indexMap
      state.setIndexMapElement(level, i, state.getIndexMapElement(level, j));
      
      // Update subgraph based on new indexMap
      state.setSubgraphElement(level, state.getIndexMapElement(level, i), 
                            state.getChildSetElement(level, i));

      if logLevel == LogLevel.DEBUG {
          writeln("\nAfter swap:");
          writeln("  New indexMap[", level, "][", i, "] = ", state.getIndexMapElement(level, i));
          writeln("  Updated subgraph value at position ", state.getIndexMapElement(level, i), 
                  " = ", state.getChildSetElement(level, i));
          writeln("\nRecursing to next level...");
      }

      Explore(state, root, level+1, remainedToVisit - m);

      if logLevel == LogLevel.DEBUG {
          writeln("----- End swapping -----\n");
      }

    }// End of swapping

    // ForwardGenerator(GEN): Part of revolve-door combination Forward Generator 
    proc ForwardGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("\n>>>>> ForwardGenerator called <<<<<");
          writeln("Parameters:");
          writeln("  n = ", n, " (total elements)");
          writeln("  k = ", k, " (selection size)");
          writeln("  level = ", level);
          writeln("  remainedToVisit = ", remainedToVisit);
          writeln("  m = ", m, " (original selection size)");
          writeln("\nCurrent State at Level ", level, ":");
          writeln("  Capacity: ", state.levelCapacities[level]);
          writeln("  Current Size: ", state.levelSizes[level]);
          writeln("  Current Selection: ");
          for i in 1..k {
              write(state.getChildSetElement(level, i), " ");
          }
          writeln();
      }

      // Ensure array capacity
      if n >= state.levelCapacities[level] {
          if logLevel == LogLevel.DEBUG {
              writeln("\nResizing required:");
              writeln("  Current capacity: ", state.levelCapacities[level]);
              writeln("  Required capacity: ", n+1);
          }
          state.resizeLevel(level, n + 1);
          if logLevel == LogLevel.DEBUG {
              writeln("  New capacity: ", state.levelCapacities[level]);
          }
      }

      if k > 0 && k < n {
          if logLevel == LogLevel.DEBUG {
              writeln("\nRecursing with n-1 = ", n-1);
          }
          ForwardGenerator(n-1, k, root, level, remainedToVisit, m, state);

          if k == 1 {
              if logLevel == LogLevel.DEBUG {
                  writeln("\nk=1 case: swapping positions ", n, " and ", n-1);
              }
              swapping(n, n-1, root, level, remainedToVisit, m, state);
          } else {
              if logLevel == LogLevel.DEBUG {
                  writeln("\nk>1 case: swapping positions ", n, " and ", k-1);
              }
              swapping(n, k-1, root, level, remainedToVisit, m, state);
          }

          if logLevel == LogLevel.DEBUG {
              writeln("\nCalling reverseGenerator with n-1 = ", n-1, " and k-1 = ", k-1);
          }
          reverseGenerator(n-1, k-1, root, level, remainedToVisit, m, state);
      }

      if logLevel == LogLevel.DEBUG {
          writeln(">>>>> End ForwardGenerator <<<<<\n");
      }


    }// End of ForwardGenerator

    // reverseGenerator(NEG): Another part of revolve-door combination generation logic
    proc reverseGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("\n<<<<< reverseGenerator called >>>>>");
          writeln("Parameters:");
          writeln("  n = ", n, " (total elements)");
          writeln("  k = ", k, " (selection size)");
          writeln("  level = ", level);
          writeln("  remainedToVisit = ", remainedToVisit);
          writeln("  m = ", m, " (original selection size)");
          writeln("\nCurrent Selection:");
          for i in 1..m {
              write(state.getChildSetElement(level, i), " ");
          }
          writeln();
      }

      if k > 0 && k < n {
          if logLevel == LogLevel.DEBUG {
              writeln("\nCalling ForwardGenerator with n-1 = ", n-1, " and k-1 = ", k-1);
          }
          ForwardGenerator(n-1, k-1, root, level, remainedToVisit, m, state);

          if k == 1 {
              if logLevel == LogLevel.DEBUG {
                  writeln("\nk=1 case: swapping positions ", n-1, " and ", n);
              }
              swapping(n-1, n, root, level, remainedToVisit, m, state);
          } else {
              if logLevel == LogLevel.DEBUG {
                  writeln("\nk>1 case: swapping positions ", k-1, " and ", n);
              }
              swapping(k-1, n, root, level, remainedToVisit, m, state);
          }

          if logLevel == LogLevel.DEBUG {
              writeln("\nCalling reverseGenerator with n-1 = ", n-1, " and k = ", k);
          }
          reverseGenerator(n-1, k, root, level, remainedToVisit, m, state);
      }

      if logLevel == LogLevel.DEBUG {
          writeln("<<<<< End reverseGenerator >>>>>\n");
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
seperated by a -1, So Harvard team can use it for cisualization purpose
*/
////////////////////////////////////////////////////////////////////////////////


    // Enumerate: Iterates over all vertices as potential roots
    // and calls Explore to find all subgraphs of size k containing that root.
    proc Enumerate(n: int, k: int) throws {
      if logLevel == LogLevel.DEBUG {
          writeln("\n===== Starting Enumeration =====");
          writeln("Parameters:");
          writeln("  Total vertices (n): ", n);
          writeln("  Motif size (k): ", k);
      }

      // Global tracking variables
      var globalMotifCount: atomic int;
      var globalClasses: set(uint(64), parSafe=true);
      globalMotifCount.write(0);

      forall v in 0..<n with (ref globalClasses, ref globalMotifCount) {
          if logLevel == LogLevel.DEBUG {
              writeln("\nProcessing root vertex ", v, " (", v+1, "/", n, ")");
          }

          var state = new KavoshState(n, k);

          // Initialize root vertex
          state.setSubgraphElement(0, 0, 1);
          state.setSubgraphElement(0, 1, v);
          state.visited.add(v);

          // Explore from this root
          Explore(state, v, 1, k - 1);

          if logLevel == LogLevel.DEBUG {
              writeln("\nCompleted root ", v, ":");
              writeln("  Local motif count: ", state.localsubgraphCount);
              writeln("  Local motif classes: ", state.localmotifClasses);
          }

          // Update global counts
          globalMotifCount.add(state.localsubgraphCount);
          globalClasses += state.localmotifClasses;

          state.visited.remove(v);
      }

      if logLevel == LogLevel.DEBUG {
          writeln("\n===== Enumeration Complete =====");
          writeln("Final Results:");
          writeln("  Total motifs found: ", globalMotifCount.read());
          writeln("  Unique motif classes: ", globalClasses.size);
          writeln("  Class IDs: ", globalClasses);
      }

      return (globalMotifCount.read(), globalClasses);

    }// End of Enumerate


    if logLevel == LogLevel.DEBUG {
      writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
      writeln("Maximum degree: ", maxDeg);
    }

    var (totalMotifs, motifClasses) = Enumerate(n, motifSize);
    
    // Oliver: Now you can make your src and dst based on Classes that I gathered in 
    // motifClasses and return them to users 
    // we should decide to keep or delete (allmotifs list)
    
    if logLevel == LogLevel.DEBUG {
        writeln("\nMotif counting complete:");
        writeln("  Total motifs: ", totalMotifs);
        writeln("  Unique classes: ", motifClasses.size);
    }

    // Prepare return values
    // Oliver: For now, returning placeholder arrays - modify as needed

    var tempArr: [0..0] int;
    var srcPerMotif = makeDistArray(2*2, int);
    var dstPerMotif = makeDistArray(2*2, int);
    return (srcPerMotif, dstPerMotif, tempArr, tempArr);
  }// End of runMotifCounting

}// End of MotifCounting Module