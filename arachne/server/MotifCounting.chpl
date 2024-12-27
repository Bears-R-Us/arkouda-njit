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

    var visited: domain(int , parSafe=false); // I changed it from (bool of array size n) to domain

    // subgraph[level][0] = count; subgraph[level][1..count] = vertices
    var subgraph: [0..<k, 0..<k+1] int;

    // childSet[level][0] = count; childSet[level][1..count] = children
    var childSet: [0..<k, 0..(maxDeg*k)+1] int;

    // indexMap[level][i] maps selection order for revolve-door algorithm
    var indexMap: [0..<k, 0..(maxDeg*k)+1] int;

    var localsubgraphCount: int;
    var localmotifClasses: set(uint(64), parSafe=false);

    proc init(n: int, k: int, maxDeg: int) {
      this.n = n;
      this.k = k;
      this.maxDeg = maxDeg;
      // this.visited = false;
      this.visited = {1..0};
      this.subgraph = 0;
      this.childSet = 0;
      this.indexMap = 0;
      this.localsubgraphCount = 0;
    }

    proc reset() {
      // this.visited = false;
      this.subgraph = 0;
      this.childSet = 0;
      this.indexMap = 0;
      this.localsubgraphCount = 0;
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
    var n = nodeMapGraphG1.size;
    var k = motifSize; // Looking for motifs of size motifSize
    var nodeDegree: [0..<n] int;

    forall v in 0..<n with (ref nodeDegree) {
      var NeiIn = dstRG1[segRG1[v]..<segRG1[v+1]];
      var NeiOut = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];
      nodeDegree[v] = NeiIn.size + NeiOut.size;
    }
    var maxDeg = max reduce nodeDegree;

    // All motif counting and classify variables
    var globalMotifCount: atomic int;
    var globalClasses: set(uint(64), parSafe=true);
    // Initiate it to 0
    globalMotifCount.write(0);

    // Gathers unique valid neighbors for the current level.
    proc initChildSet(ref state: KavoshState, root: int, level: int) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("====== initChildSet called for level ", level, " and root ", root, " ======");
      }

      state.childSet[level,0] = 0;
      const parentsCount = state.subgraph[level-1,0];

      // For each vertex chosen at the previous level, get its neighbors
      for p in 1..parentsCount {
        const parent = state.subgraph[level-1,p];

        // Collect all neighbors (both in and out) in a domain to ensure uniqueness
        var neighbours: domain(int, parSafe=false);

        // Outgoing neighbors
        var outNeighbors = dstNodesG1[segGraphG1[parent]..<segGraphG1[parent+1]];
        neighbours += outNeighbors;

        // Incoming neighbors
        var inNeighbors = dstRG1[segRG1[parent]..<segRG1[parent+1]];
        neighbours += inNeighbors;

        // Add each outNeighbor to childSet if it passes criteria
        for neighbor in neighbours {
          // Must be greater than root and not visited para
          // if neighbor > root && !state.visited[neighbor] {
          if neighbor > root && !state.visited.contains(neighbor) {

            // // Check for duplicates in current childSet
            // var exists = false;
            // for j in 1..state.childSet[level,0] {
            //   if state.childSet[level,j] == neighbor {
            //     exists = true;
            //     break;
            //   }
            // }
            // If new, add it and mark visited
            // if !exists {
              state.childSet[level,0] += 1;
              state.childSet[level, state.childSet[level,0]] = neighbor;
              // state.visited[neighbor] = true;
              state.visited.add(neighbor);
            // }
          }
        }
      }

      if logLevel == LogLevel.DEBUG {
        writeln("initChildSet: Found ", state.childSet[level,0], " valid children at level ", level);
        write("Children: ");
        for i in 1..state.childSet[level,0] {
          write(state.childSet[level,i], " ");
        }
        writeln();
      }
    }// End of initChildSet

    proc prepareNaugtyArguments(ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("===== prepareNaugtyArguments called =====");
      }

      // Build an array for the chosen vertices in this subgraph
      var chosenVerts: [1..state.k] int;
        // subgraph[i, 1..subgraph[i,0]] are chosen at that level
        // but each level of Kavosh picks a certain number of vertices.
        // Combine them in order. The total number selected = k.
        // The order in subgraph is the order of selection.
        // Each subgraph[i,0] > 0 means we selected some vertices at that level.
        // Flatten them into chosenVerts in ascending order of level.
        var idx = 1;
        for i in 0..<state.k {
          for x in 1..state.subgraph[i,0] {
            chosenVerts[idx] = state.subgraph[i,x];
            idx += 1;
          }
        }
        // Create and initialize adjacency matrix from chosenVerts
        var adjMatrix: [0..#(state.k * state.k)] int = 0;

        forall i in 0..#state.k with (ref adjMatrix) {
            for j in 0..#state.k {
                if i != j {
                    var u = chosenVerts[i+1]; // +1 because chosenVerts is 1-based
                    var w = chosenVerts[j+1];
                    var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                    if eid != -1 {
                      adjMatrix[i * state.k + j] = 1;
                    }
                    // } else{
                    //   adjMatrix[i * state.k + j] = 0;
                    // }
                }
             }
         }
  
        if logLevel == LogLevel.DEBUG {
          // Print the mapping
          writeln("Vertex to Index mapping:");
          for i in 1..state.k {
              writeln("Vertex ", chosenVerts[i], " -> Index ", i-1);
          }

          // Print it in 2D format for better visualization
          writeln("\nAdjacency Matrix (2D visualization):");
          for i in 0..#state.k {
              for j in 0..#state.k {
                  write(adjMatrix[i * state.k + j], " ");
              }
              writeln();
          }
          writeln();
        }
      return (adjMatrix, chosenVerts);
    }// End of prepareNaugtyArguments

    // proc createNewAdjMatrix(ref chosenVerts: [] int, ref nautyLabels: [] int, ref state: KavoshState) throws {
    //   if logLevel == LogLevel.DEBUG {
    //     writeln("===== createNewAdjMatrix called =====");
    //     writeln("Original chosenVerts: ", chosenVerts);
    //     writeln("Nauty labels: ", nautyLabels);
    //   }

    //   // Create mapping from new position to original vertex
    //   var newMapping: [0..#state.k] int;
    //   for i in 0..#state.k {
    //     // nautyLabels[i] tells us which original position should be at position i
    //     // chosenVerts is 1-based, so we add 1 to nautyLabels
    //     newMapping[i] = chosenVerts[nautyLabels[i] + 1];
    //   }

    //   // Create and initialize new adjacency matrix based on new mapping
    //   var newAdjMatrix: [0..#(state.k * state.k)] int;
    //   for i in 0..#state.k {
    //     for j in 0..#state.k {
    //         if i != j {
    //             var u = newMapping[i];
    //             var w = newMapping[j];
    //             var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
    //             if eid != -1 {
    //                 newAdjMatrix[i * state.k + j] = 1;
    //             } else {
    //                 newAdjMatrix[i * state.k + j] = 0;
    //             }
    //         }
    //     }
    //   }

    //   if logLevel == LogLevel.DEBUG {
    //     writeln("New vertex mapping:");
    //     for i in 0..#state.k {
    //         writeln("Vertex ", newMapping[i], " -> IndexedTo ", i);
    //     }

    //     writeln("\nNew Adjacency Matrix (2D visualization):");
    //     for i in 0..#state.k {
    //         for j in 0..#state.k {
    //             write(newAdjMatrix[i * state.k + j], " ");
    //         }
    //         writeln();
    //     }
    //     writeln();
    //   }

    //   return (newAdjMatrix, newMapping);
    // }
    
    // proc encodePatternFromMatrix(ref adjMatrix: [] int, ref k: int): uint(64) throws {
    //   var pattern: uint(64) = 0;
    //   var pos = 0;

    //   // Same row-major traversal as before
    //   for i in 0..#k {
    //       for j in 0..#k {
    //           // Set bit based on adjacency matrix value
    //           if adjMatrix[i * k + j] == 1 {
    //               pattern |= 1:uint(64) << pos;
    //           }
    //           pos += 1;
    //       }
    //   }

    //   if logLevel == LogLevel.DEBUG {
    //       writeln("Adjacency Matrix used for encoding:");
    //       for i in 0..#k {
    //           for j in 0..#k {
    //               write(adjMatrix[i * k + j], " ");
    //           }
    //           writeln();
    //       }
    //       writeln("Generated pattern= ", pattern);
    //   }
      
    //   return pattern;
    // }

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
            // For debugging, show what the equivalent adjacency matrix would look like
            writeln("\nEquivalent Adjacency Matrix (2D visualization):");
            for i in 0..#state.k {
                for j in 0..#state.k {
                    var bitPos = i * state.k + j;
                    write(if (pattern & (1:uint(64) << bitPos)) != 0 then 1 else 0, " ");
                }
                writeln();
            }
            writeln();
        }
      return pattern;
    }// End of generatePatternDirect

    // Explores subgraphs containing the root vertex,
    // expanding level by level until remainedToVisit = 0 (which means we have chosen k vertices).
    proc Explore(ref state: KavoshState, root: int, level: int, remainedToVisit: int) throws{

      
      if logLevel == LogLevel.DEBUG {
        writeln("===== Explore called =====");
        writeln("Current root: ", root, " level: ", level, " remainedToVisit: ", remainedToVisit);
        writeln("Visited Vertices: ", state.visited);
        writeln("Current partial subgraph level by level:");
        for l in 0..<level {
          write("Level ", l, " (count=", state.subgraph[l,0], "): ");
          for x in 1..state.subgraph[l,0] {
            write(state.subgraph[l,x], " ");
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
          // writeln("Found complete subgraph #", allMotifCounts.read());
          for l in 0..<state.k {
            write("Level ", l, ": ");
            for x in 1..state.subgraph[l,0] {
              write(state.subgraph[l,x], " ");
            }
            writeln();
          }
          writeln("Now we make adjMatrix to pass to Naugty");
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

        
        // For test purpose assume naugty returned this
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

      // Get children for this level
      initChildSet(state, root, level);
      const childCount = state.childSet[level,0];

      // Try all possible selection sizes at this level, from 1 to remainedToVisit
      for selSize in 1..remainedToVisit {
        if childCount < selSize {
          // Not enough children to form this selection
          if logLevel == LogLevel.DEBUG {
            writeln("Not enough children (", childCount, ") to select ", selSize, " vertices at level ", level);
          }
          // Unmark visited children before returning
          for i in 1..childCount {
            // state.visited[state.childSet[level,i]] = false;
            state.visited.remove(state.childSet[level,i]);
          }
          return;
        }

        // Initial selection: pick the first selSize children
        state.subgraph[level,0] = selSize;
        for i in 1..selSize {
          state.subgraph[level,i] = state.childSet[level,i];
          state.indexMap[level,i] = i;
        }

        if logLevel == LogLevel.DEBUG {
          writeln("Exploring with initial selection of size ", selSize, " at level ", level);
          write("Selected vertices: ");
          for i in 1..selSize {
            write(state.subgraph[level,i], " ");
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
        // state.visited[state.childSet[level,i]] = false;
        state.visited.remove(state.childSet[level,i]);
      }
      state.subgraph[level,0] = 0;
    }// End of Explore

    // I read this for implementing revolving door 
    // https://encyclopediaofmath.org/wiki/Gray_code#Combinations.2C_partitions.2C_permutations.2C_and_other_objects.

    // swapping: Used by revolve-door Gray code generation to swap two elements
    // and then immediately Explore with the new combination.
    proc swapping(i: int, j: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("swapping called: swapping indices ", i, " and ", j, " at level ", level);
        writeln("Before swapping: indexMap[level,i] = ", state.indexMap[level,i], 
                " indexMap[level,j] = ", state.indexMap[level,j]);
      }

      state.indexMap[level,i] = state.indexMap[level,j];
      state.subgraph[level, state.indexMap[level,i]] = state.childSet[level,i];

      if logLevel == LogLevel.DEBUG {
        writeln("After swapping: subgraph[level,indexMap[level,i]] = childSet[level,i] = ", state.childSet[level,i]);
        writeln("Now calling Explore after swapping");
      }

      Explore(state, root, level+1, remainedToVisit - m);
    }// End of swapping

    // ForwardGenerator(GEN): Part of revolve-door combination Forward Generator 
    proc ForwardGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("ForwardGenerator called with n=", n, " k=", k, " level=", level, " remainedToVisit=", remainedToVisit, " m=", m);
      }

      if k > 0 && k < n {
        ForwardGenerator(n-1, k, root, level, remainedToVisit, m, state);

        if k == 1 {
          if logLevel == LogLevel.DEBUG {
            writeln("ForwardGenerator: k=1 case, calling swapping(n, n-1) => swapping(", n, ", ", n-1, ")");
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
    proc reverseGenerator(n: int, k: int, root: int, level: int, remainedToVisit: int, m: int, ref state: KavoshState) throws{
      if logLevel == LogLevel.DEBUG {
        writeln("reverseGenerator called with n=", n, " k=", k, " level=", level, " remainedToVisit=", remainedToVisit, " m=", m);
      }

      if k > 0 && k < n {
        ForwardGenerator(n-1, k-1, root, level, remainedToVisit, m, state);

        if k == 1 {
          if logLevel == LogLevel.DEBUG {
            writeln("reverseGenerator: k=1 case, calling swapping(n-1, n) => swapping(", n-1, ", ", n, ")");
          }
          swapping(n-1, n, root, level, remainedToVisit, m, state);
        } else {
          if logLevel == LogLevel.DEBUG {
            writeln("reverseGenerator: k>1 case, calling swapping(k-1, n) => swapping(", k-1, ", ", n, ")");
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
seperated by a -1, So Harvard team can use it for cisualization purpose
*/
////////////////////////////////////////////////////////////////////////////////

    // Execute enumeration for sequentil running
    //Enumerate(state);

    // EnumerateParallel(n, k, maxDeg);
    // Enumerate: Iterates over all vertices as potential roots
    // and calls Explore to find all subgraphs of size k containing that root.
    proc Enumerate(n: int, k: int, maxDeg: int) throws{
      
      if logLevel == LogLevel.DEBUG {
        writeln("Enumerate: starting enumeration over all vertices");
      }

      coforall v in 0..<n with (ref globalClasses, ref globalMotifCount){
        if logLevel == LogLevel.DEBUG {
          writeln("Root = ", v, " (", v+1, "/", n, ")");
        }

        var state = new KavoshState(n, k, maxDeg);

        state.subgraph[0,0] = 1;
        state.subgraph[0,1] = v;
        state.visited.add(v);

        Explore(state, v, 1, state.k - 1);
        if logLevel == LogLevel.DEBUG {
          writeln("Total Number of motifs: ", state.localsubgraphCount);
          writeln("Number of Non-isomorphic Classes: ", state.localmotifClasses);
          writeln();
        }
        globalMotifCount.add(state.localsubgraphCount);
        //globalClasses += state.localmotifClasses;

      }

      if logLevel == LogLevel.DEBUG {
        writeln("Enumerate: finished enumeration over all vertices");
      }
    }// End of Enumerate




    if logLevel == LogLevel.DEBUG {
      writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
      writeln("Maximum degree: ", maxDeg);
    }

    Enumerate(g1.n_vertices, motifSize, maxDeg );

    // Oliver: Now you can make your src and dst based on Classes that I gathered in 
    // motifClasses and return them to users 
    // we should decide to keep or delete (allmotifs list)
    
    if logLevel == LogLevel.DEBUG {
      writeln("\nglobalMotifCount: ", globalMotifCount.read());
      writeln("\nglobalClasses: ", globalClasses);
      writeln("\nglobalClasses.size: ", globalClasses.size);
    }
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