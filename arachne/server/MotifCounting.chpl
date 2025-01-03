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
            
            // For test purpose assume naugty returned this
            var results: [0..<state.k] int = 0..<state.k;
            var nautyLabels = results;

            if logLevel == LogLevel.DEBUG {
                writeln("Nauty returned: ", nautyLabels, " we are in the way to Classify!");
            }

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
seperated by a -1, So Harvard team can use it for cisualization purpose
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


    writeln("**********************************************************************");

    writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
    writeln("Maximum degree: ", maxDeg);

    Enumerate(g1.n_vertices, motifSize, maxDeg );
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