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

// TreeNode class to represent nodes in our pattern classification tree
class TreeNode {
    var left: unmanaged TreeNode?;   // Left child (no edge)
    var right: unmanaged TreeNode?;  // Right child (edge exists)
    var pattern: uint(64);           // Pattern stored at leaf nodes
    var isLeaf: bool = false;        // Flag to mark leaf nodes

    // Constructor
    proc init() {
        this.left = nil;
        this.right = nil;
        this.pattern = 0;
        this.isLeaf = false;
    }

    // Destructor to handle memory management
    proc deinit() {
        if left != nil then delete left;
        if right != nil then delete right;
    }
}

    class KavoshState {
        var n: int;
        var k: int;
        var maxDeg: int;
        var visited: domain(int, parSafe=true);

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
require "nauty-wrapper/bin/nautyClassify.o",
        "nauty-wrapper/include/nautyClassify.h",
        "nauty-wrapper/bin/nauty.o",
        "nauty-wrapper/bin/naugraph.o",
        "nauty-wrapper/bin/nautil.o";

// The function signature stays the same, just uses int64_t
extern proc c_nautyClassify(
    subgraph: [] int(64), 
    subgraphSize: int(64), 
    results: [] int(64),
    performCheck: int(64),
    verbose: int(64)
) : int(64);
  

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
    try {
        if logLevel == LogLevel.DEBUG {
            writeln("===== prepareNaugtyArguments called =====");
        }

        // Step 1: Build array of chosen vertices with bounds checking
        var chosenVerts: [1..state.k] int;
        var idx = 1;
        var totalVertices = 0;
        
        // First pass: validate total vertex count
        for level in 0..<state.k {
            const vertCount = state.getSubgraph(level, 0);
            if vertCount < 0 {
                writeln("Error state at level ", level);
                writeln("Current state: ", state);
                writeln("VertCount: ", vertCount);
                throw new Error("Invalid vertex count at level " + level:string);
            }
            totalVertices += vertCount;
            if logLevel == LogLevel.DEBUG {
                writeln("Level ", level, " has ", vertCount, " vertices");
            }
        }
        
        if totalVertices != state.k {
            writeln("Vertex count mismatch:");
            writeln("Found: ", totalVertices);
            writeln("Expected: ", state.k);
            throw new Error("Total vertices mismatch");
        }

        // Second pass: collect vertices with detailed validation
        var usedVertices: domain(int);  // Track used vertices to check duplicates
        for level in 0..<state.k {
            const vertCount = state.getSubgraph(level, 0);
            if logLevel == LogLevel.DEBUG {
                writeln("Processing level ", level, " with ", vertCount, " vertices");
            }
            
            for pos in 1..vertCount {
                if idx > state.k {
                    writeln("Error: Index ", idx, " exceeds k=", state.k);
                    writeln("Level: ", level, " Position: ", pos);
                    throw new Error("Vertex index exceeds k");
                }
                
                const vertex = state.getSubgraph(level, pos);
                if vertex < 0 {
                    writeln("Error: Negative vertex value ", vertex);
                    writeln("Level: ", level, " Position: ", pos);
                    throw new Error("Invalid vertex value");
                }
                
                if usedVertices.contains(vertex) {
                    writeln("Error: Duplicate vertex ", vertex);
                    writeln("Level: ", level, " Position: ", pos);
                    throw new Error("Duplicate vertex found");
                }
                
                chosenVerts[idx] = vertex;
                usedVertices.add(vertex);
                
                if logLevel == LogLevel.DEBUG {
                    writeln("Added vertex ", vertex, " at index ", idx);
                }
                idx += 1;
            }
        }

        // Verify vertex collection
        if idx - 1 != state.k {
            writeln("Error: Collected ", idx-1, " vertices but expected ", state.k);
            throw new Error("Vertex collection mismatch");
        }

        // Create a copy for sorting to preserve original order
        var sortedVerts = chosenVerts;
        sort(sortedVerts);

        if logLevel == LogLevel.DEBUG {
            writeln("Original vertices: ", chosenVerts);
            writeln("Sorted vertices: ", sortedVerts);
        }

        // Step 2: Create adjacency matrix with bounds checking
        var adjMatrix: [0..#(state.k * state.k)] int = 0;

        // Step 3: Fill adjacency matrix using original vertex order
        var edgeCount = 0;
        for i in 0..#state.k {
            if i+1 > state.k {
                writeln("Warning: Index i=", i+1, " exceeds k=", state.k);
                continue;
            }
            for j in 0..#state.k {
                if j+1 > state.k {
                    writeln("Warning: Index j=", j+1, " exceeds k=", state.k);
                    continue;
                }
                if i != j {
                    var u = chosenVerts[i+1];
                    var w = chosenVerts[j+1];
                    var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                    if eid != -1 {
                        adjMatrix[i * state.k + j] = 1;
                        edgeCount += 1;
                    }
                }
            }
        }

        if logLevel == LogLevel.DEBUG {
            writeln("\nAdjacency Matrix (", edgeCount, " edges):");
            for i in 0..#state.k {
                for j in 0..#state.k {
                    write(adjMatrix[i * state.k + j], " ");
                }
                writeln();
            }
        }

        // Final validation
        if edgeCount == 0 {
            writeln("Warning: No edges found in adjacency matrix", "Vertices: ", chosenVerts);
            writeln();
        }

        return (adjMatrix, sortedVerts);
    } catch e {
        writeln("----------------------------------------");
        writeln("ERROR in prepareNaugtyArguments");
        writeln("Error: ", e.message());
        writeln("State k: ", state.k);
        writeln("State subgraphCount: ", state.localsubgraphCount);
        writeln("----------------------------------------");
        halt();
    }
}

proc generateCanonicalPattern(ref chosenVerts: [] int, ref nautyLabels: [] int, ref state: KavoshState): uint(64) throws {
    
    if chosenVerts.size < state.k || nautyLabels.size < state.k {
        //halt("Error: Arrays smaller than expected size");
    }
    
    // Step 1: Create normalized adjacency matrix
    var adjMatrix: [0..#(state.k * state.k)] int = 0;
    
    // Fill adjacency matrix using Nauty's labeling
    for i in 0..#state.k {
        for j in 0..#state.k {
            if i != j {
                var u = chosenVerts[nautyLabels[i] + 1];
                var w = chosenVerts[nautyLabels[j] + 1];
                var eid = getEdgeId(u, w, dstNodesG1, segGraphG1);
                if eid != -1 {
                    adjMatrix[i * state.k + j] = 1;
                }
            }
        }
    }

    // Step 2: Create a canonical ordering based on vertex properties
    var vertexSignatures: [0..#state.k] (int, int, int);  // (outDegree, inDegree, originalLabel)
    for i in 0..#state.k {
        var outDeg = 0;
        var inDeg = 0;
        for j in 0..#state.k {
            if adjMatrix[i * state.k + j] == 1 then outDeg += 1;
            if adjMatrix[j * state.k + i] == 1 then inDeg += 1;
        }
        vertexSignatures[i] = (outDeg, inDeg, i);
    }

    // Sort vertices by their signatures
    sort(vertexSignatures);

    // Step 3: Generate pattern using sorted order
    var pattern: uint(64) = 0;
    var pos = 0;
    
    // Create pattern by reading matrix in sorted vertex order
    for i in 0..#state.k {
        for j in 0..#state.k {
            if i != j {
                var srcIdx = vertexSignatures[i][2];  // original index
                var dstIdx = vertexSignatures[j][2];  // original index
                if adjMatrix[srcIdx * state.k + dstIdx] == 1 {
                    pattern |= 1:uint(64) << pos;
                }
            }
            pos += 1;
        }
    }

    if logLevel == LogLevel.DEBUG {
        writeln("Vertex signatures: ", vertexSignatures, " Generated pattern: ", pattern, " Original vertices: ", nodeMapGraphG1[chosenVerts]);

    }

    return pattern;
}

    proc generatePatternDirect(ref chosenVerts: [] int, ref nautyLabels: [] int, ref state: KavoshState): uint(64) throws {
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
            writeln("Generated pattern= ", pattern, " Nauty labels: ", nautyLabels, " Original chosenVerts: ", nodeMapGraphG1[chosenVerts]);
        }
        return pattern;
    }// End of generatePatternDirect

    // Explores subgraphs containing the root vertex,
    // expanding level by level until remainedToVisit = 0 (which means we have chosen k vertices).
 proc Explore(ref state: KavoshState, root: int, level: int, remainedToVisit: int) throws {
    try {
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

        if remainedToVisit == 0 {
            try {
                state.localsubgraphCount += 1;
                var (adjMatrix, chosenVerts) = prepareNaugtyArguments(state);
                var results: [0..<state.k] int = 0..<state.k;
                var performCheck: int = 1;
                var verbose: int = 0;

                var status = c_nautyClassify(adjMatrix, motifSize, results, performCheck, verbose);

                if status != 0 {
                    writeln("----------------------------------------");
                    writeln("$$ ERROR: Nauty Classification Failed");
                    writeln("$$ Root: ", root, " Level: ", level);
                    writeln("$$ Status: ", status);
                    writeln("$$ AdjMatrix: ", adjMatrix);
                    writeln("$$ ChosenVerts: ", chosenVerts);
                    writeln("$$ results: ", results);
                    writeln("----------------------------------------");
                    if status == -5 {
                        status = c_nautyClassify(adjMatrix, motifSize, results, performCheck, verbose);
                        // if status != 0 {
                        //     writeln("ERROR Again: Nauty Classification Failed");
                        //     halt();
                        // }
                    }
                    //halt();
                }

                var nautyLabels = results;
                //var pattern = generateCanonicalPattern(chosenVerts, nautyLabels, state);
                var pattern = generatePatternDirect(chosenVerts, nautyLabels, state);
                
                if logLevel == LogLevel.DEBUG {    
                    writeln("subgraph = ", adjMatrix, " Nauty returned: ", results, " status =", status, "pattern = ", pattern);
                }
                
                state.localmotifClasses.add(pattern);
                
                if logLevel == LogLevel.DEBUG {
                    writeln("state.localmotifClasses: ", state.localmotifClasses);
                }
                return;
            } catch e {
                writeln("----------------------------------------");
                writeln("ERROR in Base Case Processing");
                writeln("Location: root=", root, " level=", level);
                writeln("Error: ", e.message());
                writeln("State: localsubgraphCount=", state.localsubgraphCount);
                writeln("----------------------------------------");
                //halt();
            }
        }

        // Get children for this level
        try {
            initChildSet(state, root, level);
            const childCount = state.getChildSet(level, 0);

            for selSize in 1..remainedToVisit {
                if childCount < selSize {
                    if logLevel == LogLevel.DEBUG {
                        writeln("Not enough children (", childCount, ") to select ", selSize, " vertices at level ", level);
                    }
                    for i in 1..childCount {
                        state.visited.remove(state.getChildSet(level, i));
                    }
                    return;
                }

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

                Explore(state, root, level+1, remainedToVisit - selSize);
                ForwardGenerator(childCount, selSize, root, level, remainedToVisit, selSize, state);
            }

            for i in 1..childCount {
                state.visited.remove(state.getChildSet(level, i));
            }
            state.setSubgraph(level, 0, 0);

        } catch e {
            writeln("----------------------------------------");
            writeln("ERROR in Child Processing");
            writeln("Location: root=", root, " level=", level);
            writeln("Error: ", e.message());
            writeln("ChildCount: ", state.getChildSet(level, 0));
            writeln("RemainedToVisit: ", remainedToVisit);
            writeln("----------------------------------------");
            //halt();
        }
    } catch e {
        writeln("----------------------------------------");
        writeln("ERROR in Explore");
        writeln("Location: root=", root, " level=", level);
        writeln("Error: ", e.message());
        writeln("RemainedToVisit: ", remainedToVisit);
        writeln("State: subgraphCount=", state.localsubgraphCount);
        writeln("----------------------------------------");
        //halt();
    }
}


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



    proc patternToAdjMatrix(pattern: uint(64), k: int) throws {
    writeln("===== patternToAdjMatrix called =====");
    writeln("Input pattern: ", pattern);
    writeln("k value: ", k);

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
    }


    /* This function takes a set of patterns (represented as uint64) and motif size,
    runs Nauty on each pattern to find canonical forms, and returns:
    1. A set of unique motif classes
    2. A flat array containing all adjacency matrices of the unique motifs
    */
    proc verifyPatterns(globalClasses: set(uint(64)), motifSize: int) throws {
        var uniqueMotifClasses: set(uint(64));
        var motifCount = 0;

        var motifArr: [0..#(globalClasses.size * motifSize * motifSize)] int;
        
        // Process each pattern found
        for pattern in globalClasses {
            if pattern == 0 {
                writeln("$$$$$$$$$$$$$$$$$$$$We had BROKEN C we found and ignored it$$$$$$$$$$$$$$$$$$$$$$$");
                continue;
            }

            // Convert pattern to adjacency matrix
            var adjMatrix = patternToAdjMatrix(pattern, motifSize);
            var results: [0..<motifSize] int;
            // Run Nauty on the adjacency matrix
            var status = c_nautyClassify(adjMatrix, motifSize, results, 1, 1);
            
            if status != 0 {
                writeln("Warning: Nauty failed with status ", status, " for pattern ", pattern);
                continue;
            }
            
            // Check if Nauty returned canonical form equal to [0,1,2]
            var isCanonical = true;
            for i in 0..<motifSize {
                if results[i] != i {
                    isCanonical = false;
                    break;
                }
            }
            
            var matrixToAdd: [0..#(motifSize * motifSize)] int;
            if isCanonical {
                // If canonical, add original pattern and matrix
                uniqueMotifClasses.add(pattern);
                matrixToAdd = adjMatrix;
            } else {
                // If not canonical, generate new pattern from Nauty's labeling
                var nautyPattern = generateNautyPattern(adjMatrix, results, motifSize);
                uniqueMotifClasses.add(nautyPattern);
                matrixToAdd = patternToAdjMatrix(nautyPattern, motifSize);
            }

            // Add matrix to motifArr - each matrix takes motifSize^2 elements
            var startIdx = motifCount * motifSize * motifSize;
            for i in 0..#(motifSize * motifSize) {
                motifArr[startIdx + i] = matrixToAdd[i];
            }
            motifCount += 1;
        }

        // Create final array with exact size needed for found motifs
        var finalMotifArr: [0..#(motifCount * motifSize * motifSize)] int;
        for i in 0..#(motifCount * motifSize * motifSize) {
            finalMotifArr[i] = motifArr[i];
        }

        if logLevel == LogLevel.DEBUG {
            writeln("\nSummary:");
            writeln("Original patterns: ", globalClasses.size);
            writeln("Unique patterns: ", uniqueMotifClasses.size);
            writeln("Motif array size: ", finalMotifArr.size);
            // Calculate expected size
            writeln("Expected size (uniquePatterns × motifSize²): ", 
                    uniqueMotifClasses.size * motifSize * motifSize);
        }
    
    return (uniqueMotifClasses, finalMotifArr);
    }
    // New function to create pattern from adjMatrix and Nauty labeling
    proc generateNautyPattern(adjMatrix: [] int, nautyLabels: [] int, motifSize: int): uint(64) {
        var pattern: uint(64) = 0;
        var pos = 0;
        
        // Look at each possible edge in the new ordering
        for i in 0..#motifSize {
            for j in 0..#motifSize {
                if i != j {
                    // Check if edge exists after applying Nauty's labeling
                    var src = nautyLabels[i];
                    var dst = nautyLabels[j];
                    if adjMatrix[src * motifSize + dst] == 1 {
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
        if logLevel == LogLevel.DEBUG {
            writeln("Enumerate: starting enumeration over all vertices");
        }

        // forall v in 0..<n with (ref globalClasses, ref globalMotifCount) {
        forall v in 0..<n-k+1 with (ref globalClasses, ref globalMotifCount) {
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

    
    writeln("Starting motif counting with k=", k, " on a graph of ", n, " vertices.");
    writeln("Maximum degree: ", maxDeg);

    Enumerate(g1.n_vertices, motifSize, maxDeg );
    // Oliver: Now you can make your src and dst based on Classes that I gathered in 
    // motifClasses and return them to users 
    // we should decide to keep or delete (allmotifs list)


    

    writeln("**********************************************************************");


    writeln("\nglobalMotifCount: ", globalMotifCount.read());
    writeln("\nglobalClasses: ", globalClasses);
    writeln("\nglobalClasses.size: ", globalClasses.size);
    writeln("**********************************************************************");

    writeln("**********************************************************************");
    writeln("**********************************************************************");
    //try {
        var (uniqueMotifClasses, finalMotifArr) = verifyPatterns(globalClasses, motifSize);
        // writeln("Found ", count, " truly unique patterns after Nauty verification");
    // } catch e {
    //     writeln("Error during isomorphism checking: ", e.message());
    // }
    writeln("\nglobalMotifCount: ", globalMotifCount.read());
    writeln("\n uniqueMotifClasses: ", uniqueMotifClasses);
    writeln("\n finalMotifArr.size: ", finalMotifArr.size);

    var tempArr: [0..0] int;
    var srcPerMotif = makeDistArray(2*2, int);
    var dstPerMotif = makeDistArray(2*2, int);

    srcPerMotif[srcPerMotif.domain.low] = uniqueMotifClasses.size;
    // dstPerMotif[dstPerMotif.domain.low] = globalMotifCount.read();

    return (srcPerMotif, finalMotifArr, tempArr, tempArr);
  }// End of runMotifCounting

}// End of MotifCounting Module