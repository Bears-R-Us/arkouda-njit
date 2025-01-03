module SubgraphIsomorphism {
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
  use SubgraphIsomorphismMsg;
  use WellConnectedComponents; // for edge list sort
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use MultiTypeRegEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;
  use SymArrayDmap;
  use Unique;
  use ArgSortMsg;

  /** Keeps track of the isomorphic mapping state during the execution process of VF2.*/
  class State {
    var n1: int; // size of main graph
    var n2: int; // size of subgraph
  
    var D_core: domain(1) = {0..<n2};
    var core: [0..<n2] int;
    
    var Tin1: domain(int, parSafe=true); // in-neighbors of current state for main graph
    var Tout1: domain(int, parSafe=true); // out-neighbors of current state for main graph

    var Tin2: domain(int, parSafe=true); // in-neighbors of current state for subgraph
    var Tout2: domain(int, parSafe=true); // out-neighbors of current state for subgraph
    
    var depth:int; // recursion depth, when depth == n2 then all vertices are mapped.

    /** State initializer.*/
    proc init(n1: int, n2: int) {
      this.n1 = n1;
      this.n2 = n2;
      
      this.D_core = {0..<n2};
      this.core = -1;
      
      this.Tin1 = {1..0};
      this.Tout1 = {1..0};
      
      this.Tin2 = {1..0};
      this.Tout2 = {1..0};
      
      this.depth = 0;
    }
    
    /** Reset vectors during backtracking.*/
    proc reset() {
      this.D_core = {0..1};
      this.core = -1;

      this.Tin1  =  {1..0};
      this.Tout1 =  {1..0};

      this.Tin2  =  {1..0};
      this.Tout2 =  {1..0};

      this.depth = 0;
    }
    
    /** Method to create a copy of the instance.*/
    proc clone(): owned State throws {
      var newState = new owned State(this.n1, this.n2);
      newState.core = this.core;

      newState.Tin1 = this.Tin1;
      newState.Tout1 = this.Tout1;
      
      newState.Tin2 = this.Tin2;
      newState.Tout2 = this.Tout2;
      
      newState.depth = this.depth;

      return newState;
    }

    /** Check if a given node is mapped in g1.*/
    proc isMappedn1(n1: int): bool {
      var Mapflag: bool = false;
      for i in D_core do if this.core[i] == n1 then Mapflag = true;
      return Mapflag;
    }
    
    /** Check if a given node is mapped in g2.*/
    proc isMappedn2(n2: int): bool {
      return (this.core[n2] != -1);
    }
  } // end of State class

  /*
    Given a vertex or edge index returns true if a vertex or edge from the main host graph
    matches a given vertex or edge from a subgraph. 
    
    NOTE: checking categoricals is very time consuming as internal indices need to be mapped to 
    strings and then compared. Users should be encouraged to maintain their own integer 
    categorical consistencies and use integer attribute matching instead.
  */
  proc doAttributesMatch(graphIdx, subgraphIdx, const ref graphAttributes, const ref subgraphAttributes, 
                         matchType:string, st: borrowed SymTab) throws {
    var outerMatch:bool;
    var matchCounter:int = 0;
    if matchType == "and" then outerMatch = true;
    if matchType == "or" then outerMatch = false;
    for (k,v) in zip(subgraphAttributes.keys(), subgraphAttributes.values()) {
      if !graphAttributes.contains(k) then continue; // check if attribute exists in graph
      if v[1] != graphAttributes[k][1] then continue; // check if types are same
      var innerMatch:bool;

      // Check the actual data.
      select v[1] {
        when "Categorical" {
          var subgraphArrEntry = (st.registry.tab(v[0])):shared CategoricalRegEntry;
          const ref subgraphArr = toSymEntry(getGenericTypedArrayEntry(subgraphArrEntry.codes, st), int).a;
          const ref subgraphCats = getSegString(subgraphArrEntry.categories, st);

          var graphArrEntry = (st.registry.tab(graphAttributes[k][0])):shared CategoricalRegEntry;
          const ref graphArr = toSymEntry(getGenericTypedArrayEntry(graphArrEntry.codes, st), int).a;
          const ref graphCats = getSegString(graphArrEntry.categories, st);

          innerMatch = (subgraphCats[subgraphArr[subgraphIdx]] == graphCats[graphArr[graphIdx]]);
          matchCounter += 1;
        }
        when "Strings" {
          var subgraphStrings = getSegString(v[0], st);
          var graphStrings = getSegString(graphAttributes[k][0], st);

          innerMatch = subgraphStrings[subgraphIdx] == graphStrings[graphIdx];
          matchCounter += 1;
        }
        when "pdarray" {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(v[0], st);
          var graphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(graphAttributes[k][0], st);
          if subgraphArrEntry.dtype != graphArrEntry.dtype then continue;

          var etype = subgraphArrEntry.dtype;
          select etype {
            when (DType.Int64) {
              const ref subgraphArr = toSymEntry(subgraphArrEntry, int).a;
              const ref graphArr = toSymEntry(graphArrEntry, int).a;
              innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              matchCounter += 1;
            }
            when (DType.UInt64) {
              const ref subgraphArr = toSymEntry(subgraphArrEntry, uint).a;
              const ref graphArr = toSymEntry(graphArrEntry, uint).a;
              innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              matchCounter += 1;
            }
            when (DType.Float64) {
              const ref subgraphArr = toSymEntry(subgraphArrEntry, real).a;
              const ref graphArr = toSymEntry(graphArrEntry, real).a;
              innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              matchCounter += 1;
            }
            when (DType.Bool) {
              const ref subgraphArr = toSymEntry(subgraphArrEntry, bool).a;
              const ref graphArr = toSymEntry(graphArrEntry, bool).a;
              innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              matchCounter += 1;
            }
          }
        }
      }
      if matchType == "or" then outerMatch = outerMatch || innerMatch;
      if matchType == "and" then outerMatch = outerMatch && innerMatch;
      
      // For or check, if at least one of the checks yields true, then no other checks need to be
      // made.
      if matchType == "or" && outerMatch then return true;
    }
    
    // Since the default `outerMatch` for "and" is true, then if no checks were actually done, 
    // then we should return false.
    if matchType == "and" && matchCounter == 0 then return false;

    // Alternatively, if there were no matches performed, and the matching type is "or" then return
    // true.
    if matchType == "or" && matchCounter == 0 then return true;

    else return outerMatch;
  } // end of doAttributesMatch

  /* Maps to track the probability distributions generated per attribute type. */
  var edgeCategoricalProbabilityDistributions = new map(string, map(string, real));
  var edgeStringsProbabilityDistributions = new map(string, map(string,real));
  var edgeIntProbabilityDistributions = new map(string, map(int, real));
  var edgeUIntProbabilityDistributions = new map(string, map(uint, real));
  var edgeRealProbabilityDistributions = new map(string, map(real, real));
  var edgeBoolProbabilityDistributions = new map(string, map(bool, real));

  var nodeCategoricalProbabilityDistributions = new map(string, map(string, real));
  var nodeStringsProbabilityDistributions = new map(string, map(string,real));
  var nodeIntProbabilityDistributions = new map(string, map(int, real));
  var nodeUIntProbabilityDistributions = new map(string, map(uint, real));
  var nodeRealProbabilityDistributions = new map(string, map(real, real));
  var nodeBoolProbabilityDistributions = new map(string, map(bool, real));

  /* Generates the probability distribution for given subgraph attributes derived from the host
     graph. */
  proc generateProbabilityDistribution(const ref subgraphAttributes, const ref graphAttributes, 
                                       attributeBelongsTo:string, st: borrowed SymTab) throws {
    for (k,v) in zip(subgraphAttributes.keys(), subgraphAttributes.values()) {
      if !graphAttributes.contains(k) then continue; // check if attribute exists in graph
      if v[1] != graphAttributes[k][1] then continue; // check if types are same

      // Check the actual data.
      select v[1] {
        when "Categorical" {
          var graphArrEntry = (st.registry.tab(graphAttributes[k][0])):shared CategoricalRegEntry;
          const ref graphArr = toSymEntry(getGenericTypedArrayEntry(graphArrEntry.codes, st), int).a;
          const ref graphCats = getSegString(graphArrEntry.categories, st);
          
          var (values, counts) = uniqueSort(graphArr);
          var probMap = new map(string, real);
          for (v,c) in zip (values,counts) do probMap.add(graphCats[v], c:real / graphArr.size:real);

          if attributeBelongsTo == "edge" then 
            edgeCategoricalProbabilityDistributions.add(k, probMap);
          else
            nodeCategoricalProbabilityDistributions.add(k, probMap);
        }
        when "Strings" {
          var graphStrings = getSegString(graphAttributes[k][0], st);
          var (uo, uv, counts, inv) = uniqueGroup(graphStrings);
          
          var values = getSegString(uo, uv, st);
          var probMap = new map(string, real);
          for (v,c) in zip (counts.domain, counts) do probMap.add(values[v], c:real / graphStrings.size:real);

          if attributeBelongsTo == "edge" then 
            edgeStringsProbabilityDistributions.add(k, probMap);
          else
            nodeStringsProbabilityDistributions.add(k, probMap);
        }
        when "pdarray" {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(v[0], st);
          var graphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(graphAttributes[k][0], st);
          if subgraphArrEntry.dtype != graphArrEntry.dtype then continue;

          var etype = subgraphArrEntry.dtype;
          select etype {
            when (DType.Int64) {
              const ref graphArr = toSymEntry(graphArrEntry, int).a;
              
              var (values, counts) = uniqueSort(graphArr);
              var probMap = new map(int, real);
              for (v,c) in zip (values,counts) do probMap.add(v, c:real / graphArr.size:real);

              if attributeBelongsTo == "edge" then 
                edgeIntProbabilityDistributions.add(k, probMap);
              else
                nodeIntProbabilityDistributions.add(k, probMap);
            }
            when (DType.UInt64) {
              const ref graphArr = toSymEntry(graphArrEntry, uint).a;
              
              var (values, counts) = uniqueSort(graphArr);
              var probMap = new map(uint, real);
              for (v,c) in zip (values,counts) do probMap.add(v, c:real / graphArr.size:real);

              if attributeBelongsTo == "edge" then 
                edgeUIntProbabilityDistributions.add(k, probMap);
              else
                nodeUIntProbabilityDistributions.add(k, probMap);
            }
            when (DType.Float64) {
              const ref graphArr = toSymEntry(graphArrEntry, real).a;
              
              var (values, counts) = uniqueSort(graphArr);
              var probMap = new map(real, real);
              for (v,c) in zip (values,counts) do probMap.add(v, c:real / graphArr.size:real);

              if attributeBelongsTo == "edge" then 
                edgeRealProbabilityDistributions.add(k, probMap);
              else
                nodeRealProbabilityDistributions.add(k, probMap);
            }
            when (DType.Bool) {
              const ref graphArr = toSymEntry(graphArrEntry, bool).a;
              
              var (values, counts) = uniqueSort(graphArr);
              var probMap = new map(bool, real);
              for (v,c) in zip (values,counts) do probMap.add(v, c:real / graphArr.size:real);

              if attributeBelongsTo == "edge" then 
                edgeBoolProbabilityDistributions.add(k, probMap);
              else
                nodeBoolProbabilityDistributions.add(k, probMap);
            }
          }
        }
      }
    }
  }

  /* Given a subgraph and host graph probability distribution, generates the probability of each
     vertex and edge with given attributes to appear in the host graph. */
  proc getSubgraphProbabilities(subgraph: SegGraph, st: borrowed SymTab) throws {
    const ref src = toSymEntry(subgraph.getComp("SRC_SDI"), int).a;
    const ref dst = toSymEntry(subgraph.getComp("DST_SDI"), int).a;
    const ref nodeMap = toSymEntry(subgraph.getComp("VERTEX_MAP_SDI"), int).a;
    var nodeAttributes = subgraph.getNodeAttributes();
    var edgeAttributes = subgraph.getEdgeAttributes();

    var edgeProbabilities = makeDistArray(src.size, real);
    var nodeProbabilities = makeDistArray(nodeMap.size, real);
    edgeProbabilities = 1; nodeProbabilities = 1;

    // Calculate the probabilities of each vertex appearing based on the distribution of 
    // probabilities created from the host graph. This is done per attribute type for each vertex.
    if nodeAttributes.size > 0 {
      for u in nodeMap.domain {
        for k in nodeCategoricalProbabilityDistributions.keys() {
          var subgraphArrEntry = (st.registry.tab(nodeAttributes[k][0])):shared CategoricalRegEntry;
          const ref subgraphArr = toSymEntry(getGenericTypedArrayEntry(subgraphArrEntry.codes, st), int).a;
          const ref subgraphCats = getSegString(subgraphArrEntry.categories, st);
          
          nodeProbabilities[u] *= nodeCategoricalProbabilityDistributions[k][subgraphCats[subgraphArr[u]]];
        }
        for k in nodeStringsProbabilityDistributions.keys() {
          var subgraphStrings = getSegString(nodeAttributes[k][0], st);

          nodeProbabilities[u] *= nodeStringsProbabilityDistributions[k][subgraphStrings[u]];
        }
        for k in nodeIntProbabilityDistributions.keys() {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(nodeAttributes[k][0], st);
          const ref subgraphArr = toSymEntry(subgraphArrEntry, int).a;

          nodeProbabilities[u] *= nodeIntProbabilityDistributions[k][subgraphArr[u]];
        }
        for k in nodeUIntProbabilityDistributions.keys() {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(nodeAttributes[k][0], st);
          const ref subgraphArr = toSymEntry(subgraphArrEntry, uint).a;

          nodeProbabilities[u] *= nodeUIntProbabilityDistributions[k][subgraphArr[u]];
        }
        for k in nodeRealProbabilityDistributions.keys() {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(nodeAttributes[k][0], st);
          const ref subgraphArr = toSymEntry(subgraphArrEntry, real).a;

          nodeProbabilities[u] *= nodeRealProbabilityDistributions[k][subgraphArr[u]];
        }
        for k in nodeBoolProbabilityDistributions.keys() {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(nodeAttributes[k][0], st);
          const ref subgraphArr = toSymEntry(subgraphArrEntry, bool).a;

          nodeProbabilities[u] *= nodeBoolProbabilityDistributions[k][subgraphArr[u]];
        }
      }
    }

    // Calculate the probabilities of each edge appearing based on the distribution of 
    // probabilities created from the host graph. This is done per attribute type for each edge.
    // Further, the probabilities of the vertices that make up the endpoints are combined into the
    // edge probabilities.
    if edgeAttributes.size > 0 {
      for (u,v,i) in zip(src, dst, src.domain) {
        for k in edgeCategoricalProbabilityDistributions.keys() {
          var subgraphArrEntry = (st.registry.tab(edgeAttributes[k][0])):shared CategoricalRegEntry;
          const ref subgraphArr = toSymEntry(getGenericTypedArrayEntry(subgraphArrEntry.codes, st), int).a;
          const ref subgraphCats = getSegString(subgraphArrEntry.categories, st);
          
          edgeProbabilities[i] *= edgeCategoricalProbabilityDistributions[k][subgraphCats[subgraphArr[i]]];
        }
        for k in edgeStringsProbabilityDistributions.keys() {
          var subgraphStrings = getSegString(edgeAttributes[k][0], st);
          
          edgeProbabilities[i] *= edgeStringsProbabilityDistributions[k][subgraphStrings[i]];
        }
        for k in edgeIntProbabilityDistributions.keys() {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(edgeAttributes[k][0], st);
          const ref subgraphArr = toSymEntry(subgraphArrEntry, int).a;
          
          edgeProbabilities[i] *= edgeIntProbabilityDistributions[k][subgraphArr[i]];
        }
        for k in edgeUIntProbabilityDistributions.keys() {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(edgeAttributes[k][0], st);
          const ref subgraphArr = toSymEntry(subgraphArrEntry, uint).a;
          
          edgeProbabilities[i] *= edgeUIntProbabilityDistributions[k][subgraphArr[i]];
        }
        for k in edgeRealProbabilityDistributions.keys() {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(edgeAttributes[k][0], st);
          const ref subgraphArr = toSymEntry(subgraphArrEntry, real).a;
          
          edgeProbabilities[i] *= edgeRealProbabilityDistributions[k][subgraphArr[i]];
        }
        for k in edgeBoolProbabilityDistributions.keys() {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(edgeAttributes[k][0], st);
          const ref subgraphArr = toSymEntry(subgraphArrEntry, bool).a;
          
          edgeProbabilities[i] *= edgeBoolProbabilityDistributions[k][subgraphArr[i]];
        }
        edgeProbabilities[i] *= nodeProbabilities[u] * nodeProbabilities[v];
      }
    }

    return (edgeProbabilities, nodeProbabilities);
  }

  
  // /* Generates a mapping for old vertex names to new vetrex names. */
  // proc getSubgraphReordering(subgraph: SegGraph, st: borrowed SymTab) throws {
  //   const ref src = toSymEntry(subgraph.getComp("SRC_SDI"), int).a;
  //   const ref dst = toSymEntry(subgraph.getComp("DST_SDI"), int).a;
  //   const ref seg = toSymEntry(subgraph.getComp("SEGMENTS_SDI"), int).a;
  //   const ref srcR = toSymEntry(subgraph.getComp("SRC_R_SDI"), int).a;
  //   const ref dstR = toSymEntry(subgraph.getComp("DST_R_SDI"), int).a;
  //   const ref segR = toSymEntry(subgraph.getComp("SEGMENTS_R_SDI"), int).a;
  //   const ref nodeMap = toSymEntry(subgraph.getComp("VERTEX_MAP_SDI"), int).a;
  //   var nodeAttributes = subgraph.getNodeAttributes();
  //   var edgeAttributes = subgraph.getEdgeAttributes();
    
  //   // Get the probabilities of each edge and vertex from the subgraph appearing in the main graph.
  //   var (edgeProbabilities, nodeProbabilities) = getSubgraphProbabilities(subgraph, st);

  //   // Create a map of old internal vertex names to new internal vertex names. -1 is the default.
  //   var reorderedNodes = new map(int, int);
  //   for u in nodeMap.domain do reorderedNodes.add(u, -1);

  //   // Find the edges and vertices with lowest probability. If no edge and/or vertex attributes have
  //   // been defined, then these probabilities should default to edge 0 and vertex 0.
  //   var sortedIdxEdgeProbabilities = argsortDefault(edgeProbabilities);
  //   var sortedIdxNodeProbabilities = argsortDefault(nodeProbabilities);
  //   var rarestEdge = sortedIdxEdgeProbabilities[0];
  //   var rarestNode = sortedIdxNodeProbabilities[0];

  //   // Keep track of the edges and nodes that have been mapped already.
  //   var mappedEdges = makeDistArray(src.size, bool);
  //   var mappedNodes = makeDistArray(nodeMap.size, bool);
  //   mappedEdges = false; mappedNodes = false;

  //   // writeln("src = ", src);
  //   // writeln("dst = ", dst);
  //   // writeln("probs = ", edgeProbabilities);
  //   // writeln();
  //   // writeln("nodes = ", nodeMap);
  //   // writeln("probs = ", nodeProbabilities);
  //   // writeln();
  //   // writeln("rarestEdge = ", src[rarestEdge], " --> ", dst[rarestEdge]);
  //   // writeln("rarestNode = ", rarestNode);
  //   // writeln();

  //   var outDegree = makeDistArray(nodeMap.size, int);
  //   var inDegree = makeDistArray(nodeMap.size, int);
  //   var totalDegree = makeDistArray(nodeMap.size, int);

  //   // Get structural information for subgraph. 
  //   for u in nodeMap.domain {
  //     outDegree[u] = seg[u+1] - seg[u];
  //     inDegree[u] = segR[u+1] - segR[u];
  //     totalDegree[u] = outDegree[u] + inDegree[u];
  //   }

  //   var reorderComplete = false;
  //   /**********************************************************************************************/
  //   /**********************************************************************************************/
  //   /********************************************CASE 1********************************************/
  //   /**********************************************************************************************/
  //   /**********************************************************************************************/
  //   /* Edge attributes exist. This means that we want to create the reordering based on the 
  //      probabilities of each edge appearing. Starting from the rarest edge and then picking amongst
  //      the rarest edges connected to either starting vertex and continuing until all vertices 
  //      have been remapped. */
  //   if edgeAttributes.size > 0 {
  //     reorderedNodes[src[rarestEdge]] = 0;
  //     reorderedNodes[dst[rarestEdge]] = 1;
  //     mappedEdges[rarestEdge] = true;
  //     mappedNodes[src[rarestEdge]] = true;
  //     mappedNodes[dst[rarestEdge]] = true;

  //     var nextNodeName = 2;
  //     var currRarestEdge = rarestEdge;
  //     while !reorderComplete { // loop until all the vertices have been remapped
  //       var nextPossibleEdges = new list((int,int,int)); // tuple of u --> v and edge id e
  //       var currProbabilities = new list(real); // used to keep candidate probabilities
  //       var u = src[currRarestEdge];
  //       var v = dst[currRarestEdge];

  //       /* Get all of the out neighbors and in neighbors of the currently rarest edge. */
  //       for outNeighbor in dst[seg[u]..<seg[u+1]] {
  //         var e = getEdgeId(u, outNeighbor, dst, seg);
  //         if !mappedEdges[e] && !mappedNodes[outNeighbor] {
  //           nextPossibleEdges.pushBack((u, outNeighbor, e));
  //           currProbabilities.pushBack(edgeProbabilities[e]);
  //         }
  //       }
        
  //       for outNeighbor in dst[seg[v]..<seg[v+1]] {
  //         var e = getEdgeId(v, outNeighbor, dst, seg);
  //         if !mappedEdges[e] && !mappedNodes[outNeighbor] {
  //           nextPossibleEdges.pushBack((v, outNeighbor, e));
  //           currProbabilities.pushBack(edgeProbabilities[e]);
  //         }
  //       }

  //       for inNeighbor in dstR[segR[u]..<segR[u+1]] {
  //         var e = getEdgeId(inNeighbor, u, dst, seg);
  //         if !mappedEdges[e] && !mappedNodes[inNeighbor] {
  //           nextPossibleEdges.pushBack((inNeighbor, u, e));
  //           currProbabilities.pushBack(edgeProbabilities[e]);
  //         }
  //       }

  //       for inNeighbor in dstR[segR[v]..<segR[v+1]] {
  //         var e = getEdgeId(inNeighbor, v, dst, seg);
  //         if !mappedEdges[e] && !mappedNodes[inNeighbor] {
  //           nextPossibleEdges.pushBack((inNeighbor, v, e));
  //           currProbabilities.pushBack(edgeProbabilities[e]);
  //         }
  //       }

  //       /* The end of a certain path was reached, but unmapped vertices remain. */
  //       if nextPossibleEdges.size <= 0 && nextNodeName < nodeMap.size {
  //         /* Iterate over all remaining edges, adding their probabilities to find the lowest. */
  //         for (p,e) in zip(mappedEdges, mappedEdges.domain) {
  //           if p == false {
  //             nextPossibleEdges.pushBack((src[e], dst[e], e));
  //             currProbabilities.pushBack(edgeProbabilities[e]);
  //           }
  //         }
  //         var idx = argsortDefault(currProbabilities.toArray());
  //         var e = nextPossibleEdges[idx[0]][2];
  //         var u = src[e];
  //         var v = dst[e];

          

  //         /* Check to see if two edges have the same probability. */
  //         var needsTieBreaker = false;
  //         if idx.size > 1 {
  //           if currProbabilities[e] == currProbabilities[nextPossibleEdges[idx[1]][2]] then needsTieBreaker = true;
  //         }
  //         // TODO: Code the tie-breaker.

  //         if !mappedNodes[u] && !mappedNodes[v] { // Neither end points have been mapped.
  //           reorderedNodes[u] = nextNodeName;
  //           reorderedNodes[v] = nextNodeName + 1;
  //           mappedEdges[e] = true;
  //           mappedNodes[u] = true;
  //           mappedNodes[v] = true;

  //           nextNodeName += 2;
  //           currRarestEdge = e;
  //           if nextNodeName == nodeMap.size then reorderComplete = true;
  //           continue;
  //         } else if !mappedNodes[u] && mappedNodes[v] { // Only the destination has been mapped.
  //           reorderedNodes[u] = nextNodeName;
  //           mappedEdges[e] = true;
  //           mappedNodes[u] = true;

  //           nextNodeName += 1;
  //           currRarestEdge = e;
  //           if nextNodeName == nodeMap.size then reorderComplete = true;
  //           continue;
  //         } else if mappedNodes[u] && !mappedNodes[v] { // Only the source has been mapped.
  //           reorderedNodes[v] = nextNodeName;
  //           mappedEdges[e] = true;
  //           mappedNodes[v] = true;

  //           nextNodeName += 1;
  //           currRarestEdge = e;
  //           if nextNodeName == nodeMap.size then reorderComplete = true;
  //           continue;
  //         } else {
  //           writeln("Something catastrophic has gone wrong!");
  //         }
  //       }

  //       writeln("nextPossibleEdges = ", nextPossibleEdges);

  //       if currProbabilities.size >= 1 {
  //         /* Sort the probabilities of current candidate edges to be remapped. */
  //         var idx = argsortDefault(currProbabilities.toArray());

  //         /* Check to see if two edges have the same probability. */
  //         var needsTieBreaker = false;
  //         if idx.size > 1 {
  //           if currProbabilities[idx[0]] == currProbabilities[idx[1]] then needsTieBreaker = true;
  //         }
  //         // TODO: Code the tie-breaker.

  //         /* Remap the remaining node of the chosen edge. */
  //         var nextEdge = nextPossibleEdges[idx[0]];
  //         writeln("nextEdge = ", nextEdge);
  //         if (nextEdge[0] == u || nextEdge[0] == v) && !mappedNodes[nextEdge[1]] {
  //           reorderedNodes[nextEdge[1]] = nextNodeName;
  //           mappedNodes[nextEdge[1]] = true;
  //         } else if (nextEdge[1] == u || nextEdge[1] == v) && !mappedNodes[nextEdge[0]] {
  //           reorderedNodes[nextEdge[0]] = nextNodeName;
  //           mappedNodes[nextEdge[0]] = true;
  //         }

  //         /* Update variables. */
  //         nextNodeName += 1;
  //         currRarestEdge = idx[0];
  //         if nextNodeName == nodeMap.size then reorderComplete = true;

  //         writeln();
  //       }
  //     }
  //   } else if nodeAttributes.size > 0 && edgeAttributes.size <= 0 {
  //     /********************************************************************************************/
  //     /********************************************************************************************/
  //     /*******************************************CASE 2*******************************************/
  //     /********************************************************************************************/
  //     /********************************************************************************************/
  //     /* Only node attributes exist. This means that we want to create the reordering based on the 
  //       probabilities of each node appearing. Starting from the rarest node and then picking amongst
  //       the rarest neighbors connected to this vertex we continue untill all vertices have been 
  //       remapped. */ 
  //     reorderedNodes[rarestNode] = 0;
  //     mappedNodes[rarestNode] = true;

  //     var nextNodeName = 1;
  //     var currRarestNode = rarestNode;
  //     while !reorderComplete { // loop until all the vertices have been remapped
  //       var nextPossibleNodes = new list(int); // adds all neighbors for a vertex not yet checked
  //       var currProbabilities = new list(real); // used to keep candidate probabilities
  //       var u = currRarestNode;

  //       /* Get all of the out neighbors and in neighbors of current rarest vertex. */
  //       for outNeighbor in dst[seg[u]..<seg[u+1]] {
  //         if !mappedNodes[outNeighbor] {
  //           nextPossibleNodes.pushBack(outNeighbor);
  //           currProbabilities.pushBack(nodeProbabilities[outNeighbor]);
  //         }
  //       }

  //       for inNeighbor in dstR[segR[u]..<segR[u+1]] {
  //         if !mappedNodes[inNeighbor] {
  //           nextPossibleNodes.pushBack(inNeighbor);
  //           currProbabilities.pushBack(nodeProbabilities[inNeighbor]);
  //         }
  //       }

  //       /* The end of a certain path was reached, but unmapped vertices remain. */
  //       if nextPossibleNodes.size <= 0 && nextNodeName < nodeMap.size {
  //         /* Iterate over all remaining vertices, adding their probabilities to find the lowest. */
  //         for (p,u) in zip(mappedNodes, mappedNodes.domain) do 
  //           if p == false {
  //             nextPossibleNodes.pushBack(u);
  //             currProbabilities.pushBack(nodeProbabilities[u]);
  //           }

  //         var idx = argsortDefault(currProbabilities.toArray());

  //         /* Check to see if two vertices have the same probability. */
  //         var needsTieBreaker = false;
  //         if idx.size > 1 {
  //           if currProbabilities[idx[0]] == currProbabilities[idx[1]] then needsTieBreaker = true;
  //         }
  //         // TODO: Code the tie-breaker.

  //         var u = nextPossibleNodes[idx[0]];
  //         reorderedNodes[u] = nextNodeName;
  //         mappedNodes[u] = true;

  //         nextNodeName += 1;
  //         currRarestNode = u;
  //         if nextNodeName == nodeMap.size then reorderComplete = true;
  //         continue;
  //       }

  //       writeln("nextPossibleNodes = ", nextPossibleNodes);

  //       if currProbabilities.size >= 1 {
  //         /* Sort the probabilities of current candidate edges to be remapped. */
  //         var idx = argsortDefault(currProbabilities.toArray());

  //         /* Check to see if two nodes have the same probability. */
  //         var needsTieBreaker = false;
  //         if idx.size > 1 {
  //           if currProbabilities[idx[0]] == currProbabilities[idx[1]] then needsTieBreaker = true;
  //         }
  //         // TODO: Code the tie-breaker.

  //         /* Remap the selected node. */
  //         var nextNode = nextPossibleNodes[idx[0]];
  //         reorderedNodes[nextNode] = nextNodeName;
  //         mappedNodes[nextNode] = true;

  //         /* Update variables. */
  //         nextNodeName += 1;
  //         currRarestNode = nextNode;
  //         if nextNodeName == nodeMap.size then reorderComplete = true;

  //         writeln();
  //       }
  //     }
  //   } else if nodeAttributes.size <= 0 && edgeAttributes.size <= 0 {
  //     /********************************************************************************************/
  //     /********************************************************************************************/
  //     /*******************************************CASE 3*******************************************/
  //     /********************************************************************************************/
  //     /********************************************************************************************/
  //     /* No vertex or node attributes exist. This means we want to create the reordering based on 
  //        the degrees of each vertex. Starting with the vertex with most degree and then picking 
  //        amongst its neighbors the next vertex with most degree. This is repeated until all the 
  //        vertices have been reordered. */
  //     var outDegreeIdx = argsortDefault(outDegree);
  //     var inDegreeIdx = argsortDefault(inDegree);
  //     var totalDegreeIdx = argsortDefault(totalDegree);
  //     var outDom = outDegreeIdx.domain;
  //     var inDom = inDegreeIdx.domain;

  //     var mostImportantNode = if outDegree[outDegreeIdx[outDom.high]] != 0 then outDegreeIdx[outDom.high]
  //                             else inDegreeIdx[inDom.high];

  //     writeln("STARTING STRUCTURAL REORDERING BELOW: ");
  //     writeln("Visiting ", mostImportantNode, " first...");
  //     reorderedNodes[mostImportantNode] = 0;
  //     mappedNodes[mostImportantNode] = true;

  //     var nextNodeName = 1;
  //     var currMostImportantNode = mostImportantNode;
  //     while !reorderComplete { // loop until all the vertices have been remapped
  //       var nextPossibleInNodes = new list(int); // adds in neighbors for a node not yet checked
  //       var inNodeOutDegrees = new list(int);
  //       var inNodeInDegrees = new list(int);

  //       var nextPossibleOutNodes = new list(int); // adds out neighbors for a node not yet checked
  //       var outNodeOutDegrees = new list(int);
  //       var outNodeInDegrees = new list(int);
        
  //       var u = currMostImportantNode;

  //       /* Get all of the out neighbors and in neighbors of current most important vertex. */
  //       for outNeighbor in dst[seg[u]..<seg[u+1]] {
  //         if !mappedNodes[outNeighbor] {
  //           nextPossibleOutNodes.pushBack(outNeighbor);
  //           outNodeOutDegrees.pushBack(outDegree[outNeighbor]);
  //           outNodeInDegrees.pushBack(inDegree[outNeighbor]);
  //         }
  //       }

  //       for inNeighbor in dstR[segR[u]..<segR[u+1]] {
  //         if !mappedNodes[inNeighbor] {
  //           nextPossibleInNodes.pushBack(inNeighbor);
  //           inNodeOutDegrees.pushBack(outDegree[inNeighbor]);
  //           inNodeInDegrees.pushBack(inDegree[inNeighbor]);
  //         }
  //       }

  //       /* The end of a certain path was reached, but unmapped vertices remain. */
  //       if nextPossibleOutNodes.size <= 0 && nextPossibleInNodes.size <= 0 && nextNodeName < nodeMap.size {
  //         var nextPossibleNodes = new list(int);
  //         var currOutDegrees = new list(int);
  //         var currInDegrees = new list(int);

  //         /* Iterate over all remaining vertices, adding their degrees to find the lowest. */
  //         for (p,u) in zip(mappedNodes, mappedNodes.domain) {
  //           if p == false {
  //             nextPossibleNodes.pushBack(u);
  //             currOutDegrees.pushBack(outDegree[u]);
  //             currInDegrees.pushBack(inDegree[u]);
  //           }
  //         }
  //         var outDegreeIdx = argsortDefault(currOutDegrees.toArray());
  //         var inDegreeIdx = argsortDefault(currInDegrees.toArray());
  //         var outDom = outDegreeIdx.domain;
  //         var inDom = inDegreeIdx.domain;

  //         var mostImportantNode = if currOutDegrees[outDegreeIdx[outDom.high]] != 0 then nextPossibleNodes[outDegreeIdx[outDom.high]]
  //                                 else nextPossibleNodes[inDegreeIdx[inDom.high]];            
  //         reorderedNodes[mostImportantNode] = nextNodeName;
  //         mappedNodes[mostImportantNode] = true;

  //         nextNodeName += 1;
  //         currMostImportantNode = mostImportantNode;
  //         if nextNodeName == nodeMap.size then reorderComplete = true;
  //         continue;
  //       }

  //       writeln("nextPossibleOutNodes = ", nextPossibleOutNodes);
  //       writeln("nextPossibleInNodes = ", nextPossibleInNodes);

  //       if nextPossibleOutNodes.size >= 1 || nextPossibleInNodes.size >= 1 {
  //         var outNodeOutDegreeIdx = argsortDefault(outNodeOutDegrees.toArray());
  //         var outNodeInDegreeIdx = argsortDefault(outNodeInDegrees.toArray());
  //         var inNodeOutDegreeIdx = argsortDefault(inNodeOutDegrees.toArray());
  //         var inNodeInDegreeIdx = argsortDefault(inNodeInDegrees.toArray());

  //         var outDom = outNodeOutDegreeIdx.domain;
  //         var inDom = inNodeInDegreeIdx.domain;
  //         var mostImportantNode:int;

  //         /* TODO: CONTINUE HERE. */
          
  //         if nextPossibleOutNodes.size >= 1 && nextPossibleInNodes.size >= 1 {
  //           mostImportantNode = if outNodeOutDegrees[outNodeOutDegreeIdx[outDom.high]] != 0 then nextPossibleOutNodes[outNodeOutDegreeIdx[outDom.high]]
  //                               else nextPossibleOutNodes[outNodeInDegreeIdx[inDom.high]];
  //         } else if nextPossibleOutNodes.size >= 1 && nextPossibleInNodes.size <= 0 {
  //           mostImportantNode = nextPossibleOutNodes[outDegreeIdx[outDom.high]];
  //         } else if nextPossibleOutNodes.size <= 0 && nextPossibleInNodes.size >= 1 {
  //           mostImportantNode = nextPossibleInNodes[inDegreeIdx[inDom.high]];
  //         }
           
  //         writeln("Visiting ", mostImportantNode, " now...");
  //         reorderedNodes[mostImportantNode] = nextNodeName;
  //         mappedNodes[mostImportantNode] = true;

  //         nextNodeName += 1;
  //         currMostImportantNode = mostImportantNode;
  //         if nextNodeName == nodeMap.size then reorderComplete = true;

  //         writeln();
  //       }
  //     }
  //   }

  //   writeln("reorderedNodes = ", reorderedNodes);
  //   return reorderedNodes;
  // }

  /* Computes the degree of a graph when only source and destination arrays are known. */
  proc computeDegrees(src, dst) throws {
    // Find unique nodes. 
    var uniqueNodesSet = new set(int);
    for (u,v) in zip(src,dst) { uniqueNodesSet.add(u); uniqueNodesSet.add(v); }
    var uniqueNodes = uniqueNodesSet.toArray();
    sort(uniqueNodes);

    // Initialize degree arrays.
    var inDegree = makeDistArray(uniqueNodes.size, int); inDegree = 0;
    var outDegree = makeDistArray(uniqueNodes.size, int); outDegree = 0;

    // Create a map to map nodes to their index in uniqueNodes.
    var nodeToIndex = new map(int, int);
    for (idx, node) in zip(uniqueNodes.domain, uniqueNodes) do nodeToIndex.add(node, idx);

    // Calculate out-degrees.
    for node in src do outDegree[nodeToIndex[node]] += 1;

    // Calculate in-degrees.
    for node in dst do inDegree[nodeToIndex[node]] += 1;

    // Calculate total degrees.
    var totalDegree = inDegree + outDegree;

    return (uniqueNodes, nodeToIndex, inDegree, outDegree, totalDegree);
  }

  /* When some vertex u is reindexed, then the degrees need to be updated. */
  proc updateDegrees(src, dst, uniqueNodes) throws {
    // Create a map to map nodes to their index in uniqueNodes.
    var nodeToIndex = new map(int, int);
    for (idx, node) in zip(uniqueNodes.domain, uniqueNodes) do nodeToIndex.add(node, idx);
    var inDegree = makeDistArray(uniqueNodes.size, int); inDegree = 0;
    var outDegree = makeDistArray(uniqueNodes.size, int); outDegree = 0;

    // Calculate out-degrees.
    for node in src do outDegree[nodeToIndex[node]] += 1;

    // Calculate in-degrees.
    for node in dst do inDegree[nodeToIndex[node]] += 1;

    // Calculate total degrees.
    var totalDegree = inDegree + outDegree;

    return (inDegree, outDegree, totalDegree);
  }

  /* Define a custom tuple comparator. */
  record CandidatesComparator {
    
    /* Comparator used for vertices. */
    proc compare(a: (int, real, int, int), b: (int, real, int, int)) {
      if a[1] != b[1] then return a[1] - b[1];
      else if a[1] == b[1] && a[2] != b[2] then return b[2] - a[2];
      else if a[1] == b[1] && a[2] == b[2] then return b[3] - a[3];
      else return b[3] - a[3];
    }
  }

  /* Generates a mapping of old vertex identifiers to new vertex identifiers. */
  proc getSubgraphReordering(subgraph: SegGraph, st: borrowed SymTab) throws {
    // Extract copies and references to subgraph source and destination arrays.
    var srcTemp = toSymEntry(subgraph.getComp("SRC_SDI"), int).a;
    var dstTemp = toSymEntry(subgraph.getComp("DST_SDI"), int).a;
    const ref src = toSymEntry(subgraph.getComp("SRC_SDI"), int).a;
    const ref dst = toSymEntry(subgraph.getComp("DST_SDI"), int).a;

    // Extract attribute information to decide if edge, vertex, or structural based reordering is 
    // to be used.
    var nodeAttributes = subgraph.getNodeAttributes();
    var edgeAttributes = subgraph.getEdgeAttributes();

    // Compute degrees.
    var (uniqueNodes, nodeToIndex, inDegree, outDegree, totalDegree) = computeDegrees(srcTemp, dstTemp);
    var reordering = nodeToIndex;
    for key in reordering.keys() do reordering.replace(key, -1);
    
    // Get the probabilities of each edge and vertex from the subgraph appearing in the main graph.
    var (edgeProbabilities, nodeProbabilities) = getSubgraphProbabilities(subgraph, st);

    writeln("initial srcTemp = ", srcTemp);
    writeln("initial dstTemp = ", dstTemp);
    writeln("uniqueNodes     = ", uniqueNodes);
    writeln("inDegree        = ", inDegree);
    writeln("outDegree       = ", outDegree);
    writeln("totalDegree     = ", totalDegree);

    if edgeAttributes.size == 0 { // There are no edge attributes, focus on vertices and/or structure.
      // Create an array of tuples tracking vertex probability, highest degree, and out-degree.
      var candidates = makeDistArray(uniqueNodes.size, (int,real,int,int));
      for i in candidates.domain do candidates[i] = (uniqueNodes[i], nodeProbabilities[i], totalDegree[i], outDegree[i]);
      var candidatesComparator: CandidatesComparator;
      sort(candidates, comparator=candidatesComparator);
      var replacedNodes = new list(int);

      writeln("candidates = ", candidates);

      // Select and remap the first given node.
      writeln("\nSelecting and remapping the first given node...");
      var selectedNode = candidates[0][0];
      var sortedIndex = 0;
      writef("Initially selected node %i was given sorted index %i\n", selectedNode, sortedIndex);

      // Swap the selected node with the first sorted index.
      for i in srcTemp.domain {
        if srcTemp[i] == selectedNode then srcTemp[i] = uniqueNodes[sortedIndex];
        else if srcTemp[i] == uniqueNodes[sortedIndex] then srcTemp[i] = selectedNode;

        if dstTemp[i] == selectedNode then dstTemp[i] = uniqueNodes[sortedIndex];
        else if dstTemp[i] == uniqueNodes[sortedIndex] then dstTemp[i] = selectedNode;
      }
      replacedNodes.pushBack(uniqueNodes[sortedIndex]);

      writeln("replacedNodes = ", replacedNodes);
      writeln("updated srcTemp = ", srcTemp);
      writeln("updated dstTemp = ", dstTemp);

      writeln("\nFirst node remapping finished, while loop begins...");
      // Loop until all vertices have been remapped.
      while replacedNodes.size < uniqueNodes.size {
        var currentNode = replacedNodes.last;
        var (inDegree, outDegree, totalDegree) = updateDegrees(srcTemp, dstTemp, uniqueNodes);
        
        // Select the out-neighbors of the current vertex and sort them based on candidacy. 
        var outNeighborsList = new list((int,real,int,int));
        for i in srcTemp.domain {
          var outNeighbor = dstTemp[i];
          if srcTemp[i] == currentNode && !replacedNodes.contains(outNeighbor) {
            outNeighborsList.pushBack((outNeighbor,
                                      nodeProbabilities[nodeToIndex[outNeighbor]],
                                      totalDegree[nodeToIndex[outNeighbor]],
                                      outDegree[nodeToIndex[outNeighbor]]));
          }
        }
        var outNeighbors = outNeighborsList.toArray();
        sort(outNeighbors, comparator=candidatesComparator);

        writef("\nChecking node %i with out-neighbors ", currentNode);
        write(outNeighbors);
        write("...\n");
        writeln("uniqueNodes = ", uniqueNodes);
        writeln("inDegree    = ", inDegree);
        writeln("outDegree   = ", outDegree);
        writeln("totalDegree = ", totalDegree);

        // If there are out-neighbors then perform the same swapping steps as above.
        if outNeighbors.size > 0 {
          var nextNode = outNeighbors[0][0];
          var sortedIndex = replacedNodes.size;

          for i in srcTemp.domain {
            if srcTemp[i] == nextNode then srcTemp[i] = uniqueNodes[sortedIndex];
            else if srcTemp[i] == uniqueNodes[sortedIndex] then srcTemp[i] = nextNode;

            if dstTemp[i] == nextNode then dstTemp[i] = uniqueNodes[sortedIndex];
            else if dstTemp[i] == uniqueNodes[sortedIndex] then dstTemp[i] = nextNode;
          }    

          replacedNodes.pushBack(uniqueNodes[sortedIndex]);

          writef("Next selected node %i was given sorted index %i\n", nextNode, sortedIndex);
          writeln("replacedNodes   = ", replacedNodes);
          writeln("updated srcTemp = ", srcTemp);
          writeln("updated dstTemp = ", dstTemp);    
        } else { // If there are no out-neighbors, then pick the next node from the remaining vertices.
          // Assemble remaining candidates, checking their probabilities and structure.
          var remainingCandidatesList = new list((int,real,int,int));
          for i in uniqueNodes.domain {
            var u = uniqueNodes[i];
            if !replacedNodes.contains(u) {
              remainingCandidatesList.pushBack((u,
                                                nodeProbabilities[i],
                                                totalDegree[i],
                                                outDegree[i]));
            }
          }
          var remainingCandidates = remainingCandidatesList.toArray();
          sort(remainingCandidates, comparator=candidatesComparator);

          writeln("remainingCandidates = ", remainingCandidates);
          if remainingCandidates.size > 0 {
            // Select first remaining candidate.
            var selectedNode = remainingCandidates[0][0];
            var sortedIndex = replacedNodes.size;

            for i in srcTemp.domain {
              if srcTemp[i] == selectedNode then srcTemp[i] = uniqueNodes[sortedIndex];
              else if srcTemp[i] == uniqueNodes[sortedIndex] then srcTemp[i] = selectedNode;

              if dstTemp[i] == selectedNode then dstTemp[i] = uniqueNodes[sortedIndex];
              else if dstTemp[i] == uniqueNodes[sortedIndex] then dstTemp[i] = selectedNode;
            }

            replacedNodes.pushBack(uniqueNodes[sortedIndex]);
            writef("Next selected node (no out-neighbors) %i was given sorted index %i\n", selectedNode, sortedIndex);
            writeln("replacedNodes   = ", replacedNodes);
            writeln("updated srcTemp = ", srcTemp);
            writeln("updated dstTemp = ", dstTemp);
          }
        }
      }
    } else { // There are edge attributes. Use edge probabilities.
      // Candidates are edge tuples, edge probability, and source and destination vertex probs.
      // It break ties on destination and source vertex probabilities, respectively.
      var candidates = makeDistArray(srcTemp.size, (int, real, int, int));
      for i in candidates.domain {
        var u = src[i];
        var v = dst[i];
        var edgeProb = edgeProbabilities[i];
        var combinedTotalDegree = totalDegree[u] + totalDegree[v];
        var combinedOutDegree = outDegree[u] + outDegree[v];
        candidates[i] = (i, edgeProb, combinedTotalDegree, combinedTotalDegree);
      }
      var candidatesComparator: CandidatesComparator;
      sort(candidates, comparator=candidatesComparator);
      var replacedNodes = new list(int);

      writeln("candidates = ", candidates);

      // Select and remap both of the vertices of the first given edge.
      writeln("\nSelecting and remapping the first given edge...");
      // First selected edge.
      var e = candidates[0][0];
      
      // Firstly, vertex u...
      var selectedNode = src[e];
      var sortedIndex = 0;
      writef("Source node %i was given sorted index %i\n", selectedNode, sortedIndex);
      for i in srcTemp.domain {
        if srcTemp[i] == selectedNode then srcTemp[i] = uniqueNodes[sortedIndex];
        else if srcTemp[i] == uniqueNodes[sortedIndex] then srcTemp[i] = selectedNode;

        if dstTemp[i] == selectedNode then dstTemp[i] = uniqueNodes[sortedIndex];
        else if dstTemp[i] == uniqueNodes[sortedIndex] then dstTemp[i] = selectedNode;
      }
      replacedNodes.pushBack(uniqueNodes[sortedIndex]);
      writeln("replacedNodes = ", replacedNodes);
      writeln("updated srcTemp = ", srcTemp);
      writeln("updated dstTemp = ", dstTemp);

      // Secondly, vertex v...
      selectedNode = dst[e];
      sortedIndex = 1;
      writef("Destination node %i was given sorted index %i\n", selectedNode, sortedIndex);
      for i in srcTemp.domain {
        if srcTemp[i] == selectedNode then srcTemp[i] = uniqueNodes[sortedIndex];
        else if srcTemp[i] == uniqueNodes[sortedIndex] then srcTemp[i] = selectedNode;

        if dstTemp[i] == selectedNode then dstTemp[i] = uniqueNodes[sortedIndex];
        else if dstTemp[i] == uniqueNodes[sortedIndex] then dstTemp[i] = selectedNode;
      }
      replacedNodes.pushBack(uniqueNodes[sortedIndex]);
      writeln("replacedNodes = ", replacedNodes);
      writeln("updated srcTemp = ", srcTemp);
      writeln("updated dstTemp = ", dstTemp);

      writeln("\nFirst edge remapping finished, while loop begins...");
      // Loop until all vertices have been remapped.
      while replacedNodes.size < uniqueNodes.size {
        var currentNode = replacedNodes.last;
        var (inDegree, outDegre, totalDegree) = updateDegrees(srcTemp, dstTemp, uniqueNodes);

        // Select the out-neighbors of the current vertex and sort them based on candidacy. 
        var outNeighborsList = new list((int,real,int,int));
        for i in srcTemp.domain {
          var outNeighbor = dstTemp[i];
          if srcTemp[i] == currentNode && !replacedNodes.contains(outNeighbor) {
            outNeighborsList.pushBack((outNeighbor,
                                      edgeProbabilities[nodeToIndex[outNeighbor]],
                                      totalDegree[nodeToIndex[outNeighbor]],
                                      outDegree[nodeToIndex[outNeighbor]]));
          }
        }
        var outNeighbors = outNeighborsList.toArray();
        sort(outNeighbors, comparator=candidatesComparator);

        writef("\nChecking node %i with out-neighbors ", currentNode);
        write(outNeighbors);
        write("...\n");
        writeln("uniqueNodes = ", uniqueNodes);
        writeln("inDegree    = ", inDegree);
        writeln("outDegree   = ", outDegree);
        writeln("totalDegree = ", totalDegree);

        // If there are out-neighbors then perform the same swapping steps as above.
        if outNeighbors.size > 0 {
          var nextNode = outNeighbors[0][0];
          var sortedIndex = replacedNodes.size;

          for i in srcTemp.domain {
            if srcTemp[i] == nextNode then srcTemp[i] = uniqueNodes[sortedIndex];
            else if srcTemp[i] == uniqueNodes[sortedIndex] then srcTemp[i] = nextNode;

            if dstTemp[i] == nextNode then dstTemp[i] = uniqueNodes[sortedIndex];
            else if dstTemp[i] == uniqueNodes[sortedIndex] then dstTemp[i] = nextNode;
          }    

          replacedNodes.pushBack(uniqueNodes[sortedIndex]);

          writef("Next selected node %i was given sorted index %i\n", nextNode, sortedIndex);
          writeln("replacedNodes   = ", replacedNodes);
          writeln("updated srcTemp = ", srcTemp);
          writeln("updated dstTemp = ", dstTemp);    
        } else { // If there are no out-neighbors, then pick the next node from the remaining vertices.
          // Assemble remaining candidates, checking their probabilities and structure.
          var remainingCandidatesList = new list((int,real,int,int));
          for i in uniqueNodes.domain {
            var u = uniqueNodes[i];
            if !replacedNodes.contains(u) {
              remainingCandidatesList.pushBack((u,
                                                edgeProbabilities[i],
                                                totalDegree[i],
                                                outDegree[i]));
            }
          }
          var remainingCandidates = remainingCandidatesList.toArray();
          sort(remainingCandidates, comparator=candidatesComparator);

          writeln("remainingCandidates = ", remainingCandidates);
          if remainingCandidates.size > 0 {
            // Select first remaining candidate.
            var selectedNode = remainingCandidates[0][0];
            var sortedIndex = replacedNodes.size;

            for i in srcTemp.domain {
              if srcTemp[i] == selectedNode then srcTemp[i] = uniqueNodes[sortedIndex];
              else if srcTemp[i] == uniqueNodes[sortedIndex] then srcTemp[i] = selectedNode;

              if dstTemp[i] == selectedNode then dstTemp[i] = uniqueNodes[sortedIndex];
              else if dstTemp[i] == uniqueNodes[sortedIndex] then dstTemp[i] = selectedNode;
            }

            replacedNodes.pushBack(uniqueNodes[sortedIndex]);
            writef("Next selected node (no out-neighbors) %i was given sorted index %i\n", selectedNode, sortedIndex);
            writeln("replacedNodes   = ", replacedNodes);
            writeln("updated srcTemp = ", srcTemp);
            writeln("updated dstTemp = ", dstTemp);
          }
        }
      }
    }

    // Save the reordering based off the new source and destination arrays.
    for (u, v, uNew, vNew) in zip(src, dst, srcTemp, dstTemp) {
      reordering[u] = uNew;
      reordering[v] = vNew;
    }

    return reordering;
  }



  /* Given a new permutation, reorder given attributes. Used for subgraph reordering. */
  proc getReorderedAttributes(attributes, perm, st) throws {
    var newAttributeMap = new map(string, (string, string));
    
    // Loop over edge attributes. Making new symbol table entries and saving them.
    for (k,v) in zip(attributes.keys(), attributes.values()) {
      var attributeName = k;
      var attributeStId = v[0];
      var attributeType = v[1];
      
      // Check the actual data.
      select attributeType {
        when "Categorical" {
          var subgraphArrEntry = (st.registry.tab(attributeStId)):shared CategoricalRegEntry;
          const ref subgraphArr = toSymEntry(getGenericTypedArrayEntry(subgraphArrEntry.codes, st), int).a;
          var subgraphCats = getSegString(subgraphArrEntry.categories, st);

          var newArr = subgraphArr[perm];
          var newCats = getSegString(subgraphArrEntry.categories, st);
          var arrName = st.nextName();
          st.addEntry(arrName, new shared SymEntry(newArr));
          
          var newEntry = new shared CategoricalRegEntry(arrName, 
                                                        subgraphArrEntry.categories,
                                                        subgraphArrEntry.permutation,
                                                        subgraphArrEntry.segments,
                                                        subgraphArrEntry.naCode);
          var categoricalName = st.nextName();
          st.registry.register_categorical(categoricalName, newEntry);
          newAttributeMap.add(attributeName, (categoricalName, attributeType));
        }
        when "Strings" {
          var subgraphStrings = getSegString(attributeStId, st);
          var (offsets, values) = subgraphStrings[perm];
          
          var offsetsEntry = createSymEntry(offsets);
          var valuesEntry = createSymEntry(values);
          var stringsEntry = new shared SegStringSymEntry(offsetsEntry, valuesEntry, string);
          var name = st.nextName();
          st.addEntry(name, stringsEntry);
          newAttributeMap.add(attributeName, (name, attributeType));
        }
        when "pdarray" {
          var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(attributeStId, st);
          var etype = subgraphArrEntry.dtype;

          select etype {
            when (DType.Int64) {
              const ref subgraphArr = toSymEntry(subgraphArrEntry, int).a;
              var newArr = subgraphArr[perm];

              var name = st.nextName();
              st.addEntry(name, new shared SymEntry(newArr));
              newAttributeMap.add(attributeName, (name, attributeType));
            }
            when (DType.UInt64) {
              const ref subgraphArr = toSymEntry(subgraphArrEntry, uint).a;
              var newArr = subgraphArr[perm];

              var name = st.nextName();
              st.addEntry(name, new shared SymEntry(newArr));
              newAttributeMap.add(attributeName, (name, attributeType));
            }
            when (DType.Float64) {
              const ref subgraphArr = toSymEntry(subgraphArrEntry, real).a;
              var newArr = subgraphArr[perm];

              var name = st.nextName();
              st.addEntry(name, new shared SymEntry(newArr));
              newAttributeMap.add(attributeName, (name, attributeType));
            }
            when (DType.Bool) {
              const ref subgraphArr = toSymEntry(subgraphArrEntry, bool).a;
              var newArr = subgraphArr[perm];

              var name = st.nextName();
              st.addEntry(name, new shared SymEntry(newArr));
              newAttributeMap.add(attributeName, (name, attributeType));
            }
          }
        }
      }
    }

    return newAttributeMap;
  }

  /* Given a node mapping of original vertex names to new vertex names and the original subgraph, 
     returns new structural and attribute arrays following the new reordering. */
  proc getReorderedSubgraph(nodeMapping, originalSubgraph, st) throws {
    const ref src = toSymEntry(originalSubgraph.getComp("SRC_SDI"), int).a;
    const ref dst = toSymEntry(originalSubgraph.getComp("DST_SDI"), int).a;
    const ref nodeMap = toSymEntry(originalSubgraph.getComp("VERTEX_MAP_SDI"), int).a;
    var nodeAttributes = originalSubgraph.getNodeAttributes();
    var edgeAttributes = originalSubgraph.getEdgeAttributes();

    // Generate new source and destination arrays.
    var newSrc = makeDistArray(src.size, int);
    var newDst = makeDistArray(dst.size, int);
    for (s, d, i, j) in zip(src, dst, newSrc.domain, newDst.domain) {
      newSrc[i] = nodeMapping[s];
      newDst[j] = nodeMapping[d];
    }

    // Sort the newly created edge list.
    var (sortedNewSrc, sortedNewDst) = sortEdgeList(newSrc, newDst);

    // Get the permutation that sorts the edges. This is needed to sort the attributes.
    var edgePerm = makeDistArray(src.size, int);
    for (i, sns, snd) in zip(edgePerm.domain, sortedNewSrc, sortedNewDst) {
      for (j, ns, nd) in zip(newSrc.domain, newSrc, newDst) {
        if sns == ns && snd == nd then edgePerm[i] = j;
      }
    }

    // Get the permutation that sorts the nodes. This is needed to sort the attributes.
    var newNodeMap = nodeMap;
    for (i,u) in zip(newNodeMap.domain, newNodeMap) do newNodeMap[i] = nodeMapping[u];
    var nodePerm = argsortDefault(newNodeMap);
    var sortedNodeMap = newNodeMap[nodePerm];

    // Reorder the attributes.
    var reorderedEdgeAttributes = getReorderedAttributes(edgeAttributes, edgePerm, st);
    var reorderedNodeAttributes = getReorderedAttributes(nodeAttributes, nodePerm, st);

    // Created reversed arrays.
    var srcR = sortedNewDst;
    var dstR = sortedNewSrc;
    var (sortedSrcR, sortedDstR) = sortEdgeList(srcR, dstR);

    // Generate segments arrays for both regular and reversed arrays.
    var (srcUnique, srcCounts) = Unique.uniqueFromSorted(sortedNewSrc);
    var neis = makeDistArray(nodeMap.size, int);
    neis = 0; 
    neis[srcUnique] = srcCounts;
    var segs = + scan neis; 
    var completeSegs = makeDistArray(nodeMap.size + 1, int);
    completeSegs[0] = 0;
    completeSegs[1..] = segs;

    var (srcRUnique, srcRCounts) = Unique.uniqueFromSorted(sortedSrcR);
    var neisR = makeDistArray(nodeMap.size, int);
    neisR = 0; 
    neisR[srcRUnique] = srcRCounts;
    var segsR = + scan neisR; 
    var completeSegsR = makeDistArray(nodeMap.size + 1, int);
    completeSegsR[0] = 0;
    completeSegsR[1..] = segsR;

    return (sortedNewSrc, sortedNewDst, completeSegs, sortedNodeMap, 
            sortedSrcR, sortedDstR, completeSegsR, 
            reorderedEdgeAttributes, reorderedNodeAttributes);
  }

  /* Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
  searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
  array that maps the isomorphic vertices of `g1` to those of `g2`. */
  proc runVF2(g1: SegGraph, g2: SegGraph, semanticCheckType: string, 
              sizeLimit: string, in timeLimit: int, in printProgressInterval: int,
              algType: string, returnIsosAs:string, reorder: bool, st: borrowed SymTab) throws {
    var numIso: int = 0;
    var numIsoAtomic: chpl__processorAtomicType(int) = 0;
    var semanticAndCheck = if semanticCheckType == "and" then true else false;
    var semanticOrCheck = if semanticCheckType == "or" then true else false;
    var matchLimit = if sizeLimit != "none" then sizeLimit:int else 0;
    var limitSize:bool = if matchLimit > 0 then true else false;
    var limitTime:bool = if timeLimit > 0 then true else false;
    var printProgressCheck:bool = if printProgressInterval > 0 then true else false;
    var stopper:atomic bool = false;
    timeLimit *= 60;

    // Extract the g1/G/g information from the SegGraph data structure.
    const ref srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    const ref dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    const ref segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
    const ref dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
    const ref segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;

    // Returns the map of attribute name to tuple of symbol table identifier and array data type
    // to be used to extract a given attribute array.
    var graphNodeAttributes = g1.getNodeAttributes();
    var subgraphNodeAttributesOriginal = g2.getNodeAttributes();
    var graphEdgeAttributes = g1.getEdgeAttributes();
    var subgraphEdgeAttributesOriginal = g2.getEdgeAttributes();

    // Generate the probability distributions for each attribute. Will be stored in module-level
    // maps for each datatype. This is only performed for the attributes that exist in both the
    // subgraph and the graph.
    if reorder {
      generateProbabilityDistribution(subgraphNodeAttributesOriginal, graphNodeAttributes, 
                                      "vertex", st);
      generateProbabilityDistribution(subgraphEdgeAttributesOriginal, graphEdgeAttributes, 
                                      "edge", st);
    }

    // Reorder the subgraph vertices and edges.
    var newOrdering = if reorder then getSubgraphReordering(g2, st) else new map(int, int);

    // Get a newly constructed subgraph from the reordering created above.
    var (newSrc,newDst,newSeg,newMap,newSrcR,newDstR,newSegR,newEdgeAttributes,newNodeAttributes) = 
        if reorder then getReorderedSubgraph(newOrdering, g2, st)
        else (makeDistArray(1, int), makeDistArray(1, int), makeDistArray(1, int),
              makeDistArray(1, int), makeDistArray(1, int), makeDistArray(1, int),
              makeDistArray(1, int), new map(string, (string, string)), 
              new map(string, (string, string)));

    // Extract the g2/H/h information from the SegGraph data structure.
    const ref srcNodesG2 = if reorder then newSrc
                           else toSymEntry(g2.getComp("SRC_SDI"), int).a;
    const ref dstNodesG2 = if reorder then newDst
                           else toSymEntry(g2.getComp("DST_SDI"), int).a;
    const ref segGraphG2 = if reorder then newSeg
                           else toSymEntry(g2.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG2 = if reorder then newSrcR
                       else toSymEntry(g2.getComp("SRC_R_SDI"), int).a;
    const ref dstRG2 = if reorder then newDstR
                       else toSymEntry(g2.getComp("DST_R_SDI"), int).a;
    const ref segRG2 = if reorder then newSegR
                       else toSymEntry(g2.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG2 = if reorder then newMap
                               else toSymEntry(g2.getComp("VERTEX_MAP_SDI"), int).a;

    var subgraphEdgeAttributes = if reorder then newEdgeAttributes 
                                 else subgraphEdgeAttributesOriginal;
    var subgraphNodeAttributes = if reorder then newNodeAttributes
                                 else subgraphNodeAttributesOriginal;

    // Get the number of vertices and edges for each graph.
    var nG1 = nodeMapGraphG1.size;
    var mG1 = srcNodesG1.size;
    var nG2 = nodeMapGraphG2.size;
    var mG2 = srcNodesG2.size;

    // Check to see if there are vertex and edge attributes.
    var noVertexAttributes = if subgraphNodeAttributes.size == 0 then true else false;
    var noEdgeAttributes = if subgraphEdgeAttributes.size == 0 then true else false;

    // Timer for print-outs during execution.
    var timer:stopwatch;
    timer.start();

    /* Pick the vertices from the host graph that can be mapped to vertex 0 in the data graph. */
    proc vertexPicker() throws {
      var vertexFlagger: [0..<g1.n_vertices] bool = false;
      var Tin_0 = segRG2[1] - segRG2[0];
      var Tout_0 = segGraphG2[1] - segGraphG2[0];

      forall v in 0..<g1.n_vertices {
        var inNeighborsg1 = segRG1[v+1] - segRG1[v];            
        var outNeighborsg1 = segGraphG1[v+1] - segGraphG1[v];

        if semanticAndCheck {
          if doAttributesMatch(v, 0, graphNodeAttributes, subgraphNodeAttributes, "and", st) && (inNeighborsg1 >= Tin_0) && (outNeighborsg1 >= Tout_0)
            then vertexFlagger[v] = true;
        } else if semanticOrCheck {
          if doAttributesMatch(v, 0, graphNodeAttributes, subgraphNodeAttributes, "or", st) && (inNeighborsg1 >= Tin_0) && (outNeighborsg1 >= Tout_0)
            then vertexFlagger[v] = true;
        } else { vertexFlagger[v] = true; }
      }

      return vertexFlagger;
    }

    /* Pick the edges from the host graph that can be mapped to edge 0 of the data graph. */
    proc edgePicker(checkVertices:bool = false) throws {
      var edgeFlagger: [0..<g1.n_edges] bool = false;

      // Get the first edge of the subgraph. Since the edge list is pre-sorted, then the first edge
      // will always be at index 0.
      var uSubgraph = srcNodesG2[0];
      var vSubgraph = dstNodesG2[0];

      // Get in-degree and out-degree for source vertex of first edge.
      var Tin_uSubgraph = segRG2[uSubgraph+1] - segRG2[uSubgraph];
      var Tout_uSubgraph = segGraphG2[uSubgraph+1] - segGraphG2[uSubgraph];

      // Get in-degree and out-degree for destination vertex of first edge.
      var Tin_vSubgraph = segRG2[vSubgraph+1] - segRG2[vSubgraph];
      var Tout_vSubgraph = segGraphG2[vSubgraph+1] - segGraphG2[vSubgraph];

      forall e in 0..<g1.n_edges {
        var u = srcNodesG1[e];
        var v = dstNodesG1[e];

        var Tin_u = segRG1[u+1] - segRG1[u];
        var Tout_u = segGraphG1[u+1] - segGraphG1[u];

        if checkVertices {
          if semanticAndCheck {
            if !(doAttributesMatch(u, uSubgraph, graphNodeAttributes, subgraphNodeAttributes, "and", st) && (Tin_u >= Tin_uSubgraph) && (Tout_u >= Tout_uSubgraph))
              then continue;
          } else if semanticOrCheck {
            if !(doAttributesMatch(u, uSubgraph, graphNodeAttributes, subgraphNodeAttributes, "or", st) && (Tin_u >= Tin_uSubgraph) && (Tout_u >= Tout_uSubgraph))
              then continue;
          } else { /* Do nothing. */ }
        }

        var Tin_v = segRG1[v+1] - segRG1[v];
        var Tout_v = segGraphG1[v+1] - segGraphG1[v];

        if semanticAndCheck {
          if doAttributesMatch(e, 0, graphEdgeAttributes, subgraphEdgeAttributes, "and", st) && (Tin_u >= Tin_uSubgraph) && (Tout_u >= Tout_uSubgraph) && (Tin_v >= Tin_vSubgraph) && (Tout_v >= Tout_vSubgraph)
            then edgeFlagger[e] = true;
        } else if semanticOrCheck {
          if doAttributesMatch(e, 0, graphEdgeAttributes, subgraphEdgeAttributes, "or", st) && (Tin_u >= Tin_uSubgraph) && (Tout_u >= Tout_uSubgraph) && (Tin_v >= Tin_vSubgraph) && (Tout_v >= Tout_vSubgraph)
            then edgeFlagger[e] = true;
        } else { edgeFlagger[e] = true; }
      }

      return edgeFlagger;
    }

    /* Generate in-neighbors and out-neighbors for a given subgraph state.*/
    proc addToTinTout (u: int, v: int, state: State): int throws {
      state.core[v] = u; // v from g2 to a u from g1
      state.depth += 1; // a pair of vertices were mapped therefore increment depth by 1
      if state.depth==g2.n_vertices then return 1;
      else {
        var inNeighbors = dstRG1[segRG1[u]..<segRG1[u+1]];
        var outNeighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];

        state.Tin1.remove(u);
        state.Tout1.remove(u);
        
        state.Tin1 += inNeighbors;
        state.Tout1 += outNeighbors;
        
        for i in state.D_core do if state.core[i] != -1 then state.Tin1.remove(state.core[i]);
        for i in state.D_core do if state.core[i] != -1 then state.Tout1.remove(state.core[i]);
    
        var inNeighborsg2 = dstRG2[segRG2[v]..<segRG2[v+1]];      
        var outNeighborsg2 = dstNodesG2[segGraphG2[v]..<segGraphG2[v+1]];

        state.Tin2.remove(v);
        state.Tout2.remove(v);

        for n2 in inNeighborsg2 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
        for n2 in outNeighborsg2 do if !state.isMappedn2(n2) then state.Tout2.add(n2);
        
        return 1;
      }
    } // end of addToTinTout

    /* Generate in-neighbors and out-neighbors for a given subgraph state.*/
    proc addToTinToutMVE(u0_g1: int, u1_g1: int, state: State): bool throws {
      var Tin_u0, Tout_u0, Tin_u1, Tout_u1, Tin_0, Tin_1, Tout_0, Tout_1: domain(int, parSafe=true);
      var Nei_u0, Nei_u1, Nei_0, Nei_1: domain(int, parSafe=true);
      
      Tin_u0 = dstRG1[segRG1[u0_g1]..<segRG1[u0_g1 + 1]];
      Tout_u0 = dstNodesG1[segGraphG1[u0_g1]..<segGraphG1[u0_g1 + 1]];
      
      Tin_u1 = dstRG1[segRG1[u1_g1]..<segRG1[u1_g1 + 1]];
      Tout_u1 = dstNodesG1[segGraphG1[u1_g1]..<segGraphG1[u1_g1 + 1]];
      
      Tin_0 = dstRG2[segRG2[0]..<segRG2[1]];
      Tout_0 = dstNodesG2[segGraphG2[0]..<segGraphG2[1]];
      
      Tin_1 = dstRG2[segRG2[1]..<segRG2[2]];
      Tout_1 = dstNodesG2[segGraphG2[1]..<segGraphG2[2]];

      if semanticAndCheck {
        if !doAttributesMatch(u1_g1, 1, graphNodeAttributes, subgraphNodeAttributes, "and", st) 
          then return false;
      } else if semanticOrCheck {
        if !doAttributesMatch(u1_g1, 1, graphNodeAttributes, subgraphNodeAttributes, "or", st)
          then return false;
      } else { }

      var eid1 = getEdgeId(u0_g1, u1_g1, dstNodesG1, segGraphG1);
      var eid2 = getEdgeId(0, 1, dstNodesG2, segGraphG2);

      if semanticAndCheck {
        if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "and", st) then
          return false;
      } else if semanticOrCheck {
        if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "or", st) then
          return false;
      } else { }

      var eid1_rev = getEdgeId(u1_g1, u0_g1, dstNodesG1, segGraphG1);
      var eid2_rev = getEdgeId(1, 0, dstNodesG2, segGraphG2);
      if eid2_rev != -1 && eid1_rev == -1 then return false;

      if eid1_rev != -1 && eid2_rev != -1 {
        if semanticAndCheck {
          if !doAttributesMatch(eid1_rev, eid2_rev, graphEdgeAttributes, subgraphEdgeAttributes, "and", st) then
            return false;
        } else if semanticOrCheck {
          if !doAttributesMatch(eid1_rev, eid2_rev, graphEdgeAttributes, subgraphEdgeAttributes, "or", st) then
            return false;
        } else { }
      }
      const cond2 = Tin_u1.size >= Tin_1.size && Tout_u1.size >= Tout_1.size;
      if !cond2 then return false;

      Nei_u0 += Tin_u0;
      Nei_u0 += Tout_u0;
      Nei_u1 += Tin_u1;
      Nei_u1 += Tout_u1;

      var intersecg1, intersecg2: domain(int, parSafe=true);
      intersecg1 = Nei_u0 & Nei_u1;

      Nei_0 += Tin_0;
      Nei_0 += Tout_0;
      Nei_1 += Tin_1;
      Nei_1 += Tout_1;

      intersecg2 = Nei_0 & Nei_1;

      if !(intersecg1.size >= intersecg2.size) then return false;
      
      state.Tin1 = Tin_u0 | Tin_u1;
      state.Tout1 = Tout_u0 | Tout_u1;

      state.Tin2 = Tin_0 | Tin_1;
      state.Tout2 = Tout_0 | Tout_1;

      state.depth += 2;
      state.core[0] = u0_g1;
      state.core[1] = u1_g1;

      state.Tin1.remove(u0_g1); state.Tout1.remove(u0_g1);
      state.Tin1.remove(u1_g1); state.Tout1.remove(u1_g1);

      state.Tin2.remove(0); state.Tout2.remove(0);
      state.Tin2.remove(1); state.Tout2.remove(1);

      return true;
    } // end of addToTinToutMVE

    /* Check to see if the mapping of n1 from g1 to n2 from g2 is feasible. */
    proc isFeasible(n1: int, n2: int, state: State) throws {
      var termout1, termout2, termin1, termin2, new1, new2 : int = 0;
      
      // Process the out-neighbors of g2.
      var getOutN2 = dstNodesG2[segGraphG2[n2]..<segGraphG2[n2+1]];
      for Out2 in getOutN2 {
        if state.core(Out2) != -1 {
          var Out1 = state.core(Out2);
          var eid1 = getEdgeId(n1, Out1, dstNodesG1, segGraphG1);
          var eid2 = getEdgeId(n2, Out2, dstNodesG2, segGraphG2);

          if eid1 == -1 || eid2 == -1 then return false;

          if semanticAndCheck {
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "and", st) then
              return false;
          } else if semanticOrCheck {
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "or", st) then
              return false;
          } else { }
        } else {
          if state.Tin2.contains(Out2) then termin2 += 1;
          if state.Tout2.contains(Out2) then termout2 += 1;
          if !state.Tin2.contains(Out2) && !state.Tout2.contains(Out2) then new2 += 1;
        }
      }
        
      // Process the in-neighbors of g2. 
      var getInN2 = dstRG2[segRG2[n2]..<segRG2[n2+1]];
      for In2 in getInN2 {
        if state.core[In2] != -1 {
          var In1 = state.core(In2);
          var eid1 = getEdgeId(In1, n1, dstNodesG1, segGraphG1);
          var eid2 = getEdgeId(In2, n2, dstNodesG2, segGraphG2);

          if eid1 == -1 || eid2 == -1 then return false;

          if semanticAndCheck {
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "and", st) then
              return false;
          } else if semanticOrCheck {
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "or", st) then
              return false;
          } else { }
        } else {
          if state.Tin2.contains(In2) then termin2 += 1;
          if state.Tout2.contains(In2) then termout2 += 1;
          if !state.Tin2.contains(In2) && !state.Tout2.contains(In2) then new2 += 1;
        }
      }
        
      // Process the out-neighbors of g1. 
      var getOutN1 = dstNodesG1[segGraphG1[n1]..<segGraphG1[n1+1]];
      for Out1 in getOutN1 {
        if !state.isMappedn1(Out1) {
          if state.Tin1.contains(Out1) then termin1 += 1;
          if state.Tout1.contains(Out1) then termout1 += 1;
          if !state.Tin1.contains(Out1) && !state.Tout1.contains(Out1) then new1 += 1;
        }
      }
        
      // Process the in-neighbors of g2.
      var getInN1 = dstRG1[segRG1[n1]..<segRG1[n1+1]];
      for In1 in getInN1 {
        if !state.isMappedn1(In1) {
          if state.Tin1.contains(In1) then termin1 += 1;
          if state.Tout1.contains(In1) then termout1 += 1;
          if !state.Tin1.contains(In1) && !state.Tout1.contains(In1) then new1 += 1;
        }
      }

      if !(termin2 <= termin1 && termout2 <= termout1 && 
          (termin2 + termout2 + new2) <= (termin1 + termout1 + new1)
        ) then return false;

      if semanticAndCheck {
        if !doAttributesMatch(n1, n2, graphNodeAttributes, subgraphNodeAttributes, "and", st) 
          then return false;
      } else if semanticOrCheck {
        if !doAttributesMatch(n1, n2, graphNodeAttributes, subgraphNodeAttributes, "or", st)
          then return false;
      } else { }

      return true;
    } // end of isFeasible

    /** Return the unmapped vertices for g1 and g2. */
    proc getBothUnmappedNodes(state: State): ([0..<state.n1]int, int) throws {
      var UnMapG1: [0..<state.n1] int = -1;
      var UnMapG2: int = -1;

      for i in state.D_core by -1{
        if state.core[i] == -1 then UnMapG2 = i; // Node i in G2 is mapped
        else UnMapG1[state.core[i]] = 0; // Corresponding node in G1 is mapped
      }
      
      return (UnMapG1, UnMapG2);
    } // end of getBothUnmappedNodes
     
    /** Create candidates based on current state and retuns a set of pairs.*/
    proc getCandidatePairsOpti(state: State): set((int, int)) throws {
      var candidates = new set((int, int), parSafe = true);
      if state.Tout1.size > 0 && state.Tout2.size > 0 {
        var minTout2: int;
        for elem in state.Tout2 {
          minTout2 = elem;
          break;
        }  
        for n1 in state.Tout1 do candidates.add((n1, minTout2));      
      } else {
        if state.Tin1.size > 0 && state.Tin2.size > 0 {
          var minTin2: int;
          for elem in state.Tin2 {
            minTin2 = elem;
            break;
          }
          for n1 in state.Tin1 do candidates.add((n1, minTin2));
        } else { 
          var (unmappedG1, unmappedG2) = getBothUnmappedNodes(state);
          if unmappedG2 != -1 {
            for i in 0..<state.n1 {
              if unmappedG1[i] == -1 then candidates.add((i,unmappedG2));
            } 
          }
        } 
      }   
      return candidates;
    } // end of getCandidatePairsOpti

    /* Print the progress when this function is called and X minutes have passed. */
    var lastPrintedMinute: atomic int;
    proc printProgress() throws {
      const elapsedMinutes = timer.elapsed() / 60;
      const currentMinute = elapsedMinutes:int / printProgressInterval;

      if currentMinute > lastPrintedMinute.read() {
        if lastPrintedMinute.compareAndSwap(currentMinute - 1, currentMinute) {
          var outMsg = "Motifs found so far: " + numIsoAtomic.read():string;
          siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        }
      }
    }

    /* Perform the vf2 recursive steps returning all found isomorphisms.*/
    proc vf2Helper(state: owned State, depth: int): list(int,parSafe=true) throws {
      var allmappings: list(int, parSafe=true);

      // Prints the progress every X number of minutes.
      // if printProgress then printProgress();
      // TODO: TURN BACK ON FOR PRODUCTION.
      
      // Base case: the depth is equivalent to the number of vertices in the subgraph.
      if depth == g2.n_vertices {
        allmappings.pushBack(state.core);
        // numIsoAtomic.add(1);
        // TODO: TURN BACK ON FOR PRODUCTION.
        return allmappings;
      }

      // Stop execution if flagged.
      // if stopper.read() then return;
      // TODO: TURN BACK ON FOR PRODUCTION.

      // Early termination checks for both time and size limits, if enabled.
      // if limitSize && numIsoAtomic.read() >= matchLimit {
      //   stopper.testAndSet();
      //   return;
      // }
      // if limitTime && timer.elapsed():int >= timeLimit {
      //   stopper.testAndSet();
      //   return;
      // }
      // TODO: TURN BACK ON FOR PRODUCTION.

      // Generate candidate pairs (n1, n2) for mapping
      var candidatePairs = getCandidatePairsOpti(state);

      // Iterate in parallel over candidate pairs
      forall (n1, n2) in candidatePairs with (ref state, ref allmappings) {
        // if stopper.read() then continue;
        // TODO: TURN BACK ON FOR PRODUCTION.

        if isFeasible(n1, n2, state) {
          // Work on a clone, not the original state
          var newState = state.clone();

          // Update state with the new mapping
          addToTinTout(n1, n2, newState);

          // Recursive call with updated state and increased depth
          var newMappings: list(int, parSafe=true);
          newMappings = vf2Helper(newState, depth + 1);

          // Use a loop to add elements from newMappings to allmappings
          for mapping in newMappings do allmappings.pushBack(mapping);
        }
      }
      return allmappings;
    }
    
    /* Executes VF2SIFromVertices. */
    proc VF2SIFromVertices(g1: SegGraph, g2: SegGraph, const ref vertexFlagger) throws {
      var solutions: list(int, parSafe=true);
      forall edgeIndex in 0..mG1-1 with(ref solutions) {
        // if stopper.read() then continue;
        // TODO: TURN BACK ON FOR PRODUCTION.

        if vertexFlagger[srcNodesG1[edgeIndex]] && srcNodesG1[edgeIndex] != dstNodesG1[edgeIndex] {
          var initialState = new State(g1.n_vertices, g2.n_vertices);
          var edgeChecked = addToTinToutMVE(srcNodesG1[edgeIndex], dstNodesG1[edgeIndex], initialState);
          if edgeChecked {
            var newMappings = vf2Helper(initialState, 2);
            for mapping in newMappings do solutions.pushBack(mapping);
          }
        }
      }
      var subIsoArrToReturn: [0..#solutions.size](int);
      for i in 0..#solutions.size do subIsoArrToReturn[i] = solutions(i);

      return subIsoArrToReturn;
    } // end of VF2SIFrom Vertices

    /* Executes VF2SIFromEdges. */
    proc VF2SIFromEdges(g1: SegGraph, g2: SegGraph, const ref edgeFlagger) throws {
      var solutions: list(int, parSafe=true);
      forall edgeIndex in 0..mG1-1 with(ref solutions) {
        // if stopper.read() then continue;
        // TODO: TURN BACK ON FOR PRODUCTION.

        if edgeFlagger[edgeIndex] && srcNodesG1[edgeIndex] != dstNodesG1[edgeIndex] {
          var initialState = new State(g1.n_vertices, g2.n_vertices);
          var edgeChecked = addToTinToutMVE(srcNodesG1[edgeIndex], dstNodesG1[edgeIndex], initialState);
          if edgeChecked {
            var newMappings = vf2Helper(initialState, 2);
            for mapping in newMappings do solutions.pushBack(mapping);
          }
        }
      }
      var subIsoArrToReturn: [0..#solutions.size](int);
      for i in 0..#solutions.size do subIsoArrToReturn[i] = solutions(i);

      return subIsoArrToReturn;
    } // end of VF2SIFromEdges

    /* Executes VF2PS. */
    proc VF2PS(g1: SegGraph, g2: SegGraph) throws {
      var initialState = new State(g1.n_vertices, g2.n_vertices);
      var solutions = vf2Helper(initialState, 0);
      
      var subIsoArrToReturn: [0..#solutions.size](int);
      for i in 0..#solutions.size do subIsoArrToReturn[i] = solutions(i);

      return subIsoArrToReturn;
    } // end of VF2PS

    // Global array to store final results.
    var allMappingsArrayD = makeDistDom(1);
    var allMappingsArray: [allMappingsArrayD] int;

    // Call out to one of the vf2 procedures.
    if algType == "ps" {
      var allmappings = VF2PS(g1, g2);

      allMappingsArrayD = makeDistDom(allmappings.size);
      allMappingsArray = allmappings;
    }

    if algType == "si" {
      var pickerTimer:stopwatch;
      if noEdgeAttributes && !noVertexAttributes { // Graph only has vertex attributes.
        pickerTimer.start();
        var vertexFlagger = vertexPicker();
        var outMsg = "Vertex picker took: " + pickerTimer.elapsed():string + " sec";
        pickerTimer.reset();
        siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        var allmappings = VF2SIFromVertices(g1,g2,vertexFlagger);

        allMappingsArrayD = makeDistDom(allmappings.size);
        allMappingsArray = allmappings;
      } else if !noEdgeAttributes && noVertexAttributes { // Graph only has edge attributes.
        pickerTimer.start();
        var edgeFlagger = edgePicker();
        var outMsg = "Edge picker took: " + pickerTimer.elapsed():string + " sec";
        pickerTimer.reset();
        siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        var allmappings = VF2SIFromEdges(g1,g2,edgeFlagger);

        allMappingsArrayD = makeDistDom(allmappings.size);
        allMappingsArray = allmappings;
      } else if !noVertexAttributes && !noVertexAttributes { // Graph has both attributes.
        pickerTimer.start();
        var edgeFlagger = edgePicker(true);
        var outMsg = "Combined picker took: " + pickerTimer.elapsed():string + " sec";
        pickerTimer.reset();
        siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        var allmappings = VF2SIFromEdges(g1,g2,edgeFlagger);

        allMappingsArrayD = makeDistDom(allmappings.size);
        allMappingsArray = allmappings;
      } else { // Graph has no attributes.
        var edgeFlagger: [0..<g1.n_edges] bool = true;
        var allmappings = VF2SIFromEdges(g1,g2,edgeFlagger);

        allMappingsArrayD = makeDistDom(allmappings.size);
        allMappingsArray = allmappings;
      }
    }
    timer.stop();

    var isoArr = nodeMapGraphG1[allMappingsArray]; // Map vertices back to original values.
    var tempArr: [0..0] int;

    var numSubgraphVertices = nodeMapGraphG2.size;
    var numSubgraphEdges = srcNodesG2.size;
    var numIsos = isoArr.size / numSubgraphVertices;

    var isoMapper = makeDistArray(numSubgraphVertices*numIsos, int);
    forall i in isoMapper.domain by numSubgraphVertices {
      isoMapper[i..<i+numSubgraphVertices] = nodeMapGraphG2;
    }

    if returnIsosAs == "vertices" then return (isoArr, isoMapper, tempArr, tempArr);
    else {
      var srcPerIso = makeDistArray(numSubgraphEdges*numIsos, int);
      var dstPerIso = makeDistArray(numSubgraphEdges*numIsos, int);

      forall i in srcPerIso.domain by numSubgraphEdges {
        srcPerIso[i..<i+numSubgraphEdges] = srcNodesG2;
        dstPerIso[i..<i+numSubgraphEdges] = dstNodesG2;
      }

      forall (i,j) in zip(srcPerIso.domain by numSubgraphEdges, isoArr.domain by numSubgraphVertices) {
        srcPerIso[i..<i+numSubgraphEdges] = isoArr[srcPerIso[i..<i+numSubgraphEdges] + j];
        dstPerIso[i..<i+numSubgraphEdges] = isoArr[dstPerIso[i..<i+numSubgraphEdges] + j];
      }

      if returnIsosAs == "complete" then return (isoArr, isoMapper, srcPerIso, dstPerIso);

      return (srcPerIso, dstPerIso, tempArr, tempArr);
    }
  } //end of runVF2
}