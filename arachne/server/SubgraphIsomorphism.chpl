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
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use MultiTypeRegEntry;
  use ServerConfig;
  use AryUtil;
  use SegStringSort;
  use SegmentedString;

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

  /** Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
  searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
  array that maps the isomorphic vertices of `g1` to those of `g2`.*/
  proc runVF2PS (g1: SegGraph, g2: SegGraph, semanticCheckType: string, sizeLimit: string, st: borrowed SymTab):[] int throws {
    var numIso: int = 0;
    var numIsoAtomic: chpl__processorAtomicType(int) = 0;
    var semanticAndCheck = if semanticCheckType == "and" then true else false;
    var semanticOrCheck = if semanticCheckType == "or" then true else false;
    var matchLimit = if sizeLimit != "none" then sizeLimit:int else 0;
    var limitSize:bool = if matchLimit > 0 then true else false;

    // Extract the g1/G/g information from the SegGraph data structure.
    const ref srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    const ref dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    const ref segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
    const ref dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
    const ref segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;

    // Extract the g2/H/h information from the SegGraph data structure.
    const ref srcNodesG2 = toSymEntry(g2.getComp("SRC_SDI"), int).a;
    const ref dstNodesG2 = toSymEntry(g2.getComp("DST_SDI"), int).a;
    const ref segGraphG2 = toSymEntry(g2.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG2 = toSymEntry(g2.getComp("SRC_R_SDI"), int).a;
    const ref dstRG2 = toSymEntry(g2.getComp("DST_R_SDI"), int).a;
    const ref segRG2 = toSymEntry(g2.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG2 = toSymEntry(g2.getComp("VERTEX_MAP_SDI"), int).a;

    // Get the number of vertices and edges for each graph.
    var nG1 = nodeMapGraphG1.size;
    var mG1 = srcNodesG1.size;
    var nG2 = nodeMapGraphG2.size;
    var mG2 = srcNodesG2.size;

    // Returns the map of attribute name to tuple of symbol table identifier and array data type
    // to be used to extract a given attribute array.
    var graphNodeAttributes = g1.getNodeAttributes();
    var subgraphNodeAttributes = g2.getNodeAttributes();
    var graphEdgeAttributes = g1.getEdgeAttributes();
    var subgraphEdgeAttributes = g2.getEdgeAttributes();

    /* Given a vertex or edge index returns true if a vertex or edge from the main host graph
    matches a given vertex or edge from a subgraph. 
    
    NOTE: checking categoricals is very time consuming as internal indices need to be mapped to 
    strings and then compared. Users should be encouraged to maintain their own integer 
    categorical consistencies and use integer attribute matching instead.*/
    proc doAttributesMatch(graphIdx, subgraphIdx, const ref graphAttributes, const ref subgraphAttributes, matchType:string) throws {
      var outerMatch:bool;
      if matchType == "and" then outerMatch = true;
      if matchType == "or" then outerMatch = false;
      for (k,v) in zip(subgraphAttributes.keys(), subgraphAttributes.values()) {
        if !graphAttributes.contains(k) then return false; // check if attributes are same
        if v[1] != graphAttributes[k][1] then return false; // check if types are same
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
          }
          when "Strings" {
            var subgraphStringEntry = toSegStringSymEntry(getGenericTypedArrayEntry(v[0], st));
            var graphStringEntry = toSegStringSymEntry(getGenericTypedArrayEntry(graphAttributes[k][0], st));
            
            const ref subgraphStringOffsets = subgraphStringEntry.offsetsEntry.a;
            const ref subgraphStringBytes = subgraphStringEntry.bytesEntry.a;

            const ref graphStringOffsets = graphStringEntry.offsetsEntry.a;
            const ref graphStringBytes = graphStringEntry.bytesEntry.a;

            const ref string1 = subgraphStringBytes[subgraphStringOffsets[subgraphIdx]..<subgraphStringOffsets[subgraphIdx+1]];
            const ref string2 = graphStringBytes[graphStringOffsets[graphIdx]..<graphStringOffsets[graphIdx+1]];

            innerMatch = || reduce (string1 == string2);
          }
          when "pdarray" {
            var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(v[0], st);
            var graphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(graphAttributes[k][0], st);
            if subgraphArrEntry.dtype != graphArrEntry.dtype then return false;

            var etype = subgraphArrEntry.dtype;
            select etype {
              when (DType.Int64) {
                const ref subgraphArr = toSymEntry(subgraphArrEntry, int).a;
                const ref graphArr = toSymEntry(graphArrEntry, int).a;
                innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              }
              when (DType.UInt64) {
                const ref subgraphArr = toSymEntry(subgraphArrEntry, uint).a;
                const ref graphArr = toSymEntry(graphArrEntry, uint).a;
                innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              }
              when (DType.Float64) {
                const ref subgraphArr = toSymEntry(subgraphArrEntry, real).a;
                const ref graphArr = toSymEntry(graphArrEntry, real).a;
                innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              }
              when (DType.Bool) {
                const ref subgraphArr = toSymEntry(subgraphArrEntry, bool).a;
                const ref graphArr = toSymEntry(graphArrEntry, bool).a;
                innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              }
            }
          }
        }
        if matchType == "or" then outerMatch = outerMatch || innerMatch;
        if matchType == "and" then outerMatch = outerMatch && innerMatch;

        if matchType == "or" && outerMatch then return true;
      }
      return outerMatch;
    }
    
    var IsoArrtemp = vf2(g1, g2);
    var IsoArr = nodeMapGraphG1[IsoArrtemp]; // Map vertices back to original values.
         
    /** Generate in-neighbors and out-neighbors for a given subgraph state.*/
    proc addToTinTout (u: int, v: int, state: State) {
      state.core[v] = u; // v from g2 to a u from g1
      state.depth += 1; // a pair of vertices were mapped therefore increment depth by 1

      if state.depth == g2.n_vertices then return;
      else {
        const ref inNeighbors = dstRG1[segRG1[u]..<segRG1[u+1]];
        const ref outNeighbors = dstNodesG1[segGraphG1[u]..<segGraphG1[u+1]];

        state.Tin1.remove(u);
        state.Tout1.remove(u);
    
        for n1 in inNeighbors do if !state.isMappedn1(n1) then state.Tin1.add(n1);
        for n1 in outNeighbors do if !state.isMappedn1(n1) then state.Tout1.add(n1);
    
        const ref inNeighborsg2 = dstRG2[segRG2[v]..<segRG2[v+1]];
        const ref outNeighborsg2 = dstNodesG2[segGraphG2[v]..<segGraphG2[v+1]];

        state.Tin2.remove(v);
        state.Tout2.remove(v);

        for n2 in inNeighborsg2 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
        for n2 in outNeighborsg2 do if !state.isMappedn2(n2) then state.Tout2.add(n2);
        return;
      }
    } // end of addToTinTout

    /** Check to see if the mapping of n1 from g1 to n2 from g2 is feasible.*/
    proc isFeasible(n1: int, n2: int, state: State) throws {
      var termout1, termout2, termin1, termin2, new1, new2 : int = 0;
      var outNeighborsCheck, inNeighborsCheck, edgeCheck:bool;
      
      // Process the out-neighbors of g2.
      const ref getOutN2 = dstNodesG2[segGraphG2[n2]..<segGraphG2[n2+1]];
      for Out2 in getOutN2 {
        if state.core(Out2) != -1 {
          var Out1 = state.core(Out2);
          var eid1 = getEdgeId(n1, Out1, dstNodesG1, segGraphG1);
          var eid2 = getEdgeId(n2, Out2, dstNodesG2, segGraphG2);

          if eid1 == -1 || eid2 == -1 then return false;

          if semanticAndCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "and") then
              return false;
          else if semanticOrCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "or") then
              return false;
        } 
        else {
          if state.Tin2.contains(Out2) then termin2 += 1;
          if state.Tout2.contains(Out2) then termout2 += 1;
          if !state.Tin2.contains(Out2) && !state.Tout2.contains(Out2) then new2 += 1;
        }
      }
        
      // Process the in-neighbors of g2. 
      const ref getInN2 = dstRG2[segRG2[n2]..<segRG2[n2+1]];
      for In2 in getInN2 {
        if state.core[In2] != -1 {
          var In1 = state.core(In2);
          var eid1 = getEdgeId(In1, n1, dstNodesG1, segGraphG1);
          var eid2 = getEdgeId(In2, n2, dstNodesG2, segGraphG2);

          if eid1 == -1 || eid2 == -1 then return false;
          
          if semanticAndCheck then 
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "and") then
              return false;
          else if semanticOrCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "or") then 
              return false;
        }
        else {
          if state.Tin2.contains(In2) then termin2 += 1;
          if state.Tout2.contains(In2) then termout2 += 1;
          if !state.Tin2.contains(In2) && !state.Tout2.contains(In2) then new2 += 1;
        }
      }
        
      // Process the out-neighbors of g1. 
      const ref getOutN1 = dstNodesG1[segGraphG1[n1]..<segGraphG1[n1+1]];
      for Out1 in getOutN1 {
        if !state.isMappedn1(Out1) {
          if state.Tin1.contains(Out1) then termin1 += 1;
          if state.Tout1.contains(Out1) then termout1 += 1;
          if !state.Tin1.contains(Out1) && !state.Tout1.contains(Out1) then new1 += 1;
        }
      }
        
      // Process the in-neighbors of g2.
      const ref getInN1 = dstRG1[segRG1[n1]..<segRG1[n1+1]];
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

      if semanticAndCheck then 
        if !doAttributesMatch(n1, n2, graphNodeAttributes, subgraphNodeAttributes, "and") 
          then return false;
      else if semanticOrCheck then
        if !doAttributesMatch(n1, n2, graphNodeAttributes, subgraphNodeAttributes, "or")
          then return false;
      
      return true;
    } // end of isFeasible

    /** Return the unmapped vertices for g1 and g2. */
    proc getBothUnmappedNodes(state: State): ([0..<state.n1] int, int) throws {
      var UnMapG1: [0..<state.n1] int = -1;
      var UnMapG2: int = -1;

      for i in state.D_core by -1 {
        if state.core[i] == -1 then UnMapG2 = i; // Node i in G2 is mapped
        else UnMapG1[state.core[i]] = 0; // Corresponding node in G1 is mapped
      }
      
      return (UnMapG1, UnMapG2);
    } // end of getBothUnmappedNodes
     
    /** Create candidates based on current state and retuns a set of pairs.*/
    proc getCandidatePairsOpti(state: State): set((int, int)) throws {
      var candidates = new set((int, int), parSafe = true);
      if state.depth == 0 {
        var (unmappedG1, unmappedG2) = getBothUnmappedNodes(state);

        if unmappedG2 != -1 then
          for i in 0..<state.n1 do
            if unmappedG1[i] == -1 then candidates.add((i,unmappedG2));
  
        return candidates;
      } else {
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
            for elem in state.Tin2{
              minTin2 = elem;
              break;
            }
            for n1 in state.Tin1 do candidates.add((n1, minTin2));

          } else { 
            var (unmappedG1, unmappedG2) = getBothUnmappedNodes(state);

            if unmappedG2 != -1 then
              for i in 0..<state.n1 do
                if unmappedG1[i] == -1 then candidates.add((i,unmappedG2));
          }
        }
        return candidates;
      }
    } // end of getCandidatePairsOpti

    /** Perform the vf2 recursive steps returning all found isomorphisms.*/
    proc vf2Helper(state: State, depth: int): list(int) throws {
      var allmappings: list(int, parSafe=true);

      // Base case: the depth is equivalent to the number of vertices in the subgraph.
      if depth == g2.n_vertices {
        for elem in state.core do allmappings.pushBack(elem);
        if limitSize then numIsoAtomic.add(1);
        return allmappings;
      }

      // Generate candidate pairs (n1, n2) for mapping
      var candidatePairs = getCandidatePairsOpti(state);

      if limitSize then
        if numIsoAtomic.compareAndSwap(matchLimit, matchLimit) then return allmappings;

      // Iterate in parallel over candidate pairs
      forall (n1, n2) in candidatePairs with (ref state, ref allmappings) {
        if isFeasible(n1, n2, state) {
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

    /* Main procedure that invokes the recursive vf2 steps using the inputted graphs. */
    proc vf2(g1: SegGraph, g2: SegGraph): [] int throws {
      var initial = new State(g1.n_vertices, g2.n_vertices);
      var solutions = vf2Helper(initial, 0);
      var subIsoArrToReturn: [0..#solutions.size](int);
      for i in 0..#solutions.size do subIsoArrToReturn[i] = solutions(i);
      return subIsoArrToReturn;
    } // end of vf2
    
    return IsoArr;
  } //end of runVF2PS

  /** Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
  searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
  array that maps the isomorphic vertices of `g1` to those of `g2`.*/
  proc runVF2SI (g1: SegGraph, g2: SegGraph, semanticCheckType: string, sizeLimit: string, st: borrowed SymTab):[] int throws {
    var numIso: int = 0;
    var numIsoAtomic: chpl__processorAtomicType(int) = 0;
    var semanticAndCheck = if semanticCheckType == "and" then true else false;
    var semanticOrCheck = if semanticCheckType == "or" then true else false;
    var matchLimit = if sizeLimit != "none" then sizeLimit:int else 0;
    var limitSize:bool = if matchLimit > 0 then true else false;

    // Extract the g1/G/g information from the SegGraph data structure.
    const ref srcNodesG1 = toSymEntry(g1.getComp("SRC_SDI"), int).a;
    const ref dstNodesG1 = toSymEntry(g1.getComp("DST_SDI"), int).a;
    const ref segGraphG1 = toSymEntry(g1.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG1 = toSymEntry(g1.getComp("SRC_R_SDI"), int).a;
    const ref dstRG1 = toSymEntry(g1.getComp("DST_R_SDI"), int).a;
    const ref segRG1 = toSymEntry(g1.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG1 = toSymEntry(g1.getComp("VERTEX_MAP_SDI"), int).a;

    // Extract the g2/H/h information from the SegGraph data structure.
    const ref srcNodesG2 = toSymEntry(g2.getComp("SRC_SDI"), int).a;
    const ref dstNodesG2 = toSymEntry(g2.getComp("DST_SDI"), int).a;
    const ref segGraphG2 = toSymEntry(g2.getComp("SEGMENTS_SDI"), int).a;
    const ref srcRG2 = toSymEntry(g2.getComp("SRC_R_SDI"), int).a;
    const ref dstRG2 = toSymEntry(g2.getComp("DST_R_SDI"), int).a;
    const ref segRG2 = toSymEntry(g2.getComp("SEGMENTS_R_SDI"), int).a;
    const ref nodeMapGraphG2 = toSymEntry(g2.getComp("VERTEX_MAP_SDI"), int).a;

    // Get the number of vertices and edges for each graph.
    var nG1 = nodeMapGraphG1.size;
    var mG1 = srcNodesG1.size;
    var nG2 = nodeMapGraphG2.size;
    var mG2 = srcNodesG2.size;

    // Returns the map of attribute name to tuple of symbol table identifier and array data type
    // to be used to extract a given attribute array.
    var graphNodeAttributes = g1.getNodeAttributes();
    var subgraphNodeAttributes = g2.getNodeAttributes();
    var graphEdgeAttributes = g1.getEdgeAttributes();
    var subgraphEdgeAttributes = g2.getEdgeAttributes();

    /* Given a vertex or edge index returns true if a vertex or edge from the main host graph
    matches a given vertex or edge from a subgraph. 
    
    NOTE: checking categoricals is very time consuming as internal indices need to be mapped to 
    strings and then compared. Users should be encouraged to maintain their own integer 
    categorical consistencies and use integer attribute matching instead.*/
    proc doAttributesMatch(graphIdx, subgraphIdx, const ref graphAttributes, const ref subgraphAttributes, matchType:string) throws {
      var outerMatch:bool;
      if matchType == "and" then outerMatch = true;
      if matchType == "or" then outerMatch = false;
      for (k,v) in zip(subgraphAttributes.keys(), subgraphAttributes.values()) {
        if !graphAttributes.contains(k) then return false; // check if attributes are same
        if v[1] != graphAttributes[k][1] then return false; // check if types are same
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
          }
          when "Strings" {
            var subgraphStringEntry = toSegStringSymEntry(getGenericTypedArrayEntry(v[0], st));
            var graphStringEntry = toSegStringSymEntry(getGenericTypedArrayEntry(graphAttributes[k][0], st));
            
            const ref subgraphStringOffsets = subgraphStringEntry.offsetsEntry.a;
            const ref subgraphStringBytes = subgraphStringEntry.bytesEntry.a;

            const ref graphStringOffsets = graphStringEntry.offsetsEntry.a;
            const ref graphStringBytes = graphStringEntry.bytesEntry.a;

            const ref string1 = subgraphStringBytes[subgraphStringOffsets[subgraphIdx]..<subgraphStringOffsets[subgraphIdx+1]];
            const ref string2 = graphStringBytes[graphStringOffsets[graphIdx]..<graphStringOffsets[graphIdx+1]];

            innerMatch = || reduce (string1 == string2);
          }
          when "pdarray" {
            var subgraphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(v[0], st);
            var graphArrEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(graphAttributes[k][0], st);
            if subgraphArrEntry.dtype != graphArrEntry.dtype then return false;

            var etype = subgraphArrEntry.dtype;
            select etype {
              when (DType.Int64) {
                const ref subgraphArr = toSymEntry(subgraphArrEntry, int).a;
                const ref graphArr = toSymEntry(graphArrEntry, int).a;
                innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              }
              when (DType.UInt64) {
                const ref subgraphArr = toSymEntry(subgraphArrEntry, uint).a;
                const ref graphArr = toSymEntry(graphArrEntry, uint).a;
                innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              }
              when (DType.Float64) {
                const ref subgraphArr = toSymEntry(subgraphArrEntry, real).a;
                const ref graphArr = toSymEntry(graphArrEntry, real).a;
                innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              }
              when (DType.Bool) {
                const ref subgraphArr = toSymEntry(subgraphArrEntry, bool).a;
                const ref graphArr = toSymEntry(graphArrEntry, bool).a;
                innerMatch = subgraphArr[subgraphIdx] == graphArr[graphIdx];
              }
            }
          }
        }
        if matchType == "or" then outerMatch = outerMatch || innerMatch;
        if matchType == "and" then outerMatch = outerMatch && innerMatch;

        if matchType == "or" && outerMatch then return true;
      }
      return outerMatch;
    }
    var NodeInDegree: [0..<g1.n_vertices] int = 0;
    var NodeOutDegree: [0..<g1.n_vertices] int = 0;
    var NodeFlag: [0..<g1.n_vertices] bool = false;
    GraphbyDegree();
    SortSubGraphbyDegree();

    proc GraphbyDegree() throws{
        //var NodeDegree: [0..<g1.n_vertices] int = 0; // Tuple to hold (sum of degrees, out-degree)
        
        var Tin_0 = dstRG2[segRG2[0]..<segRG2[1]];
        var Tout_0 = dstNodesG2[segGraphG2[0]..<segGraphG2[1]];

        forall v in 0..<g1.n_vertices {
            var inNeighborsg1 = dstRG1[segRG1[v]..<segRG1[v+1]];            
            var outNeighborsg1 = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

            NodeInDegree[v] = inNeighborsg1.size;
            NodeOutDegree[v] = outNeighborsg1.size;
            //NodeDegree[v] = NodeInDegree[v] + NodeOutDegree[v];

            writeln("$$$$$ 1 = ", doAttributesMatch(v, 0, graphNodeAttributes, subgraphNodeAttributes, "and"), "\n",
                    "$$$$$ 2 = ", inNeighborsg1.size >= Tin_0.size, "\n",
                    "$$$$$ 3 = ", outNeighborsg1.size >= Tout_0.size, "\n");

            if semanticAndCheck then 
              if doAttributesMatch(v, 0, graphNodeAttributes, subgraphNodeAttributes, "and") && (inNeighborsg1.size >= Tin_0.size) && (outNeighborsg1.size >= Tout_0.size)
                then NodeFlag[v] = true;
            else if semanticOrCheck then
              if doAttributesMatch(v, 0, graphNodeAttributes, subgraphNodeAttributes, "or")  && (inNeighborsg1.size >= Tin_0.size) && (outNeighborsg1.size >= Tout_0.size)
                then NodeFlag[v] = true;

            // if nodesLabelCompatible(v, 0) && (inNeighborsg1.size >= Tin_0.size) && (outNeighborsg1.size >= Tout_0.size){
            //     NodeFlag[v] = true;
            // }

        }
        writeln("NodeFlag = ", NodeFlag);
        return ;
    }
    proc SortSubGraphbyDegree():[] int throws {
        var NodeInDegree: [0..<g2.n_vertices] int = 0;
        var NodeOutDegree: [0..<g2.n_vertices] int = 0;
        var NodeDegree: [0..<g2.n_vertices] (int, int) = (0, 0); // Tuple to hold (sum of degrees, out-degree)

        for v in 0..<g2.n_vertices {
            var inNeighborsg2 = dstRG2[segRG2[v]..<segRG2[v+1]];            
            var outNeighborsg2 = dstNodesG2[segGraphG2[v]..<segGraphG2[v+1]];

            NodeInDegree[v] = inNeighborsg2.size;
            NodeOutDegree[v] = outNeighborsg2.size;
            NodeDegree[v] = (NodeInDegree[v] + NodeOutDegree[v], NodeOutDegree[v]);
        }

        // Create an array of tuples (value, original index)
        var zipped: [NodeDegree.domain] (int, int, int);
        writeln("NodeDegree.domain = ", NodeDegree.domain);
        writeln("g2.n_vertices = ", g2.n_vertices);
        // Populate the zipped array
        for i in NodeDegree.domain {
            zipped[i] = (NodeDegree[i][0], NodeDegree[i][1], i);
        }
        writeln("zipped.size = ", zipped.size);

        // Define a custom comparator for sorting tuples
        record Comparator {
            proc compare(a: (int, int, int), b: (int, int, int)) {
                // Compare by sum of degrees first
                if a(0) != b(0) {
                    return b(0) - a(0);
                } else {
                    // If tied, compare by out-degree
                    return b(1) - a(1);
                }
            }
        }

        var TupleComparator: Comparator;

        // Sort the zipped array using the custom comparator
        sort(zipped, comparator=TupleComparator);

        // Extract the sorted array and the indices
        var sortedArray: [NodeDegree.domain] int;
        var sortedIndices: [NodeDegree.domain] int;
        for i in NodeDegree.domain{
            sortedIndices[i] = zipped[i](2);
        }

        // Print the results
        writeln("Original indices of sorted elements: ", sortedIndices);
        return (sortedIndices);
    }   

    var IsoArrtemp = vf2(g1, g2);
    var IsoArr = nodeMapGraphG1[IsoArrtemp]; // Map vertices back to original values.

    /** Generate in-neighbors and out-neighbors for a given subgraph state.*/
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

        //for n1 in inNeighbors do if !state.isMappedn1(n1) then state.Tin1.add(n1);
        //for n1 in outNeighbors do if !state.isMappedn1(n1) then state.Tout1.add(n1);
    
        var inNeighborsg2 = dstRG2[segRG2[v]..<segRG2[v+1]];      
        var outNeighborsg2 = dstNodesG2[segGraphG2[v]..<segGraphG2[v+1]];

        state.Tin2.remove(v);
        state.Tout2.remove(v);

        for n2 in inNeighborsg2 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
        for n2 in outNeighborsg2 do if !state.isMappedn2(n2) then state.Tout2.add(n2);
        return 1;
      }
    } // end of addToTinTout

  proc addToTinToutMVE(u0_g1: int, u1_g1: int, state: State): bool throws {
      var Tin_u0, Tout_u0, Tin_u1, Tout_u1, Tin_0, Tin_1, Tout_0, Tout_1: domain(int);
      var Nei_u0, Nei_u1, Nei_0, Nei_1: domain(int);
      //writeln("/////////addToTinToutMVE//// u0_g1 = ", u0_g1, " //////// u1_g1 = ", u1_g1);
      //Check for self-loops
      //if u0_g1 == u1_g1 then return (-1, false);
      
      Tin_u0 = dstRG1[segRG1[u0_g1]..<segRG1[u0_g1 + 1]];
      Tout_u0 = dstNodesG1[segGraphG1[u0_g1]..<segGraphG1[u0_g1 + 1]];
      
      Tin_u1 = dstRG1[segRG1[u1_g1]..<segRG1[u1_g1 + 1]];
      Tout_u1 = dstNodesG1[segGraphG1[u1_g1]..<segGraphG1[u1_g1 + 1]];
      
      Tin_0 = dstRG2[segRG2[0]..<segRG2[1]];
      Tout_0 = dstNodesG2[segGraphG2[0]..<segGraphG2[1]];
      
      Tin_1 = dstRG2[segRG2[1]..<segRG2[2]];
      Tout_1 = dstNodesG2[segGraphG2[1]..<segGraphG2[2]];
      
  
      //writeln("we are Here 3");

      //writeln("nodesLabelCompatible(u1_g1, 1) = ", nodesLabelCompatible(u1_g1, 1));

      // if !nodesLabelCompatible(u1_g1, 1) {
      //   //writeln("nodesLabelCompatible(u0_g1, 0) = ", nodesLabelCompatible(u0_g1, 0));
      //   return false;
      // }

            if semanticAndCheck then 
              if !doAttributesMatch(u1_g1, 1, graphNodeAttributes, subgraphNodeAttributes, "and") 
                then return false;
            else if semanticOrCheck then
              if !doAttributesMatch(u1_g1, 1, graphNodeAttributes, subgraphNodeAttributes, "or")
                then return false;
/*      if !checkEdge(u0_g1, u1_g1) {
        //writeln("checkEdge(u0_g1, u1_g1) = ", checkEdge(u0_g1, u1_g1));
        return (-1, false);
      }
      */
//////////////////////////////////
//checkEdge-out
      //writeln("we are Here 5");


      var eid1 = getEdgeId(u0_g1, u1_g1, dstNodesG1, segGraphG1);
            //writeln("we are Here 4");

      var eid2 = getEdgeId(0, 1, dstNodesG2, segGraphG2);

      //var relationshipsG1eid1 = convertedRelationshipsG1[eid1];
            //writeln("we are Here 5");

      //var relationshipsG2eid2 = convertedRelationshipsG2[eid2];
            //writeln("we are Here 6");

      //writeln("relationshipsG1eid1 = ", relationshipsG1eid1);
      //writeln("relationshipsG2eid2 = ", relationshipsG2eid2);
      // if relationshipsG1eid1 != relationshipsG2eid2 then return false;
      //writeln("we are Here 7");
          if semanticAndCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "and") then
              return false;
          else if semanticOrCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "or") then
              return false;

//checkEdge-out
      var eid1_rev = getEdgeId(u1_g1, u0_g1, dstNodesG1, segGraphG1);
      var eid2_rev = getEdgeId(1, 0, dstNodesG2, segGraphG2);
      //writeln("edge from ",u1_g1, " to ", u0_g1 );
      //writeln("eid1 = ", eid1);
      //writeln("eid2 = ", eid2);
      if eid2_rev != -1 && eid1_rev == -1 then return false;
      //writeln("we are Here 8");

      if eid1_rev != -1 && eid2_rev != -1 {
          if semanticAndCheck then
            if !doAttributesMatch(eid1_rev, eid2_rev, graphEdgeAttributes, subgraphEdgeAttributes, "and") then
              return false;
          else if semanticOrCheck then
            if !doAttributesMatch(eid1_rev, eid2_rev, graphEdgeAttributes, subgraphEdgeAttributes, "or") then
              return false;

      }
      //writeln("relationshipsG1eid1 = ", relationshipsG1eid1);
      //writeln("relationshipsG2eid2 = ", relationshipsG2eid2);

          // TODO: Add better relationship matching function.

/////////////////////////////////
      // Refactored condition
      const cond2 = Tin_u1.size >= Tin_1.size && Tout_u1.size >= Tout_1.size;

    
      
      if !cond2 {
        //writeln("Tin_u0 >= Tin_0 = ", Tin_u0.size >= Tin_0.size);
        //writeln("Tout_u0 >= Tout_0 = ", Tout_u0.size >= Tout_0.size);
        //writeln("Tin_u1 >= Tin_1 = ", Tin_u1.size >= Tin_1.size);
        //writeln("Tout_u1 >= Tout_1 = ", Tout_u1.size >= Tout_1.size);
        return false;
      }

      Nei_u0 += Tin_u0;
      Nei_u0 += Tout_u0;
      //writeln("Nei_u0 = ", Nei_u0);
      Nei_u1 += Tin_u1;
      Nei_u1 += Tout_u1;
      //writeln("Nei_u1 = ", Nei_u1);

      var intersecg1, intersecg2: domain(int);
      intersecg1 = Nei_u0 & Nei_u1;
      //writeln("intersecg1 = ", intersecg1);

      Nei_0 += Tin_0;
      Nei_0 += Tout_0;
      //writeln("Nei_0 = ", Nei_0);
      Nei_1 += Tin_1;
      Nei_1 += Tout_1;
      //writeln("Nei_1 = ", Nei_1);

      intersecg2 = Nei_0 & Nei_1;
      //writeln("intersecg2 = ", intersecg2);

      if !(intersecg1.size >= intersecg2.size) {
        //writeln("intersecg1.size = ", intersecg1.size);
        //writeln("intersecg2.size = ", intersecg2.size);
        return false;
      }
      //writeln("all checks done!");
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
/*
      for i in state.D_core do if state.core[i] != -1 then state.Tin1.remove(state.core[i]);
      for i in state.D_core do if state.core[i] != -1 then state.Tout1.remove(state.core[i]);

      for n2 in Tin_0 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
      for n2 in Tout_0 do if !state.isMappedn2(n2) then state.Tout2.add(n2);

      for n2 in Tin_1 do if !state.isMappedn2(n2) then state.Tin2.add(n2);
      for n2 in Tout_1 do if !state.isMappedn2(n2) then state.Tout2.add(n2);
*/      
      //writeln("state is = ", state);
      return true;
    }



    /** Check to see if the mapping of n1 from g1 to n2 from g2 is feasible.*/
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

          if semanticAndCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "and") then
              return false;
          else if semanticOrCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "or") then
              return false;
        } 
        else {
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

          if semanticAndCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "and") then
              return false;
          else if semanticOrCheck then
            if !doAttributesMatch(eid1, eid2, graphEdgeAttributes, subgraphEdgeAttributes, "or") then
              return false;
        }
        else {
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

      if semanticAndCheck then 
        if !doAttributesMatch(n1, n2, graphNodeAttributes, subgraphNodeAttributes, "and") 
          then return false;
      else if semanticOrCheck then
        if !doAttributesMatch(n1, n2, graphNodeAttributes, subgraphNodeAttributes, "or")
          then return false;

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
          for elem in state.Tout2{
            minTout2 = elem;
            break;
          }  
          for n1 in state.Tout1 do candidates.add((n1, minTout2));      
        } else {
          if state.Tin1.size > 0 && state.Tin2.size > 0 {
            var minTin2: int;
            for elem in state.Tin2{
              minTin2 = elem;
              break;
            }
            for n1 in state.Tin1 do candidates.add((n1, minTin2));

          } else { 
            var (unmappedG1, unmappedG2) = getBothUnmappedNodes(state);
            //var flagunmappedG2 = false;
            //var minUnmapped2 : int;

            if unmappedG2 != -1 {
              for i in 0..<state.n1 {
                if unmappedG1[i] == -1 then candidates.add((i,unmappedG2));
              } 
            }
          } 
        }   
        return candidates;
      //}

    } // end of getCandidatePairsOpti
      
          /** Create candidates based on current state and retuns a set of pairs.*/
    proc getCandidatePairsOpti_light(state: State): set((int, int)) throws {
      var candidates = new set((int, int), parSafe = true);

          var (unmappedG1, unmappedG2) = getBothUnmappedNodes(state);
          //var flagunmappedG2 = false;
          //var minUnmapped2 : int;

          if unmappedG2 != -1 {
            for i in 0..<state.n1 {
              if unmappedG1[i] == -1 then candidates.add((i,unmappedG2));
            } 
          }
  
      return candidates;
    } // end of getCandidatePairsOpti_light
       
    /** Creates an initial, empty state.*/
    proc createInitialState(n1: int, n2: int): State throws {
      return new owned State(n1, n2);
    } // end of createInitialState

    /* Perform the vf2 recursive steps returning all found isomorphisms.*/
    proc vf2Helper(state: owned State, depth: int): list(int) throws {
      var allmappings: list(int, parSafe=true);

      // Base case: check if a complete mapping is found
      if depth == g2.n_vertices {
        for elem in state.core do allmappings.pushBack(elem);
        return allmappings;
      }
      var candidatePairs = getCandidatePairsOpti(state);

      forall (n1, n2) in candidatePairs with (ref state, ref allmappings) {
        if isFeasible(n1, n2, state) {
          var newState = state.clone();
          addToTinTout(n1, n2, newState);
          var newMappings: list(int, parSafe=true);
          newMappings = vf2Helper(newState, depth + 1);
          for mapping in newMappings do allmappings.pushBack(mapping);
        }
      }
      return allmappings;
    }
    
    /* Main procedure that invokes the recursive vf2 steps using the inputted graphs. */
    proc vf2(g1: SegGraph, g2: SegGraph): [] int throws {
      var state = createInitialState(g1.n_vertices, g2.n_vertices);
      var solutions: list(int, parSafe=true);
      var n2: int = 0;
      forall edgeIndex in 0..mG1-1 with (ref solutions) {
        if NodeFlag[srcNodesG1[edgeIndex]] && srcNodesG1[edgeIndex] != dstNodesG1[edgeIndex] {
          var InitState = createInitialState(g1.n_vertices, g2.n_vertices);
          var edgechecked = addToTinToutMVE(srcNodesG1[edgeIndex], dstNodesG1[edgeIndex], InitState);
          if edgechecked {
            var newMappings = vf2Helper(InitState, 2);
            for mapping in newMappings do solutions.pushBack(mapping);
          }
        }
      }
      var subIsoArrToReturn: [0..#solutions.size](int);
      for i in 0..#solutions.size do subIsoArrToReturn[i] = solutions(i);

      return(subIsoArrToReturn);
    } // end of vf2

    return IsoArr;
  } //end of runVF2SI
} // end of SubgraphIsomorphism module