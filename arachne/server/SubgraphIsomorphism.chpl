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
  use SymArrayDmap;

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
      if !graphAttributes.contains(k) then continue; // check if attributes are same
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
          if subgraphArrEntry.dtype != graphArrEntry.dtype then return false;

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
    else return outerMatch;
  } // end of doAttributesMatch

  /** Executes the VF2 subgraph isomorphism finding procedure. Instances of the subgraph `g2` are
  searched for amongst the subgraphs of `g1` and the isomorphic ones are returned through an
  array that maps the isomorphic vertices of `g1` to those of `g2`.*/
  proc runVF2(g1: SegGraph, g2: SegGraph, semanticCheckType: string, sizeLimit: string, 
              algType: string, returnIsosAs:string, st: borrowed SymTab) throws {
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
    
    // Global array to keep track of all isomorphic mappings.
    var allmappings: list(int, parSafe=true);

    /* Pick the vertices from the host graph that can be mapped to vertex 0 in the data graph. */
    proc vertexPicker() throws {
      var vertexFlagger: [0..<g1.n_vertices] bool = false;
      var Tin_0 = dstRG2[segRG2[0]..<segRG2[1]];
      var Tout_0 = dstNodesG2[segGraphG2[0]..<segGraphG2[1]];

      forall v in 0..<g1.n_vertices {
        var inNeighborsg1 = dstRG1[segRG1[v]..<segRG1[v+1]];            
        var outNeighborsg1 = dstNodesG1[segGraphG1[v]..<segGraphG1[v+1]];

        if semanticAndCheck {
          if doAttributesMatch(v, 0, graphNodeAttributes, subgraphNodeAttributes, "and", st) && (inNeighborsg1.size >= Tin_0.size) && (outNeighborsg1.size >= Tout_0.size)
            then vertexFlagger[v] = true;
        } else if semanticOrCheck {
          if doAttributesMatch(v, 0, graphNodeAttributes, subgraphNodeAttributes, "or", st) && (inNeighborsg1.size >= Tin_0.size) && (outNeighborsg1.size >= Tout_0.size)
            then vertexFlagger[v] = true;
        } else { vertexFlagger[v] = true; }
      }

      return vertexFlagger;
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
      var Tin_u0, Tout_u0, Tin_u1, Tout_u1, Tin_0, Tin_1, Tout_0, Tout_1: domain(int);
      var Nei_u0, Nei_u1, Nei_0, Nei_1: domain(int);
      
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

      var intersecg1, intersecg2: domain(int);
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
    } // end of getCandidatePairsOpti

    /* Perform the vf2 recursive steps returning all found isomorphisms.*/
    proc vf2Helper(state: owned State, depth: int) throws {
      // Base case: the depth is equivalent to the number of vertices in the subgraph.
      if depth == g2.n_vertices {
        allmappings.pushBack(state.core);
        if limitSize then numIsoAtomic.add(1);
        return;
      }

      if limitSize then if numIsoAtomic.read() >= matchLimit then return;

      // Generate candidate pairs (n1, n2) for mapping
      var candidatePairs = getCandidatePairsOpti(state);

      // Iterate in parallel over candidate pairs
      forall (n1, n2) in candidatePairs with (ref state) {
        if isFeasible(n1, n2, state) {
          // Work on a clone, not the original state.
          var newState = state.clone();

          // Update state with the new mapping
          addToTinTout(n1, n2, newState);

          // Recursive call with updated state and increased depth
          vf2Helper(newState, depth + 1);
        }
      }
      return;
    }
    
    /* Executes VF2SI. */
    proc VF2SI(g1: SegGraph, g2: SegGraph, const ref vertexFlagger) throws {
      forall edgeIndex in 0..mG1-1 {
        if vertexFlagger[srcNodesG1[edgeIndex]] && srcNodesG1[edgeIndex] != dstNodesG1[edgeIndex] {
          var initialState = new State(g1.n_vertices, g2.n_vertices);
          var edgechecked = addToTinToutMVE(srcNodesG1[edgeIndex], dstNodesG1[edgeIndex], initialState);
          if edgechecked then vf2Helper(initialState, 2);
        }
      }
    } // end of VF2SI

    /* Executes VF2PS. */
    proc VF2PS(g1: SegGraph, g2: SegGraph) throws {
      var initialState = new State(g1.n_vertices, g2.n_vertices);
      vf2Helper(initialState, 0);
    } // end of VF2PS

    // Call out to one of the vf2 procedures.
    if algType == "ps" then VF2PS(g1, g2);
    else if algType == "si" {
      var vertexFlagger = vertexPicker();
      VF2SI(g1,g2,vertexFlagger);
    }
    else VF2PS(g1, g2);

    var allMappingsArray = makeDistArray(allmappings.toArray());
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