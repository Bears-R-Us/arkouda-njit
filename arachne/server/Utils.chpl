module Utils {
  // Chapel modules.
  use List;
  use Sort;
  use ReplicatedDist;
  use Sort;
  use BlockDist;
  use BitOps;
  use List;
  use CopyAggregation;
  use OS;
  use IO;
  use IO.FormattedIO;
  use CommDiagnostics;

  // Arachne modules.
  use GraphArray;

  // Arkouda modules.
  use MultiTypeSymEntry;
  use MultiTypeSymbolTable;

  /* A fast variant of localSubdomain() assumes 'blockArray' is a block-distributed array.*/
  proc fastLocalSubdomain(const ref blockArray) const ref 
  where isSubtype(blockArray._value.type, BlockArr) {
    assert(blockArray.targetLocales()[here.id] == here);
    return blockArray._value.dom.locDoms[here.id].myBlock;
}

  /* Overloads above `fastLocalSubdomain` procedure to not throw compile-time errors for when
    the array is a regular array. */
  proc fastLocalSubdomain(drArray: []) where drArray._value.isDefaultRectangular() { 
    return drArray.localSubdomain(); 
  }

  /* Extract the integer identifier for an edge `<u,v>`. TODO: any function that queries into the 
  graph data structure should probably be a class method of SegGraph.
  
  :arg u: source vertex to index for.
  :type u: int
  :arg v: destination vertex v to binary search for
  :type v: int
  :arg graph: Graph to search within.
  :type graph: borrowed SegGraph
  
  :returns: int */
  proc getEdgeId(u:int, v:int, const ref dst:[?D1] int, const ref seg:[?D2] int): int throws {
      var start = seg[u];
      var end = seg[u+1]-1;
      var eid = bin_search_v(dst, start, end, v);

      return eid;
  }

  /* Convenience procedure to return the type of the ranges array. */
  proc getRangesType() type {
      var tempD = {0..numLocales-1} dmapped new replicatedDist();
      var temp : [tempD] (int,locale,int);
      return borrowed ReplicatedSymEntry(temp.type);
  }

  /* Convenience procedure to return the actual ranges array stored. */
  proc GenSymEntry.getRanges() const ref do return try! (this:getRangesType()).a;

  /** Create array that keeps track of low vertex in each edges array on each locale.*/
  proc generateRanges(graph, key, key2insert, const ref array) throws {
      const ref targetLocs = array.targetLocales();
      const targetLocIds = targetLocs.id;

      // Create a domain in the range of locales that the array was distributed to. In general,
      // this will be the whole locale space, and we deal with gaps in the array through the 
      // isEmpty() method for subdomains.
      var D = {min reduce targetLocIds .. max reduce targetLocIds} dmapped new replicatedDist();
      var ranges : [D] (int,locale,int);

      // Write the local subdomain low value to the ranges array.
      coforall loc in targetLocs with (ref ranges) {
          on loc {
              const ref localSubdomain = fastLocalSubdomain(array);
              var low_vertex, high_vertex: int;

              if !localSubdomain.isEmpty() {
                  low_vertex = array[localSubdomain.low];
                  high_vertex = array[localSubdomain.high];
              } else { low_vertex = -1; high_vertex = -1; }
              
              coforall rloc in targetLocs with (ref ranges) do on rloc {
                  ranges[loc.id] = (low_vertex,loc,high_vertex);
              }
          }
      }
      graph.withComp(new shared ReplicatedSymEntry(ranges):GenSymEntry, key2insert);
  }

  /* Helper procedure to parse ranges and return the locale(s) we must write to.
  
  :arg val: value whose locale range we are looking for.
  :type val: int
  :arg ranges: replicated ranges array to use for the search.
  :type ranges: const ref [ReplicatedDist] (int,locale,int) 

  :returns: list(locale) */
  proc find_locs(val:int, const ref ranges) {
      var locs = new list(locale);

      for low2lc2high in ranges {
          if (val >= low2lc2high[0])&&(val <= low2lc2high[2]) then locs.pushBack(low2lc2high[1]);
      }

      return locs;
  }

  /* Binary search for a given key, original version by Zhihui Du.

  :arg ary: integer array to search into
  :type ary: ref [?D] int
  :arg l: low index value
  :type l: int
  :arg h: high index value
  :type h: int
  :arg key: value to search for in array
  :type key: int

  :returns: int */
  proc bin_search_v(const ref ary: [?D] int, l: int, h: int, key: int): int throws {
      if ( (l < D.lowBound) || (h > D.highBound) || (l < 0)) {
          return -1;
      }
      if ( (l > h) || ((l == h) &&  (ary[l] != key))) {
          return -1;
      }
      if (ary[l] == key) {
          return l;
      }
      if (ary[h] == key) {
          return h;
      }
      
      var m = (l + h) / 2: int;
      
      if ((m == l) ) {
          return -1;
      }
      if (ary[m] == key ) {
          return m;
      } else {
          if (ary[m] < key) {
              return bin_search_v(ary, m+1, h, key);
          }
          else {
              return bin_search_v(ary, l, m-1, key);
          }
      }
  }// end bin_search_v

  /* Non-recursive, distributed-memory binary search for a given key. NOTE: experimental! Not 
  fully tested.
  
  :arg arr: integer array to search into
  :type arr: ref [?D] int
  :arg lo: low index value
  :type lo: int
  :arg hi: high index value
  :type hi: int
  :arg key: value to search for in array
  :type key: int
  :arg comparator: comparer of array values, defaults to integer comparator
  :type comparator: defaultComparator
  
  :returns: int */
  proc bin_search(arr: [?D] int, key: int, lo: int, hi: int, comparator:?rec=defaultComparator): int throws {
      var found:int = -1; // index of found key, -1 if not found.
      coforall loc in Locales with (ref found) do on loc {
          var start_loc:bool, end_loc:bool, mid_loc:bool, skip_loc:bool;
          var l:int, h:int, local_lo:int, local_hi:int;
          local_lo = arr.localSubdomain().lowBound;
          local_hi = arr.localSubdomain().highBound;

          // Check to see if loc is either a starting locale or an end locale.
          if arr.localSubdomain().contains(lo) then start_loc = true;
          else if arr.localSubdomain().contains(hi) then end_loc = true;
          else if !start_loc && !end_loc && local_lo > lo && local_hi < hi then mid_loc = true;
          else skip_loc = true;

          if !skip_loc {
              // Start the search from the actual lo index stored on start_loc.
              if start_loc {
                  l = if arr.localSubdomain().lowBound < lo then lo
                      else arr.localSubdomain().lowBound;
              } else l = arr.localSubdomain().lowBound;
              
              // End the search from the actual hi index stored on end_loc.
              if end_loc {
                  h = if arr.localSubdomain().highBound > hi then hi
                      else arr.localSubdomain().highBound;
              } else h = arr.localSubdomain().highBound;

              // Actual binary search steps. 
              while(l <= h) {
                  if arr[l] == key {found = l; break;}
                  if arr[h] == key {found = h; break;}
                  
                  const m = (l + h) / 2 : int;

                  if m == l then break;
                  if arr[m] == key {found = m; break;}
                  
                  if chpl_compare(key, arr[m], comparator=comparator) > 0 then l = m + 1;
                  else h = m - 1;
              }
          }
      } // end of coforall
      return found;
  }// end bin_search

  /* Pulled from Arkouda. Used as the comparator for arrays made of tuples. */
  record contrivedComparator {
    const dc = new DefaultComparator();
    proc keyPart(a, i: int) {
      if canResolveMethod(dc, "keyPart", a, 0) {
        return dc.keyPart(a, i);
      } else if isTuple(a) {
        return tupleKeyPart(a, i);
      } else {
        compilerError("No keyPart method for eltType ", a.type:string);
      }
    }
    proc tupleKeyPart(x: _tuple, i:int) {
      proc makePart(y): uint(64) {
        var part: uint(64);
        // get the part, ignore the section
        const p = dc.keyPart(y, 0)(1);
        // assuming result of keyPart is int or uint <= 64 bits
        part = p:uint(64); 
        // If the number is signed, invert the top bit, so that
        // the negative numbers sort below the positive numbers
        if isInt(p) {
          const one:uint(64) = 1;
          part = part ^ (one << 63);
        }
        return part;
      }
      var part: uint(64);
      if isTuple(x[0]) && (x.size == 2) {
        for param j in 0..<x[0].size {
          if i == j {
            part = makePart(x[0][j]);
          }
        }
        if i == x[0].size {
          part = makePart(x[1]);
        }
        if i > x[0].size {
          return (-1, 0:uint(64));
        } else {
          return (0, part);
        }
      } else {
        for param j in 0..<x.size {
          if i == j {
            part = makePart(x[j]);
          }
        }
        if i >= x.size {
          return (-1, 0:uint(64));
        } else {
          return (0, part);
        }
      }
    }
  }
  const myDefaultComparator = new contrivedComparator();

  // Pulled from Arkouda, used within radix sort for merging arrays
  config param RSLSD_bitsPerDigit = 16;
  private param bitsPerDigit = RSLSD_bitsPerDigit;

  // Pulled from Arkouda, these need to be const for comms/performance reasons
  private param numBuckets = 1 << bitsPerDigit;
  private param maskDigit = numBuckets-1;

  /* 
    Pulled from Arkouda, gets the maximum bit width of the array and if there 
    are any negative numbers.
  */
  inline proc getBitWidth(a: [?aD] int): (int, bool) {
    var aMin = min reduce a;
    var aMax = max reduce a;
    var wPos = if aMax >= 0 then numBits(int) - clz(aMax) else 0;
    var wNeg = if aMin < 0 then numBits(int) - clz((-aMin)-1) else 0;
    const signBit = if aMin < 0 then 1 else 0;
    const bitWidth = max(wPos, wNeg) + signBit;
    const negs = aMin < 0;

    return (bitWidth, negs);
  }

  /* 
    Pulled from Arkouda, for two arrays returns array with bit width and 
    negative information.
  */
  proc getNumDigitsNumericArrays(arr1, arr2) {
    var bitWidths: [0..<2] int;
    var negs: [0..<2] bool;
    var totalDigits: int;

    (bitWidths[0], negs[0]) = getBitWidth(arr1);
    totalDigits += (bitWidths[0] + (bitsPerDigit-1)) / bitsPerDigit;

    (bitWidths[1], negs[1]) = getBitWidth(arr2);
    totalDigits += (bitWidths[1] + (bitsPerDigit-1)) / bitsPerDigit;

    return (totalDigits, bitWidths, negs);
  }

  /* 
    Pulled from Arkouda, get the digits for the current rshift. Signbit needs 
    to be inverted for negative values 
  */
  inline proc getDigit(key: int, rshift: int, last: bool, negs: bool): int {
    const invertSignBit = last && negs;
    const xor = (invertSignBit:uint << (RSLSD_bitsPerDigit-1));
    const keyu = key:uint;

    return (((keyu >> rshift) & (maskDigit:uint)) ^ xor):int;
  }

  /* 
    Pulled from Arkouda, return an array of all values from array a whose index
    corresponds to a true value in array `truth`.
  */
  proc boolIndexer(a: [?aD] ?t, truth: [aD] bool) {
    var iv: [truth.domain] int = (+ scan truth);
    var pop = iv[iv.size-1];
    var ret = blockDist.createArray({0..<pop}, t);

    forall (i, eai) in zip(a.domain, a) with (var agg = new DstAggregator(t)) do 
      if (truth[i]) then agg.copy(ret[iv[i]-1], eai);
    
    return ret;
  }

  /*
    Given two arrays `src` and `dst`, it symmetrizes the edge list. In other
    words, it concatenates `dst` to `src` and `src` to `dst`.
  */
  proc symmetrizeEdgeList(src, dst) {
    var m = src.size;

    var symmSrc = blockDist.createArray({0..<2*m}, int);
    var symmDst = blockDist.createArray({0..<2*m}, int);

    symmSrc[0..<m] = src; symmSrc[m..<2*m] = dst; // TODO: Needs aggregator?
    symmDst[0..<m] = dst; symmDst[m..<2*m] = src; // TODO: Needs aggregator?

    return (symmSrc, symmDst);
  }

  /* 
    Pulled from Arkouda. Given an array, `sorted`, generates the unique values
    of the array and the counts of each value, if `needCounts` is set to `true`.
  */
  proc uniqueFromSorted(sorted: [?aD] ?t, param needCounts = true) {
    var truth = blockDist.createArray(aD, bool);
    truth[0] = true;
    [(t,s,i) in zip(truth,sorted,aD)] if i > aD.low { t = (sorted[i-1] != s); }
    var allUnique: int = + reduce truth;

    if allUnique == aD.size {
      var u = blockDist.createArray(aD, t);
      u = sorted;
      if needCounts {
        var c = blockDist.createArray(aD, int);
        c = 1;
        return (u, c);
      } else {
        return u;
      }
    }

    var iv: [truth.domain] int = (+ scan truth);
    var pop = iv[iv.size - 1];

    var segs = blockDist.createArray({0..<pop}, int);
    var ukeys = blockDist.createArray({0..<pop}, t);

    forall i in truth.domain with (var agg = new DstAggregator(int)){
      if truth[i] == true {
        var idx = i; 
        agg.copy(segs[iv[i]-1], idx);
      }
    }

    forall (_,uk,seg) in zip(segs.domain, ukeys, segs) 
      with (var agg = new SrcAggregator(t)) do agg.copy(uk, sorted[seg]);

    if needCounts {
      var counts = blockDist.createArray({0..<pop}, int);
      forall i in segs.domain {
        if i < segs.domain.high then counts[i] = segs[i+1] - segs[i];
        else counts[i] = sorted.domain.high+1 - segs[i];
      }
      return (ukeys, counts);
    } else {
      return ukeys;
    }
  }

  /*
    Mostly pulled from Arkouda. It creates a merged array from considering 
    `src` as the initial digits and appending `dst` to the end. It sorts the
    newly merged array and then returns new versions `src` and `dst` based off
    the sort.
  */
  proc sortEdgeList(in src, in dst) {
    var (totalDigits,bitWidths,negs) = getNumDigitsNumericArrays(src, dst);
    var m = src.size;

    /* Pulled from Arkouda to merge two arrays into one for radix sort. */
    proc mergeNumericArrays(param numDigits,size,totalDigits,bitWidths,negs) {
      var merged = blockDist.createArray(
        {0..<size}, 
        numDigits*uint(bitsPerDigit)
      );
      var curDigit = numDigits - totalDigits;

      var nBits = bitWidths[0];
      var neg = negs[0];
      const r = 0..#nBits by bitsPerDigit;
      for rshift in r {
        const myDigit = (nBits-1 - rshift) / bitsPerDigit;
        const last = myDigit == 0;
        forall (m, a) in zip(merged, src) {
          m[curDigit+myDigit]=getDigit(a,rshift,last,neg):uint(bitsPerDigit);
        }
      }
      curDigit += r.size;
      nBits = bitWidths[1];
      neg = negs[1];
      for rshift in r {
        const myDigit = (nBits-1 - rshift) / bitsPerDigit;
        const last = myDigit == 0;
        forall (m, a) in zip(merged, dst) {
          m[curDigit+myDigit]=getDigit(a,rshift,last,neg):uint(bitsPerDigit);
        }
      }
      curDigit += r.size;

      return merged;
    }

    /* Pulled from Arkouda, runs merge and then sort */
    proc mergedArgsort(param numDigits) {
      var merged = mergeNumericArrays(
        numDigits, 
        m, 
        totalDigits, 
        bitWidths, 
        negs
      );

      var AI = blockDist.createArray(merged.domain, (merged.eltType,int));
      var iv = blockDist.createArray(merged.domain, int);

      AI = [(a, i) in zip(merged, merged.domain)] (a, i);
      Sort.TwoArrayDistributedRadixSort.twoArrayDistributedRadixSort(
        AI, comparator=myDefaultComparator
      );
      iv = [(_, i) in AI] i;

      return iv;
    }

    var iv = blockDist.createArray({0..<m}, int);
    if totalDigits <=  4 { iv = mergedArgsort( 4); }
    else if totalDigits <=  8 { iv = mergedArgsort( 8); }
    else if totalDigits <= 16 { iv = mergedArgsort(16); }

    var sortedSrc = src[iv]; var sortedDst = dst[iv];

    return (sortedSrc, sortedDst);
  }

  /*
    Given two arrays, find instances of where src[i] == dst[i] and removes these
    self-loops.
  */
  proc removeSelfLoops(src, dst) {
    var loops = src != dst;
    var noLoopsSrc = boolIndexer(src, loops);
    var noLoopsDst = boolIndexer(dst, loops);

    return (noLoopsSrc, noLoopsDst);
  }

  /*
    Given two arrays, assumed to have been previously sorted by `sortEdgeList`, 
    removes duplicated edges.
  */
  proc removeMultipleEdges(src: [?sD] int, dst) {
    var edgesAsTuples = blockDist.createArray(
      sD, (int,int)
    );

    forall (e, i) in zip(edgesAsTuples, edgesAsTuples.domain) do
      e = (src[i], dst[i]);

    var uniqueEdges = uniqueFromSorted(edgesAsTuples, needCounts = false);
    var eD = uniqueEdges.domain;
    var noDupsSrc = blockDist.createArray(eD,int);
    var noDupsDst = blockDist.createArray(eD,int);

    forall (e,u,v) in zip(uniqueEdges,noDupsSrc,noDupsDst) {
      u = e[0];
      v = e[1];
    }

    return (noDupsSrc, noDupsDst);
  }

  /*
    Wrapper to return the permutation that will sort the array `arr`.
  */
  proc argsort(arr) {
    var AI = blockDist.createArray(arr.domain, (arr.eltType,int));
    var iv = blockDist.createArray(arr.domain, int);

    AI = [(a, i) in zip(arr, arr.domain)] (a, i);
    Sort.TwoArrayDistributedRadixSort.twoArrayDistributedRadixSort(
      AI, comparator=myDefaultComparator
    );
    iv = [(_, i) in AI] i;

    return iv;
  }

  /*
    Remaps the values within `src` and `dst` to the range `0..n-1` where `n` is
    the number of vertices in the graph.
  */
  proc oneUpper(src: [?sD], in dst) {
    var srcPerm = blockDist.createArray(sD, int);
    forall (s,i) in zip(srcPerm, srcPerm.domain) do s=i;
    var (srcUnique, srcCounts) = uniqueFromSorted(src);
    
    var dstPerm = argsort(dst);
    var sortedDst = dst[dstPerm];
    var (dstUnique, dstCounts) = uniqueFromSorted(sortedDst);

    var srcSegments = (+ scan srcCounts) - srcCounts;
    var dstSegments = (+ scan dstCounts) - dstCounts;

    var vals = blockDist.createArray(srcUnique.domain, int);
    forall (v,i) in zip(vals, vals.domain) do v=i;

    var newSrc = broadcast(srcPerm, srcSegments, vals);
    var newDst = broadcast(dstPerm, dstSegments, vals);

    return (newSrc, newDst, srcUnique);
  }

  /* 
    Pulled from Arkouda. 
    Broadcast a value per segment of a segmented array to the original ordering 
    of the precursor array. For example, if the original array was sorted and 
    grouped, resulting in groups defined by <segs>, and if <vals> contains group 
    labels, then return the array of group labels corresponding to the original 
    array. Intended to be used with arkouda.GroupBy.

    For our intents and purposes, arkouda.GroupBy can be mimicked by running
    `uniqueFromSorted` to get counts that can be used to build `segs`. Further, 
    the `perm` can be computed by `argort`. Lastly, `vals` is whatever values
    need to be broadcasted and is typically of the same size as the number of
    unique elements in the array.
   */
  proc broadcast(perm: [?D] int, segs: [?sD] int, vals: [sD] ?t) {
    if sD.size == 0 {
      // early out if size 0
      return blockDist.createArray({0..<D.size}, t);
    }
    // The stragegy is to go from the segment domain to the full
    // domain by forming the full derivative and integrating it
    var keepSegs = blockDist.createArray(sD, bool);
    [(k, s, i) in zip(keepSegs, segs, sD)] if i < sD.high { k = (segs[i+1] != s); }
    keepSegs[sD.high] = true;

    const numKeep = + reduce keepSegs;

    if numKeep == sD.size {
      // Compute the sparse derivative (in segment domain) of values
      var diffs = blockDist.createArray(sD, t);
      forall (i, d, v) in zip(sD, diffs, vals) {
        if i == sD.low {
          d = v;
        } else {
          d = v - vals[i-1];
        }
      }
      // Convert to the dense derivative (in full domain) of values
      var expandedVals = blockDist.createArray(D, t);
      forall (s, d) in zip(segs, diffs) with (var agg = new DstAggregator(t)) {
        agg.copy(expandedVals[s], d);
      }
      // Integrate to recover full values
      expandedVals = (+ scan expandedVals);
      // Permute to the original array order
      var permutedVals = blockDist.createArray(D, t);
      forall (i, v) in zip(perm, expandedVals) with (var agg = new DstAggregator(t)) {
        agg.copy(permutedVals[i], v);
      }
      return permutedVals;
    }
    else {
      // boolean indexing into segs and vals
      const iv = + scan keepSegs - keepSegs;
      const kD = blockDist.createDomain(0..<numKeep);
      var compressedSegs: [kD] int;
      var compressedVals: [kD] t;
      forall (i, keep, seg, val) in zip(sD, keepSegs, segs, vals) with (var segAgg = new DstAggregator(int),
                                                                        var valAgg = new DstAggregator(t)) {
        if keep {
          segAgg.copy(compressedSegs[iv[i]], seg);
          valAgg.copy(compressedVals[iv[i]], val);
        }
      }
      // Compute the sparse derivative (in segment domain) of values
      var diffs = blockDist.createArray(kD, t);
      forall (i, d, v) in zip(kD, diffs, compressedVals) {
        if i == sD.low {
          d = v;
        } else {
          d = v - compressedVals[i-1];
        }
      }
      // Convert to the dense derivative (in full domain) of values
      var expandedVals = blockDist.createArray(D, t);
      forall (s, d) in zip(compressedSegs, diffs) with (var agg = new DstAggregator(t)) {
        agg.copy(expandedVals[s], d);
      }
      // Integrate to recover full values
      expandedVals = (+ scan expandedVals);
      // Permute to the original array order
      var permutedVals = blockDist.createArray(D, t);
      forall (i, v) in zip(perm, expandedVals) with (var agg = new DstAggregator(t)) {
        agg.copy(permutedVals[i], v);
      }
      return permutedVals;
    }
  }

  proc matrixMarketFileToGraph(path) throws {
    try { var f = open(path, ioMode.r); f.close(); }
    catch e:FileNotFoundError { writeln("Encountered FileNotFoundError."); }
    catch e { writeln("Unknown error."); }

    var commentHeader = "% ";
    commentHeader = commentHeader.strip();
    var f = open(path, ioMode.r);
    var r = f.reader(locking=false);
    var line, a, b, c: string;

    // Parse the header information of matrix market files.
    while r.readLine(line) {
      if line[0] == commentHeader then continue;
      else {
        var temp = line.split();
        a = temp[0]; 
        b = temp[1];
        c = temp[2];
        break;
      }
    }
    var rows = a:int;
    var cols = b:int;
    var entries = c:int;

    var src = blockDist.createArray({0..<entries}, int);
    var dst = blockDist.createArray({0..<entries}, int);
    var wgt = blockDist.createArray({0..<entries}, real);

    // Check to see if there will be three columns, if so the graph will be
    // weighted.
    r.readLine(line);
    var temp = line.split();
    var weighted = false;
    var ind = 0; 
    if temp.size != 3 {
      src[ind] = temp[0]:int;
      dst[ind] = temp[1]:int;
    } else {
      src[ind] = temp[0]:int;
      dst[ind] = temp[1]:int;
      wgt[ind] = temp[2]:real;
      weighted = true;
    }
    ind += 1;

    // Now, process the rest of the file.
    while r.readLine(line) {
      var temp = line.split();
      if !weighted {
        src[ind] = temp[0]:int;
        dst[ind] = temp[1]:int;
      } else {
        src[ind] = temp[0]:int;
        dst[ind] = temp[1]:int;
        wgt[ind] = temp[2]:real;
      }
      ind += 1;
    }

    return (src, dst); // TODO: make internal graph constructor & return that.
  }

  proc gnp(n, m) {
    var src = blockDist.createArray({0..<m}, int);
    var dst = blockDist.createArray({0..<m}, int);

    fillRandom(src, 0, n-1);
    fillRandom(dst, 0, n-1);

    return (src, dst); // TODO: make internal graph constructor & return that.
  }

  /*
  Hacky way to output a `.csv` file from the source of 
  `printCommDiagnosticsTable` within the `CommDiagnostics` module.
  */
  proc commDiagnosticsToCsv(comms, identifier:string, kernel:string, printEmptyColumns=false) throws {
    use Reflection, Math;

    var outputFilename = identifier + "_comm_" + kernel + "_" + numLocales:string + "L.csv";
    var outputFile = open(outputFilename, ioMode.cw);
    var outputFileWriter = outputFile.writer(locking=false);

    // grab all comm diagnostics
    var CommDiags = getCommDiagnostics();

    param unstable = "unstable";

    // cache number of fields and store vector of whether field is active
    param nFields = getNumFields(chpl_commDiagnostics);

    // How wide should the column be for this field?  A negative value
    // indicates an unstable field.  0 indicates that the field should
    // be skipped in the table.
    var fieldWidth: [0..<nFields] int;

    // print column headers while determining which fields are active
    outputFileWriter.writef("%s", "locale");
    for param fieldID in 0..<nFields {
      param name = getFieldName(chpl_commDiagnostics, fieldID);
      var maxval = 0;
      for locID in LocaleSpace do
        maxval = max(maxval, getField(CommDiags[locID], fieldID).safeCast(int));

      if printEmptyColumns || maxval != 0 {
        const width = if commDiagsPrintUnstable == false && name == "amo"
                        then -unstable.size
                        else max(name.size, ceil(log10(maxval+1)):int);
        fieldWidth[fieldID] = width;

        outputFileWriter.writef(",%s", name);
      }
    }
    outputFileWriter.writeln();

    // print a row per locale showing the active fields
    for locID in LocaleSpace {
      outputFileWriter.writef("%s", locID:string);
      for param fieldID in 0..<nFields {
        var width = fieldWidth[fieldID];
        const count = if width < 0 then unstable
                                    else getField(CommDiags[locID],
                                                  fieldID):string;
        if width != 0 then
          outputFileWriter.writef(",%s", count);
      }
      outputFileWriter.writeln();
    }
  }
}