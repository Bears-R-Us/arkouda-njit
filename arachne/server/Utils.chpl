module Utils {
    // Chapel modules.
    use List;
    use Sort;
    use ReplicatedDist;

    // Arachne modules.
    use GraphArray;

    // Arkouda modules.
    use MultiTypeSymEntry;
    use MultiTypeSymbolTable;

    /* A fast variant of localSubdomain() assumes 'blockArray' is a block-distributed array
       if it breaks, replace it with:
            inline proc fastLocalSubdomain(arr) do return arr.localSubdomain();*/
    proc fastLocalSubdomain(const ref blockArray) const ref {
        assert(blockArray.targetLocales()[here.id] == here);
        return blockArray._value.dom.locDoms[here.id].myBlock;
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
    proc getEdgeId(u:int, v:int, ref dst:[?D1] int, ref seg:[?D2] int): int throws {
        var start = seg[u];
        var end = seg[u+1]-1;
        var eid = bin_search_v(dst, start, end, v);

        return eid;
    }

    /* Convenience procedure to return the type of the ranges array. */
    proc getRangesType() type {
        var tempD = {0..numLocales-1} dmapped replicatedDist();
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
        var D = {min reduce targetLocIds .. max reduce targetLocIds} dmapped replicatedDist();
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
    proc bin_search_v(ref ary: [?D] int, l: int, h: int, key: int): int throws {
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
}