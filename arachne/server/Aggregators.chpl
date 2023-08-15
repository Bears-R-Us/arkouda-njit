module Aggregators {
    // Chapel modules.
    use ReplicatedDist;
    use Set;

    // Package modules.
    use CopyAggregation;

    // Arkouda modules.
    use CommAggregation;
    use ServerConfig;

    /** 
    * Declare our frontier queues here to be sets, done globally since refs cannot be a part of 
    * records yet. TODO: move these straight into SetDstAggregator when refs are allowed inside of 
    * records. */
    var D_frontier_sets = {0..1} dmapped Replicated();
    var frontier_sets : [D_frontier_sets] set(int, parSafe=true);
    var frontier_sets_idx : int;

    // Sizes of buffer and yield frequencies taken from the Arkouda server config information.
    private const dstBuffSize = getEnvInt("CHPL_AGGREGATION_DST_BUFF_SIZE", 4096);
    private const yieldFrequency = getEnvInt("CHPL_AGGREGATION_YIELD_FREQUENCY", 1024);

    /**
    * Record for remote set aggregator to perform set additions from one locale to the next. Built
    * using the aggregator from CopyAggregation but modfied a bit to make the aggregated memory
    * address a set instead of an array memory location. */
    record SetDstAggregator {
        type elemType;
        type aggType = elemType;
        const bufferSize = dstBuffSize;
        const myLocaleSpace = LocaleSpace;
        var opsUntilYield = yieldFrequency;
        var lBuffers: [myLocaleSpace] [0..#bufferSize] aggType;
        var rBuffers: [myLocaleSpace] remoteBuffer(aggType);
        var bufferIdxs: [myLocaleSpace] int;

        /**
        * Allocate the remote buffers on each locale allocated. */
        proc postinit() {
            for loc in myLocaleSpace {
                rBuffers[loc] = new remoteBuffer(aggType, bufferSize, loc);
            }
        }
    
        /**
        * Flush all of the buffers during deinitialization. */
        proc deinit() {
            flush();
        }

        /** 
        * For every locale allocated, flush their buffers. */
        proc flush() {
            for loc in myLocaleSpace {
                _flushBuffer(loc, bufferIdxs[loc], freeData=true);
            }
        }

        /**
        * Make a copy of the data being passed to a remote buffer in the local buffer that 
        * corresponds to the remote locale. 
        *
        * loc: id of remote locale.
        * srcVal: value to be copied to the remote locale. */
        inline proc copy(const loc, const in srcVal: elemType) {
            // Get our current index into the buffer for the destination locale.
            ref bufferIdx = bufferIdxs[loc];

            // Buffer the desired value. 
            lBuffers[loc][bufferIdx] = srcVal;
            bufferIdx += 1;

            /** 
            * Flush our buffer if it's full. If it's been a while since we've let
            * other tasks run, yield so that we're not blocking remote tasks from
            * flushing their buffers. */
            if bufferIdx == bufferSize {
                _flushBuffer(loc, bufferIdx, freeData=false);
                opsUntilYield = yieldFrequency;
            } else if opsUntilYield == 0 {
                chpl_task_yield();
                opsUntilYield = yieldFrequency;
            } else {
                opsUntilYield -= 1;
            }
        }

        /** 
        * Helper function to peform actual buffer steps for each locale.
        * 
        * loc: id of locale to flush. 
        * bufferIdx: id of buffer to PUT items into. 
        * freeData: did the last flush happen and have all remote buffers been freed? */
        proc _flushBuffer(loc: int, ref bufferIdx, freeData) {
            // Get the buffer id to extract the buffered values.
            const myBufferIdx = bufferIdx;
            if myBufferIdx == 0 then return;

            // Get refernece to allocated remote buffer at loc and allocate it if it wasn't already.
            ref rBuffer = rBuffers[loc];
            const remBufferPtr = rBuffer.cachedAlloc();

            // PUT local buffer to remote buffer. 
            rBuffer.PUT(lBuffers[loc], myBufferIdx);

            // Process remote buffer where it now exists.
            on Locales[loc] {
                ref f = frontier_sets[(frontier_sets_idx + 1) % 2];
                /** 
                * forall gives error: A standalone or leader iterator is not found for the iterable 
                * expression in this forall loop */
                for srcVal in rBuffer.localIter(remBufferPtr, myBufferIdx) { 
                    f.add(srcVal);
                }
                // Only free remaining data at deinit.
                if freeData {
                    rBuffer.localFree(remBufferPtr);
                }
            }
            if freeData {
                rBuffer.markFreed();
            }
            bufferIdx = 0;
        }
    } // end of SetDstAggregator
} // end of Aggregators