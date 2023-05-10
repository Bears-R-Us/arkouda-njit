/*
    Utilities we use for the different BFS implementations.

    Main things are the defintion of a ragged array and the aggregation
    for associative domains. 
*/

pragma "error mode fatal"
module Utils {
    use AggregationPrimitives;
    use CopyAggregation;
    use ReplicatedDist;
    use BlockDist;

    //###############################################################################
    //###############################################################################
    //###############################################################################
    /*
        Ragged array 
    */
    pragma "default intent is ref"
    record RagArray {
        var DO = {0..0};
        var A : [DO] int;

        proc new_dom(new_d : domain(1)) {
            this.DO = new_d;
        }

        proc size() {
            return A.size;
        }
    }

    private const dstBuffSize = getEnvInt("CHPL_AGGREGATION_DST_BUFF_SIZE", 4096);
    private const yieldFrequency = getEnvInt("CHPL_AGGREGATION_YIELD_FREQUENCY", 1024);

    var block_locale_D : domain(1) dmapped Block(boundingBox = LocaleSpace) = LocaleSpace;
    var curr_frontiers : [block_locale_D] domain(int);
    var next_frontiers : [block_locale_D] domain(int);
    
    record DynamicAssociativeDomainDstAggregator {
        const bufferSize = dstBuffSize; 
        const myLocaleSpace = LocaleSpace; 
        var opsUntilYield = yieldFrequency; 
        var lBuffers: [myLocaleSpace][0..#bufferSize] int;
        var rBuffers: [myLocaleSpace] remoteBuffer(int);
        var bufferIdxs: [myLocaleSpace] int;

        proc postinit() 
        {
            for loc in myLocaleSpace {
                rBuffers[loc] = new remoteBuffer(int, bufferSize, loc);
            }
        }

        proc deinit() 
        {
            flush();
        }

        proc flush()
        {
            for loc in myLocaleSpace {
                _flushBuffer(loc, bufferIdxs[loc], freeData=true);
            }
        }

        inline proc copy(const loc, const in srcVal: int)
        {
            // Get our current index into the buffer for dst's locale
            ref bufferIdx = bufferIdxs[loc];

            // Buffer the desired value
            lBuffers[loc][bufferIdx] = srcVal;
            bufferIdx += 1;

            // Flush our buffer if it's full. If it's been a while since we've let
            // other tasks run, yield so that we're not blocking remote tasks from
            // flushing their buffers.
            if bufferIdx == bufferSize {
                _flushBuffer(loc, bufferIdx, freeData=false);
                opsUntilYield = yieldFrequency;
            } 
            else if opsUntilYield == 0 {
                chpl_task_yield();
                opsUntilYield = yieldFrequency;
            } 
            else {
                opsUntilYield -= 1;
            }
        }

        // Flushes the buffer. This means doing a big append to the
        // associative domain on that locale.
        proc _flushBuffer(loc: int, ref bufferIdx, freeData) 
        {
            const myBufferIdx = bufferIdx;
            if myBufferIdx == 0 then return;

            // Allocate a remote buffer
            ref rBuffer = rBuffers[loc];
            const remBufferPtr = rBuffer.cachedAlloc();

            // Copy local buffer to remote buffer
            rBuffer.PUT(lBuffers[loc], myBufferIdx);

            // Process remote buffer
            on Locales[loc] {
                ref q = next_frontiers[loc];
                
                for srcVal in rBuffer.localIter(remBufferPtr, myBufferIdx) {
                    q += srcVal;
                }

                if freeData {
                    rBuffer.localFree(remBufferPtr);
                }
            }
            if freeData {
                rBuffer.markFreed();
            }
            bufferIdx = 0;
        }
    }
}