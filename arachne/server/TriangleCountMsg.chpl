module TriCntMsg {
    // Chapel modules.
    use Reflection;
    use Time;
    
    // Arachne modules.
    use GraphArray;
    use Utils;
    use TriangleCount;
    
    // Arkouda modules.
    use MultiTypeSymbolTable;
    use MultiTypeSymEntry;
    use ServerConfig;
    use ServerErrors;
    use ServerErrorStrings;
    use AryUtil;
    use Logging;
    use Message;

    // Server message logger. 
    private config const logLevel = ServerConfig.logLevel;
    private config const logChannel = ServerConfig.logChannel;
    const tricntLogger = new Logger(logLevel, logChannel);
  
    /**
    * Run triangle counting on an undirected and (un)weighted graph.
    *
    * cmd: operation to perform. 
    * msgArgs: arugments passed to backend. 
    * SymTab: symbol table used for storage. 
    *
    * returns: message back to Python.
    */
    proc segTriCntMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
        param pn = Reflection.getRoutineName();
        var graphEntryName = msgArgs.getValueOf("GraphName");

        var vertexArrayName = msgArgs.getValueOf("VerticesName");
        var vertexArrayGenSymEntry: borrowed GenSymEntry = getGenericTypedArrayEntry(vertexArrayName, st);
        var vertexArraySymEntry = toSymEntry(vertexArrayGenSymEntry, int);
        var vertexArray = vertexArraySymEntry.a;
        
        var repMsg, outMsg: string;
        var countName:string;
        var returnArray = vertexArray;
        
        var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
        var graph = gEntry.graph;

        var triangles:int;
        var timer:stopwatch;
        if (!graph.isDirected()) {
            if (vertexArray[0] == -1) { 
                timer.start();
                triangles = minimum_search_triangle_count_kernel(graph);
                timer.stop();
                outMsg = "Shared memory minimum search triangle count took " + timer.elapsed():string + " sec";
                repMsg = triangles:string;
            } 
            else {
                for (v,c) in zip(vertexArray,returnArray) {
                    c = minimum_search_triangle_count_per_vertex(graph, v);
                }
                var countName = st.nextName();
                var countEntry = new shared SymEntry(returnArray);
                st.addEntry(countName, countEntry);
                repMsg = "created " + st.attrib(countName);
            }
        } else {
            var errorMsg = notImplementedError(pn, "DiGraph");
            tricntLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
        }
        tricntLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
        tricntLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
        return new MsgTuple(repMsg, MsgType.NORMAL);
    }// end of segTriMsg
    use CommandMap;
    registerFunction("segmentedGraphTri", segTriCntMsg,getModuleName());
}
