module CCMsg {
  // Chapel modules.
  use Time;
  use Reflection;
  
  // Arachne modules.
  use GraphArray;
  use ConnectedComponents;
  
  // Arkouda modules.
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerConfig;
  use ServerErrors;
  use ServerErrorStrings;
  use AryUtil;
  use Logging;
  use Message;

  // private config const logLevel = ServerConfig.logLevel;
  private config const logLevel = LogLevel.DEBUG;
  const ccmLogger = new Logger(logLevel);
  var outMsg:string;

  proc segCCMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
    //var msgArgs = parseMessageArgs(payload, argSize);
    var graphEntryName=msgArgs.getValueOf("GraphName");

    // Get our graph information. 
    var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
    var ag = gEntry.graph;

    var timer:stopwatch;
    // We only care for undirected graphs, they can be weighted or unweighted. 
    var f = makeDistArray(ag.n_vertices, int);
    if (!ag.isDirected()) {
        timer.start();
        f = connectedComponents(ag);
        timer.stop(); 
        outMsg = "Time elapsed for connected components: " + timer.elapsed():string;
        ccmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
    }

    proc returnCC(): string throws {
      var CCName = st.nextName();
      var CCEntry = createSymEntry(f);
      st.addEntry(CCName, CCEntry);

      var CCMsg =  'created ' + st.attrib(CCName);
      return CCMsg;
    }

    var repMsg = returnCC();
    return new MsgTuple(repMsg, MsgType.NORMAL);
  }

  use CommandMap;
  registerFunction("segmentedGraphCC", segCCMsg,getModuleName());
}
