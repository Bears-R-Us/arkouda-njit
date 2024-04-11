module DiameterMsg {
  // Chapel modules.
  use Time;
  use Reflection;
  
  // Arachne modules.
  use GraphArray;
  use Diameter;
  
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
  const dmLogger = new Logger(logLevel);
  var outMsg:string;

  proc diameterMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
    // Get our graph information.
    var graphEntryName = msgArgs.getValueOf("GraphName");
    var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
    var ag = gEntry.graph;
    var d:int;

    var timer:stopwatch;
    var f = makeDistArray(ag.n_vertices, int);
    if (!ag.isDirected()) {
      timer.start();
      d = connectedComponentDiameter(ag);
      timer.stop();
      outMsg = "Time elapsed for diameter: " + timer.elapsed():string;
      dmLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
    }

    var repMsg = d:string;
    return new MsgTuple(repMsg, MsgType.NORMAL);
  }

  use CommandMap;
  registerFunction("diameter", diameterMsg,getModuleName());
}
