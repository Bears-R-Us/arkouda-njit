module RCCMsg {
  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  use ServerErrorStrings;
  use ServerConfig;
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use RandArray;
  use IO;
  use RConnectedComponents;

  use SymArrayDmapCompat;
  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use ArgSortMsg;
  use Time;
  use CommAggregation;
  use Sort;
  use Map;
  use DistributedDeque;

  //use LockFreeStack;
  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use Utils;

  use Set;

  // private config const logLevel = ServerConfig.logLevel;
  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);
  var outMsg:string;
  
  config const start_min_degree = 1000000;
  var tmpmindegree=start_min_degree;

  var JumpSteps:int=6;

  private proc xlocal(x :int, low:int, high:int):bool {
    return low<=x && x<=high;
  }

  private proc xremote(x :int, low:int, high:int):bool {
    return !xlocal(x, low, high);
  }

  proc segCCMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
    //var msgArgs = parseMessageArgs(payload, argSize);
    var graphEntryName=msgArgs.getValueOf("GraphName");

    // Get our graph information. 
    var gEntry:borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st);
    var ag = gEntry.graph;

    var timer:stopwatch;
    // We only care for undirected graphs, they can be weighted or unweighted. 
    var f3 = makeDistArray(ag.n_vertices, int);
    if (!ag.isDirected()) {
        timer.start();
        f3 = cc_mm(ag);
        timer.stop(); 
        outMsg = "Time elapsed for fs dist cc: " + timer.elapsed():string;
        smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
    }

    proc return_CC(): string throws {
      var CCName = st.nextName();
      var CCEntry = new shared SymEntry(f3);
      st.addEntry(CCName, CCEntry);

      var CCMsg =  'created ' + st.attrib(CCName);
      return CCMsg;
    }

    var repMsg = return_CC();
    return new MsgTuple(repMsg, MsgType.NORMAL);
  }

  use CommandMap;
  registerFunction("RsegmentedGraphCC", segCCMsg,getModuleName());
}
