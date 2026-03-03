module ExtractClusterSubgraphsMsg {
  // Chapel modules.
  import IO.FormattedIO;
  use Reflection;
  use Map;
  
  // Arachne modules.
  use GraphArray;
  use ExtractClusterSubgraphs;
  
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
  const ecsLogger = new Logger(logLevel, logChannel);

  proc extractClusterSubgraphsMsg(cmd: string, 
                            msgArgs: borrowed MessageArgs, 
                            st: borrowed SymTab): MsgTuple throws {
    param pn = Reflection.getRoutineName();
    var repMsg, outMsg:string;

    // Extract messages sent from Python.
    var graphEntryName = msgArgs.getValueOf("GraphName");
    var filePath = msgArgs.getValueOf("FilePath");
    var outputFolder = msgArgs.getValueOf("OutputFolder");

    // Pull out our graph from the symbol table.
    var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
    var g = gEntry.graph;
    
    if !g.isDirected() {
        var numClusters = runExtractClusterSubgraphs(g, st, filePath, outputFolder);
        return new MsgTuple(numClusters:string, MsgType.NORMAL);
    } else {
        var errorMsg = notImplementedError(pn, "extractClusterSubgraphs for directed graphs");
        ecsLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
        return new MsgTuple(errorMsg, MsgType.ERROR);
    }
  } // end of ExtractClusterSubgraphsMsg

  use CommandMap;
  registerFunction("extractClusterSubgraphs", extractClusterSubgraphsMsg, getModuleName());
} // end of ExtractClusterSubgraphsMsg module