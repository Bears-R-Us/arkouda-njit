module WellConnectednessMsg {
  // Chapel modules.
  import IO.FormattedIO;
  use Reflection;
  use Map;
  use Time;
  
  // Arachne modules.
  use GraphArray;
  use WellConnectedness;
  
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
  const wcLogger = new Logger(logLevel, logChannel);

  proc wellConnectednessMsg(cmd: string, 
                            msgArgs: borrowed MessageArgs, 
                            st: borrowed SymTab): MsgTuple throws {
		param pn = Reflection.getRoutineName();
		var repMsg, outMsg:string;

		// Extract messages sent from Python.
		var graphEntryName = msgArgs.getValueOf("GraphName");
		var filePath = msgArgs.getValueOf("FilePath");
		var outputPath = msgArgs.getValueOf("OutputPath");
		var connectednessCriterion = msgArgs.getValueOf("ConnectednessCriterion");
		var connectednessCriterionMultValue = msgArgs.getValueOf("ConnectednessCriterionMultValue"):real;
		var preFilterMinSize = msgArgs.getValueOf("PreFilterMinSize"):int;
		var postFilterMinSize = msgArgs.getValueOf("PostFilterMinSize"):int;
    var analysisType = msgArgs.getValueOf("AnalysisType");

		// Pull out our graph from the symbol table.
		var gEntry: borrowed GraphSymEntry = getGraphSymEntry(graphEntryName, st); 
		var g = gEntry.graph;
		
		var timer:stopwatch;
		if !g.isDirected() {
			var numClusters:int;
			timer.start();
      numClusters = runWellConnectedness(g, st, filePath, outputPath,
                                         connectednessCriterion, 
                                         connectednessCriterionMultValue, 
                                         preFilterMinSize, postFilterMinSize,
                                         analysisType);
			timer.stop();
			outMsg = "%s took %r sec".format(analysisType, timer.elapsed());
			wcLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
			return new MsgTuple(numClusters:string, MsgType.NORMAL);
		} else {
			var errorMsg = notImplementedError(pn, "well-connectedness for directed graphs");
			wcLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
			return new MsgTuple(errorMsg, MsgType.ERROR);
		}
  } // end of wellConnectednessMsg

  use CommandMap;
  registerFunction("wellConnectedness", wellConnectednessMsg, getModuleName());
} // end of WellConnectedComponentsMsg module