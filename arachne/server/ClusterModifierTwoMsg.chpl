module ClusterModifierTwoMsg {
  // Chapel modules.
  use Reflection;
  use Map;
  use Time;
  
  // Arachne modules.
  use GraphArray;
  use ClusterModifierTwo; 
  
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
  const wccLogger = new Logger(logLevel, logChannel);

  proc ClusterModifierTwoMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
		param pn = Reflection.getRoutineName();
		var repMsg, outMsg:string;

		// Extract messages sent from Python.
		var GraphEntryName = msgArgs.getValueOf("GraphName");
		var filePath = msgArgs.getValueOf("FilePath");
		var outputPath = msgArgs.getValueOf("OutputPath");
		var outputType = msgArgs.getValueOf("OutputType");
		var connectednessCriterion = msgArgs.getValueOf("ConnectednessCriterion");
		var connectednessCriterionMultValue = msgArgs.getValueOf("ConnectednessCriterionMultValue"):real;
		var preFilterMinSize = msgArgs.getValueOf("PreFilterMinSize"):int;
		var postFilterMinSize = msgArgs.getValueOf("PostFilterMinSize"):int;

		
		// Pull out our graph from the symbol table.
		var gEntry: borrowed GraphSymEntry = getGraphSymEntry(GraphEntryName, st); 
		var g = gEntry.graph;

		// Generate neighbors as sets for graph.
		wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),"Generating neighbors set.");
		g.generateNeighborsAsSet(st);
		
		var timer:stopwatch;
		if !g.isDirected() {
			timer.start();
			var numClusters = runCM2(g, st, filePath, outputPath, outputType, 
													     connectednessCriterion, connectednessCriterionMultValue, 
													     preFilterMinSize, postFilterMinSize);
			timer.stop();
			outMsg = "Cluster Modifier Two took " + timer.elapsed():string + " sec";
			wccLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);

			return new MsgTuple(numClusters:string, MsgType.NORMAL);
		} else {
			var errorMsg = notImplementedError(pn, "Cluster_Modifier_Two for directed graphs");
			wccLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
			return new MsgTuple(errorMsg, MsgType.ERROR);
		}
  } // end of ClusterModifierTwoMsg

  use CommandMap;
  registerFunction("clusterModifierTwo", ClusterModifierTwoMsg, getModuleName());
} // end of module