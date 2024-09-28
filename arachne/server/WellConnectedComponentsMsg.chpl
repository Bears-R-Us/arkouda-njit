module WellConnectedComponentsMsg {
  // Chapel modules.
  use Reflection;
  use Map;
  use Time;
  
  // Arachne modules.
  use GraphArray;
  use WellConnectedComponents; 
  
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
  const siLogger = new Logger(logLevel, logChannel);

  proc wellConnectedComponentsMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
      param pn = Reflection.getRoutineName();
      var repMsg, outMsg:string;

      // Extract messages sent from Python.
      var GraphEntryName = msgArgs.getValueOf("GraphName");
      var FilePath = msgArgs.getValueOf("FilePath");
      var OutputPath = msgArgs.getValueOf("OutputPath");
      
      // Pull out our graph from the symbol table.
      var gEntry: borrowed GraphSymEntry = getGraphSymEntry(GraphEntryName, st); 
      var g = gEntry.graph;
      var path = FilePath;
      var outputPath = OutputPath;
      
      var timer:stopwatch;
      if !g.isDirected() {
          timer.start();
          var isoArray = runWCC(g, st, path, outputPath);
          timer.stop();
          outMsg = "Well connected components took " + timer.elapsed():string + " sec";
          
          var isoDistArray = makeDistArray(isoArray.size, int);
          isoDistArray = isoArray;
          var IsoDistArrayName = st.nextName();
          var IsoDistArrayEntry = new shared SymEntry(isoDistArray);
          st.addEntry(IsoDistArrayName, IsoDistArrayEntry);
          repMsg = 'created ' + st.attrib(IsoDistArrayName);

          siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),outMsg);
          siLogger.info(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
          return new MsgTuple(repMsg, MsgType.NORMAL);
      } else {
          var errorMsg = notImplementedError(pn, "well-connected components for directed graphs");
          siLogger.error(getModuleName(), getRoutineName(), getLineNumber(), errorMsg);
          return new MsgTuple(errorMsg, MsgType.ERROR);
      }
  } // end of wellConnectedComponentsMsg

  use CommandMap;
  registerFunction("wellConnectedComponents", wellConnectedComponentsMsg, getModuleName());
} // end of module