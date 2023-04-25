module Utils {
    // Chapel modules.
    use IO;
    use Map;
    use List;

    // Arachne modules.
    use GraphArray;

    // Arkouda modules. 
    use Logging;
    use MultiTypeSymEntry;
    use MultiTypeSymbolTable;

    // Allow graphs to be printed server-side? Defaulted to false. MUST BE MANUALLY CHANGED.
    // TODO: make this a param instead of a set variable?
    var debug_print = false; 

    // Server message logger. 
    private config const logLevel = LogLevel.DEBUG;
    const smLogger = new Logger(logLevel);
    private var outMsg:string;

    /**
    * Print graph data structure server-side to visualize the raw array data.
    *
    * G: graph we want to print out. 
    *
    * returns: message back to Python.
    */
    proc print_graph_serverside(G: borrowed SegGraph) throws {
        for comp in Component {
            var curr_comp = comp:string;
            if G.hasComp(curr_comp) {
                select curr_comp {
                    when "RELATIONSHIPS", "NODE_LABELS" {
                        var X = toSymEntry(G.getComp(comp:string), list(string, parSafe=true)).a;
                        writeln(comp:string, " = ", X);
                    }
                    when "NODE_PROPS", "EDGE_PROPS" {
                        var X = toSymEntry(G.getComp(comp:string), list((string,string), parSafe=true)).a;
                        writeln(comp:string, " = ", X);
                    }
                    when "EDGE_WEIGHT", "EDGE_WEIGHT_R" {
                        var X = toSymEntry(G.getComp(comp:string), real).a;
                        writeln(comp:string, " = ", X);
                    }
                    when "NODE_MAP_R" {
                        var X = toSymEntryAD(G.getComp("NODE_MAP_R")).a;
                        writeln(comp:string, " = ", X);
                    }
                    otherwise {
                        var X = toSymEntry(G.getComp(comp:string), int).a;
                        writeln(comp:string, " = ", X);
                    }
                }
            }
        }
    } // end of print_graph_serverside

    /**
    * Read the graph file and store edge information in double-index data structure. 
    *
    * returns: null.
    */
    proc readLinebyLine(src: [?D1] int, dst: [?D2] int, e_weight: [?D3] real, path: string, 
                        comments: string, weighted: bool) throws {
        coforall loc in Locales  {
            on loc {
                var f = open(path, ioMode.r);
                var r = f.reader(kind = ionative);
                var line:string;
                var a,b,c:string;
                var edge_count:int = 0;
                var srclocal = src.localSubdomain();
                var ewlocal = e_weight.localSubdomain();

                while r.readLine(line) {
                    // Ignore comments for all files and matrix dimensions for mtx files.
                    if (line[0] == comments) {
                        edge_count -= 1; 
                        continue;
                    } else {
                        if (edge_count < 0) {
                            edge_count = 0; 
                            continue;
                        }
                    }

                    // Parse our vertices and weights, if applicable. 
                    if (!weighted) {
                        (a,b) = line.splitMsgToTuple(2);
                    } else {
                        (a,b,c) = line.splitMsgToTuple(3);
                    }

                    // Detect a self loop and write it to the server.
                    if ((a == b) && (debug_print == true)) {
                        smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),
                                        "self loop " + a + "->" + b);
                    }

                    // Place the read edge into the current locale.
                    if (srclocal.contains(edge_count)) {
                        src[edge_count] = (a:int);
                        dst[edge_count] = (b:int);

                        if (weighted) {
                            e_weight[edge_count] = (c:real);
                        }
                    }

                    edge_count += 1;

                    // Do not to write on an out of bounds locale. 
                    if (edge_count > srclocal.highBound) {
                        break;
                    }
                } 
                if (edge_count <= srclocal.highBound) {
                    var myoutMsg = "The input file does not contain enough edges for locale " 
                                    + here.id:string + " current line = " + edge_count:string;
                    smLogger.error(getModuleName(),getRoutineName(),getLineNumber(),myoutMsg);
                }
                r.close();
                f.close();
            }// end on loc
        }//end coforall
    }//end readLinebyLine

    /**
    * Write graph arrays to a file. 
    *
    * returns: null.
    */
    proc writeGraphArrays(G: borrowed SegGraph, filename: string) throws {
        // Create and open an output file with the specified filename in write mode.
        var outfile = open(filename, ioMode.cw);
        var writer = outfile.writer();

        for comp in Component {
            if G.hasComp(comp:string) {
                var X = toSymEntry(G.getComp(comp:string), int).a;
                var n = X.size;
                writer.writeln(n, " ", comp:string);
                writer.writeln(X);
            }
        }
        writer.close();
        outfile.close();
    }

    /**
    * Read graph arrays from a file. 
    *
    * returns: a SegGraph.
    */
    proc readGraphArrays(G: borrowed SegGraph, filename: string) throws {
        // Open an input file with the specified filename in read mode.
        var infile = open(filename, ioMode.r);
        var reader = infile.reader(kind = ionative);

        var count = 0;
        var arr_type:string;
        var line:string;
        while reader.readLine(line) {
            count += 1; 

            if (count % 2 != 0) {
                var line_split = line.split();
                arr_type = line_split[1];
                continue;
            } else {
                var X = line.split():int;
                G.withComp(new shared SymEntry(X):GenSymEntry, arr_type);

                if (arr_type == "SRC") {
                    G.n_edges = X.size;
                }
                if (arr_type == "NEIGHBOR") {
                    G.n_vertices = X.size;
                }
                if (arr_type == "SRC_R") {
                    G.directed = false;
                }
                if (arr_type == "EDGE_WEIGHT") {
                    G.directed = true;
                }
            }
        }
        reader.close();
        infile.close();
    }
}