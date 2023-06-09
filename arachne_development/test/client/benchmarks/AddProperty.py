#!/usr/bin/env python3                                                         

import argparse
import time 
import sys
import arkouda as ak
import arachne_development.graph as njit

def process_graph(filename:str, skiplines:int, remap_flag:int, degree_sort_flag:int, rcm_flag:int,\
                    write_flag:int, build_aligned_array_flag:int, trials:int):
    cfg = ak.get_config()
    print("GRAPH PREPROCESSING -- SINGLE MODE")
    print("server Hostname =", cfg["serverHostname"])
    print("Number of Locales=", cfg["numLocales"])
    print("number of PUs =", cfg["numPUs"])
    print("Max Tasks =", cfg["maxTaskPar"])
    print("Memory =", cfg["physicalMemory"])



    src = ak.array([0 ,0,1,1,2])
    dst = ak.array([1, 2, 3, 4, 5])
    vp1 = ak.array([1,1,1,1,1,1])
    ep1 = ak.array([2,2,2,2,2])


    Graph=njit.graph_edearray(src,dst,0,\
                              remap_flag, degree_sort_flag, rcm_flag,\
                              0, 0)
    njit.graph_add_property(Graph, "VP1",vp1)
    njit.graph_add_property(Graph, "EP1",ep1)
    print("Average performance for {} trials for graph {}: {}".format(trials, only_filename, avg))

def correctness():
    #TODO: simple correctness test!
    return
    
def create_parser():
    parser = argparse.ArgumentParser(
        description="Measure the performance of preprocessing a graph."
    )
    parser.add_argument("hostname", help="Hostname of arkouda server")
    parser.add_argument("port", type=int, help="Port of arkouda server") 
    parser.add_argument(
        "-t", 
        "--trials", 
        type=int, 
        default=1, 
        help="Number of times to run the benchmark."
    )
    parser.add_argument(
        "--correctness-only", 
        default=False, 
        action="store_true", 
        help="Only check correctness, not performance."
    )
    parser.add_argument(
        "-f",
        "--filename",
        type=str,
        help="""Absolute path to file of the graph we wish to preprocess. An extra
                metadata file must be found in same directory named 'info_pre.txt'. This file must
                contain number of lines equal to the number of files in the directory. It must 
                contain the name of the files, the number of edges in a file, the number of 
                vertices, the number of columns, and 1 if directed, 0 otherwise. The format of each 
                line must be as follows:
    
                name_of_file.ext       [num_edges]         [num_vertices]      [num_cols]      [0/1]
            """
    )
    parser.add_argument(
        "-d",
        "--dirname",
        type=str,
        help="""Absolute path to directory with multiple files to preprocess (batch method). An extra
                metadata file must be found in same directory named 'info_pre.txt'. This file must
                contain number of lines equal to the number of files in the directory. It must 
                contain the name of the files, the number of edges in a file, the number of 
                vertices, the number of columns, and 1 if directed, 0 otherwise. The format of each 
                line must be as follows:
    
                name_of_file.ext       [num_edges]         [num_vertices]      [num_cols]      [0/1]
            """
    )
    parser.add_argument(
        "--skiplines",
        type=int,
        default=0,
        help="How many lines to skip during file preprocessing.."
    )
    parser.add_argument(
        "--no-remap-flag",
        default=True,
        action="store_false",
        help="Do not remap the vertex IDs that are larger than the total number of vertices."
    )
    parser.add_argument(
        "--degree-sort-flag",
        default=False,
        action="store_true",
        help="The smallest vertex ID is the vertex whose degree is the smallest."
    )
    parser.add_argument(
        "--rcm-flag",
        default=False,
        action="store_true",
        help="The RCM algorithm is used to remap the vertex IDs."
    )
    parser.add_argument(
        "--no-write-flag",
        default=True,
        action="store_false",
        help="Do not output the final edge list as a new input file."
    )
    parser.add_argument(
        "--aligned-ary-flag",
        default=False,
        action="store_true",
        help="DO NOT USE NOW! WORK IN PROGRESS!"
    )
    
    return parser

if __name__ == "__main__":    
    parser = create_parser()
    args = parser.parse_args()
    
    print("PREPROCESSING GRAPH BENCHMARK")
    ak.verbose = False
    ak.connect(args.hostname, args.port) 

    print(args)
    
    if args.filename is not None:
        process_graph(args.filename, args.skiplines, int(args.no_remap_flag),\
                        int(args.degree_sort_flag), int(args.rcm_flag), int(args.no_write_flag),\
                        int(args.aligned_ary_flag), args.trials)
    elif args.dirname is not None:
        process_graphs(args.dirname, args.skiplines, int(args.no_remap_flag),\
                        int(args.degree_sort_flag), int(args.rcm_flag), int(args.no_write_flag),\
                        int(args.aligned_ary_flag), args.trials)
    else:
        print("Error with arguments.")
        sys.exit(0)

    ak.shutdown()
