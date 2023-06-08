#!/usr/bin/env python3                                                         

import argparse
import time 
import sys
import numpy as np
import arkouda as ak
import arachne_development.graph as njit

def tri_graph(filename:str, skiplines:int, remap_flag:int, degree_sort_flag:int, rcm_flag:int,\
                    write_flag:int, build_aligned_array_flag:int, trials:int):
    cfg = ak.get_config()
    print("GRAPH TRI -- SINGLE MODE")
    print("server Hostname =", cfg["serverHostname"])
    print("Number of Locales=", cfg["numLocales"])
    print("number of PUs =", cfg["numPUs"])
    print("Max Tasks =", cfg["maxTaskPar"])
    print("Memory =", cfg["physicalMemory"])

    # Split up filename parameter to only path and only name of file.
    filepath_and_filename = filename.rsplit("/", 1)
    only_filepath = filepath_and_filename[0] + "/"
    only_filename = filepath_and_filename[1]

    info_file = open(only_filepath + "info_post.txt", "r")

    # Make a dictionary of the metadata for each of the files used. 
    file_dict = {}
    for line in info_file:
        text = line.split()
        file_dict[text[0]] = (int(text[1]), int(text[2]), int(text[3]), int(text[4]))

    # Extract the metadata from the dictionary. 
    num_edges = file_dict[only_filename][0]
    num_vertices = file_dict[only_filename][1]
    num_cols = file_dict[only_filename][2]
    directed = file_dict[only_filename][3]

    # Read in the graph. 
    G = njit.graph_file_read(num_edges, num_vertices, num_cols, directed, filename, remap_flag,\
                                degree_sort_flag, rcm_flag, write_flag, build_aligned_array_flag)
    
    # Perform the tri cnt steps.
    start = time.time()
    for i in range(trials):
        tris = njit.graph_triangle(G)
    end = time.time()
    avg = (end-start) / trials
    print("Average performance for {} trials for graph {}: {}".format(trials, only_filename, avg))
    print("Num tris =", tris)

def tri_graphs(dirname:str, skiplines:int, remap_flag:int, degree_sort_flag:int, rcm_flag:int,\
                    write_flag:int, build_aligned_array_flag:int, trials:int):
    cfg = ak.get_config()
    print("GRAPH TRI -- BATCH MODE")
    print("server Hostname =", cfg["serverHostname"])
    print("Number of Locales=", cfg["numLocales"])
    print("number of PUs =", cfg["numPUs"])
    print("Max Tasks =", cfg["maxTaskPar"])
    print("Memory =", cfg["physicalMemory"])

    # Split up filename parameter to only path and only name of file.
    only_filepath = dirname + "/"

    info_file = open(only_filepath + "info_post.txt", "r")

    # Make a dictionary of the metadata for each of the files used. 
    file_dict = {}
    for line in info_file:
        text = line.split()
        file_dict[text[0]] = (int(text[1]), int(text[2]), int(text[3]), int(text[4]))

    for only_filename in file_dict:
        num_edges = file_dict[only_filename][0]
        num_vertices = file_dict[only_filename][1]
        num_cols = file_dict[only_filename][2]
        directed = file_dict[only_filename][3]

        filename = only_filepath + only_filename

        # Read in the graph. 
        G = njit.graph_file_read(num_edges, num_vertices, num_cols, directed, filename, remap_flag,\
                                    degree_sort_flag, rcm_flag, write_flag, build_aligned_array_flag)

        # Perform the tri cnt steps.
        start = time.time()
        for i in range(trials):
            tris = njit.graph_triangle(G)
        end = time.time()
        avg = (end-start) / trials
        print("Average performance for {} trials for graph {}: {}".format(trials, only_filename, avg))
        print("Num tris =", tris)  

def correctness():
    #TODO: simple correctness test!
    return
    
def create_parser():
    parser = argparse.ArgumentParser(
        description="Measure the performance of connected components on a graph. Must be preprocessed!"
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
                metadata file must be found in same directory named 'info_post.txt'. This file must
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
                metadata file must be found in same directory named 'info_post.txt'. This file must
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
    
    print("TRI GRAPH BENCHMARK")
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    print(args)
    
    if args.filename is not None:
        tri_graph(args.filename, args.skiplines, int(args.no_remap_flag),\
                        int(args.degree_sort_flag), int(args.rcm_flag), int(args.no_write_flag),\
                        int(args.aligned_ary_flag), args.trials)
    elif args.dirname is not None:
        tri_graphs(args.dirname, args.skiplines, int(args.no_remap_flag),\
                        int(args.degree_sort_flag), int(args.rcm_flag), int(args.no_write_flag),\
                        int(args.aligned_ary_flag), args.trials)
    else:
        print("Error with arguments.")
        sys.exit(0)

    ak.shutdown()
