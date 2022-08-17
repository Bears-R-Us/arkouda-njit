#!/usr/bin/env python3                                                         

import argparse
import time 
import arkouda as ak
import arkouda_njit as njit
import sys

def process_graph(num_edges:int, num_vertices:int, num_cols:int, directed:int, filename:str,\
                    skipline:int, remap_flag:int, degree_sort_flag:int, rec_flag:int,\
                    write_flag:int, build_aligned_array_flag:int):
    cfg = ak.get_config()
    print("Graph Preprocessing -- Single Mode")
    print("server Hostname =",cfg["serverHostname"])
    print("Number of Locales=",cfg["numLocales"])
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])

def process_graphs(num_edges:int, num_vertices:int, num_cols:int, directed:int, dirname:str,\
                    skipline:int, remap_flag:int, degree_sort_flag:int, rec_flag:int,\
                    write_flag:int, build_aligned_array_flag:int):
    cfg = ak.get_config()
    print("Graph Preprocessing -- Batch Mode")
    print("server Hostname =",cfg["serverHostname"])
    print("Number of Locales=",cfg["numLocales"])
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])
    
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
        default=10, 
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
        help="Single filename of a graph to preprocess."
    )
    parser.add_argument(
        "--num_edges",
        type=int,
        help="Number of edges of a graph. Only to be used out of batch mode!"
    )
    parser.add_argument(
        "--num_vertices",
        type=int,
        help="Number of vertices of a graph. Only to be used out of batch mode!"
    )
    parser.add_argument(
        "--num_cols",
        type=int,
        help="Number of columns of a graph mtx file. Only to be used out of batch mode!"
    )
    parser.add_argument(
        "--is_directed",
        default=False,
        action="store_true",
        help="Whether or not a graph is directed. Only to be used out of batch mode!"
    )
    parser.add_argument(
        "-d",
        "--dirname",
        type=str,
        help="""Directory name containing multiple files to preprocess (batch method). An extra
                metadata file must be found in same directory named 'info.txt'. This file must
                contain number of lines equal to the number of files in the directory. It must 
                contain the name of the files, the number of edges in a file, the number of 
                vertices, the number of columns, and 1 if directed, 0 otherwise. The format of each 
                line must be as follows:
    
                name_of_file.mtx       [num_edges]         [num_vertices]      [num_cols]      [0/1]
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
        "--degreesort-flag",
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
    
    print("Preprocessing graph benchmark.")
    ak.verbose = False
    ak.connect(args.hostname, args.port)
    
    if args.filename is not None:
        process_graph()
    elif args.dirname is not None:
        process_graphs()
    else:
        print("Error with arguments.")
        sys.exit(0)
