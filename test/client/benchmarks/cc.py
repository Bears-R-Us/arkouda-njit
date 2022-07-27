#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak
import random
import string
import arkouda_njit as njit

TYPES = ('int64', 'float64', 'bool', 'str')

def time_ak_cc_graph(d:int, w:int, vs:int, es:int, path:str):
    print("Graph BFS")
    cfg = ak.get_config()
    print("server Hostname =",cfg["serverHostname"])
    print("Number of Locales=",cfg["numLocales"])
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])
    
    start = time.time()
    Graph = njit.graph_file_read(es,vs,w,d,path)
    end = time.time()

    start = time.time()
    cc = njit.graph_cc(Graph)
    end = time.time()

def create_parser():
    parser = argparse.ArgumentParser(description="Measure the performance of connected component discovery.")
    parser.add_argument('hostname', help='Hostname of arkouda server.')
    parser.add_argument('port', type=int, help='Port of arkouda server.')
    parser.add_argument('filePath', type=str, help='File path.')
    parser.add_argument('vertices', type=int, help='Number of vertices.')
    parser.add_argument('edges', type=int, help='Number of edges.')
    return parser

if __name__ == "__main__":
    import sys
    parser = create_parser()
    args = parser.parse_args()
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    time_ak_cc_graph(0, 2, args.vertices, args.edges, args.filePath)
