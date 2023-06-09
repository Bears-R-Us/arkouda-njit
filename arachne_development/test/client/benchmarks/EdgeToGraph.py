#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak
import random
import string
import arachne_development.graph as njit


def edge_to_graph_test():

    print("Graph Truss Analysis")
    cfg = ak.get_config()
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])


    src = ak.array([0 ,0,1,1,2])
    dst = ak.array([1, 2, 3, 4, 5])
    # creat two edge arrays at arkouda backend

    Graph=njit.graph_edgearray(src.name,dst.name)
    cc = njit.graph_cc(Graph)

    return


def create_parser():
    parser = argparse.ArgumentParser(description="Measure the performance of suffix array building: C= suffix_array(V)")
    parser.add_argument('hostname', help='Hostname of arkouda server')
    parser.add_argument('port', type=int, help='Port of arkouda server')
    parser.add_argument('-v', '--logvertices', type=int, default=5, help='Problem size: log number of vertices')
    parser.add_argument('-e', '--vedges', type=int, default=2,help='Number of edges per vertex')
    parser.add_argument('-p', '--possibility', type=float, default=0.01,help='Possibility ')
    parser.add_argument('-t', '--trials', type=int, default=6, help='Number of times to run the benchmark')
    parser.add_argument('-m', '--perm', type=int, default=0 , help='if permutation ')
    parser.add_argument('--numpy', default=False, action='store_true', help='Run the same operation in NumPy to compare performance.')
    parser.add_argument('--correctness-only', default=False, action='store_true', help='Only check correctness, not performance.')
    return parser


    
if __name__ == "__main__":
    import sys
    
    parser = create_parser()
    args = parser.parse_args()
    ak.verbose = False
    print("Truss batch test")
    ak.connect(args.hostname, args.port)
    edge_to_graph_test()
    ak.shutdown()
