#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak
import random
import string
import arkouda_njit as njit

TYPES = ('int64', 'float64', 'bool', 'str')

def time_ak_truss_graph():
    print("Graph Truss Analysis")
    cfg = ak.get_config()
    print("server Hostname =",cfg["serverHostname"])
    print("Number of Locales=",cfg["numLocales"])
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])
    
    #Graph=njit.graph_file_read(3000,1003,2,0,"/home/z/zd4/Adata/3.gr")
    #Graph=njit.graph_file_read(237010,12008,2,0,"/home/z/zd4/Adata/SNAP/ca-HepPh.txt.gr")
    #Graph=njit.graph_file_read(3387388,4033394,2,0,"/home/z/zd4/Adata/SNAP/amazon0601.txt.gr")
    #Graph=njit.graph_file_read(28980,5242,2,0,"/home/z/zd4/Adata/SNAP/ca-GrQc.txt.gr",0,0)
    #Graph=njit.graph_file_read(3056,1024,2,0,"/home/z/zd4/Adata/Delaunay/delaunay_n10/delaunay_n10.mtx.gr",0,1)
    Graph=njit.graph_file_read(6127,2048,2,0,"/home/z/zd4/Adata/Delaunay/delaunay_n11/delaunay_n11.mtx.gr",0,0)
    #Graph=njit.graph_file_read(12264,4096,2,0,"/home/z/zd4/Adata/Delaunay/delaunay_n12/delaunay_n12.mtx.gr",0,1)
    start = time.time()
    k=4
    truss=njit.graph_ktruss(Graph,k)
    print("After k=",k)
    truss=njit.graph_ktruss(Graph,-1)
    print("After max k")
    truss=njit.graph_ktruss(Graph,-2)
    print("After decomposition")
    end = time.time()
    print("----------------------")
    print("truss = njit.graph_ktruss(Graph)")
    print(truss)
    print("Truss analysis takes {:.4f} seconds".format(end-start))

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
    ak.connect(args.hostname, args.port)

    time_ak_truss_graph()
    ak.shutdown()
