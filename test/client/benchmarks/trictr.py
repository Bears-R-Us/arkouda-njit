#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak
import random
import string
import arkouda_njit as njit

TYPES = ('int64', 'float64', 'bool', 'str')

def time_ak_tri_ctr(lgNv:int, Ne_per_v:int, p:float,directed:int,weighted:int):
    print("Stream Graph Triangle Counting")
    cfg = ak.get_config()
    print("server Hostname =",cfg["serverHostname"])
    print("Number of Locales=",cfg["numLocales"])
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])
    



    HomeDir="/rhome/zhihui/"
    Test1=[ [53381,26475,3,0,HomeDir+"Adata/SNAP/as-caida20071105.txt.pr"],\
            [198050,18772,2,0,HomeDir+"Adata/SNAP/ca-AstroPh.txt.pr"],\
            [93439,23133,2,0,HomeDir+"Adata/SNAP/ca-CondMat.txt.pr"],\
            [14484,5242,2,0,HomeDir+"Adata/SNAP/ca-GrQc.txt.pr"],\
            [118489,12008,2,0,HomeDir+"Adata/SNAP/ca-HepPh.txt.pr"],\
            [25973,9877,2,0,HomeDir+"Adata/SNAP/ca-HepTh.txt.pr"],\
            [2443408,403394,2,0,HomeDir+"Adata/SNAP/amazon0601.txt.pr"],\
            [2987624,1134890,2,0,HomeDir+"Adata/SNAP/com-youtube.ungraph.txt.pr"]\
             ]
    TestMtx=[ [3056,1024,2,0,HomeDir+"Adata/Delaunay/delaunay_n10/delaunay_n10.mtx.pr"],\
            [6127,2048,2,0,HomeDir+"Adata/Delaunay/delaunay_n11/delaunay_n11.mtx.pr"] ,\
            [12264, 4096,2,0,HomeDir+"Adata/Delaunay/delaunay_n12/delaunay_n12.mtx.pr"] ,\
            [24547,8192,2,0,HomeDir+"Adata/Delaunay/delaunay_n13/delaunay_n13.mtx.pr"] ,\
            [49122,16384,2,0,HomeDir+"Adata/Delaunay/delaunay_n14/delaunay_n14.mtx.pr"] ,\
            [98274,32768,2,0,HomeDir+"Adata/Delaunay/delaunay_n15/delaunay_n15.mtx.pr"] ,\
            [196575,65536,2,0,HomeDir+"Adata/Delaunay/delaunay_n16/delaunay_n16.mtx.pr"] ]

    start = time.time()
    for i in TestMtx:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        Graph=njit.graph_file_read(Edges,Vertices,Columns,Directed,str(FileName),0,0,0,0)
        trictrary=njit.graph_tri_ctr(Graph)
        print("triary = njit.graph_tri_ctr(Graph)")
        print(trictrary)

    for i in Test1:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        Graph=njit.graph_file_read(Edges,Vertices,Columns,Directed,str(FileName),0,0,0,0)
        trictrary=njit.graph_tri_ctr(Graph)
        print("triary = njit.graph_tri_ctr(Graph)")


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

    '''
    if args.correctness_only:
        check_correctness(args.number, args.size, args.trials, args.dtype)
        print("CORRECT")
        sys.exit(0)
    '''
    time_ak_tri_ctr(1,2,3.0,0,0)
