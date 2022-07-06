#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak
import random
import string
import arkouda_njit as njit


def time_ak_truss_graph():

    print("Graph Truss Analysis")
    cfg = ak.get_config()

    print("Number of Locales=",cfg["numLocales"])
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])
    HomeDir="/rhome/zhihui/"
    Test1=[ [14484,5242,2,0,HomeDir+"Adata/SNAP/ca-GrQc.txt.pr"],\
            [25973,9877,2,0,HomeDir+"Adata/SNAP/ca-HepTh.txt.pr"],\
            [53381,26475,3,0,HomeDir+"Adata/SNAP/as-caida20071105.txt.pr"],\
            [88234,4039,2,0,HomeDir+"Adata/SNAP/facebook_combined.txt.pr"],\
            [93439,23133,2,0,HomeDir+"Adata/SNAP/ca-CondMat.txt.pr"],\
            [118489,12008,2,0,HomeDir+"Adata/SNAP/ca-HepPh.txt.pr"],\
            [198050,18772,2,0,HomeDir+"Adata/SNAP/ca-AstroPh.txt.pr"],\
            [183831,36692,2,0,HomeDir+"Adata/SNAP/email-Enron.gr.pr"],\
            [214078,58228,2,0,HomeDir+"Adata/SNAP/loc-brightkite_edges.txt.pr"],\
            [405740,75879,2,0,HomeDir+"Adata/SNAP/soc-Epinions1.txt.pr"],\
            [2443408,403394,2,0,HomeDir+"Adata/SNAP/amazon0601.txt.pr"],\
            [2987624,1134890,2,0,HomeDir+"Adata/SNAP/com-youtube.ungraph.txt.pr"]\
#            [68993773,4847570,2,0,HomeDir+"Adata/SNAP/soc-LiveJournal1.txt"],\
             ]
    TestMtx=[ [3056,1024,2,0,HomeDir+"Adata/Delaunay/delaunay_n10/delaunay_n10.mtx.pr"],\
            [6127,2048,2,0,HomeDir+"Adata/Delaunay/delaunay_n11/delaunay_n11.mtx.pr"] ,\
            [12264, 4096,2,0,HomeDir+"Adata/Delaunay/delaunay_n12/delaunay_n12.mtx.pr"] ,\
            [24547,8192,2,0,HomeDir+"Adata/Delaunay/delaunay_n13/delaunay_n13.mtx.pr"] ,\
            [49122,16384,2,0,HomeDir+"Adata/Delaunay/delaunay_n14/delaunay_n14.mtx.pr"] ,\
            [98274,32768,2,0,HomeDir+"Adata/Delaunay/delaunay_n15/delaunay_n15.mtx.pr"] ,\
            [196575,65536,2,0,HomeDir+"Adata/Delaunay/delaunay_n16/delaunay_n16.mtx.pr"],\
            [393176,131072,2,0,HomeDir+"Adata/Delaunay/delaunay_n17/delaunay_n17.mtx.pr"],\
            [786396,262144,2,0,HomeDir+"Adata/Delaunay/delaunay_n18/delaunay_n18.mtx.pr"],\
            [1572823,524288,2,0,HomeDir+"Adata/Delaunay/delaunay_n19/delaunay_n19.mtx.pr"],\
            [3145686,1048576,2,0,HomeDir+"Adata/Delaunay/delaunay_n20/delaunay_n20.mtx.pr"],\
            [6291408,2097152,2,0,HomeDir+"Adata/Delaunay/delaunay_n21/delaunay_n21.mtx.pr"],\
            [12582869,4194304,2,0,HomeDir+"Adata/Delaunay/delaunay_n22/delaunay_n22.mtx.pr"],\
            [25165784,8388608,2,0,HomeDir+"Adata/Delaunay/delaunay_n23/delaunay_n23.mtx.pr"],\
            [50331601,16777216,2,0,HomeDir+"Adata/Delaunay/delaunay_n24/delaunay_n24.mtx.pr"],\
              ]
    TestRGG=[ \
            [14487995,2097148,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_21_s0/rgg_n_2_21_s0.mtx.pr"],\
            [30359198,4194301,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_22_s0/rgg_n_2_22_s0.mtx.pr"],\
            [63501393,8388607,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_23_s0/rgg_n_2_23_s0.mtx.pr"],\
            [132557200,16777215,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_24_s0/rgg_n_2_24_s0.mtx.pr"],\
              ]
    TestKron=[ \
            [2456071,55321,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn16/kron_g500-logn16.mtx.pr"],\
            [5113985,107909,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn17/kron_g500-logn17.mtx.pr"],\
            [10582686,210155,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn18/kron_g500-logn18.mtx.pr"],\
            [21780787,409175,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn19/kron_g500-logn19.mtx.pr"],\
            [44619402,795241,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn20/kron_g500-logn20.mtx.pr"],\
              ]

    start = time.time()
    for i in TestMtx:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        Graph=njit.graph_file_read(Edges,Vertices,Columns,Directed,str(FileName),0,0,0,0)
        k=4
        truss=njit.graph_ktruss(Graph,k)
        print("After k=",k)
        truss=njit.graph_ktruss(Graph,-1)
        print("After max k")
        truss=njit.graph_ktruss(Graph,-2)
        print("After decomposition")
    for i in Test1:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        Graph=njit.graph_file_read(Edges,Vertices,Columns,Directed,str(FileName),0,0,0,0)
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
    print("Truss batch test")
    ak.connect(args.hostname, args.port)
    time_ak_truss_graph()
    ak.shutdown()
