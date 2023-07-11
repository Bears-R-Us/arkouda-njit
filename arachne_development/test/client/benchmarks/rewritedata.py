#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak
import random
import string
import arachne_development.graph as njit

TYPES = ('int64', 'float64', 'bool', 'str')

def time_ak_write():
    print("Graph Truss Analysis")
    cfg = ak.get_config()
    print("server Hostname =",cfg["serverHostname"])
    print("Number of Locales=",cfg["numLocales"])
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])
    HomeDir="/rhome/zhihui/"
    EdgeList=[ [28980,5242,2,0,HomeDir+"Adata/SNAP/ca-GrQc.txt.gr"],\
            [51971,9877,2,0,HomeDir+"Adata/SNAP/ca-HepTh.txt.gr"],\
            [88234,4039,2,0,HomeDir+"Adata/SNAP/facebook_combined.txt"],\
            [103689,8277,2,0,HomeDir+"Adata/SNAP/wiki"],\
            [106762,26475,3,0,HomeDir+"Adata/SNAP/as-caida20071105.txt.gr"],\
            [186936,23133,2,0,HomeDir+"Adata/SNAP/ca-CondMat.txt.gr"],\
            [237010,12008,2,0,HomeDir+"Adata/SNAP/ca-HepPh.txt.gr"],\
            [367662,36692,2,0,HomeDir+"Adata/SNAP/email-Enron.gr"],\
            [396160,18772,2,0,HomeDir+"Adata/SNAP/ca-AstroPh.txt.gr"],\
            [428156,58228,2,0,HomeDir+"Adata/SNAP/loc-brightkite_edges.txt"],\
            [508837,75879,2,0,HomeDir+"Adata/SNAP/soc-Epinions1.txt.gr"],\
            [1049866,317080,2,0,HomeDir+"Adata/SNAP/com-dblp.ungraph.txt.gr"],\
            [2987624,1134890,2,0,HomeDir+"Adata/SNAP/com-youtube.ungraph.txt.gr"],\
            [3387388,4033394,2,0,HomeDir+"Adata/SNAP/amazon0601.txt.gr"],\
            [12508413,456626,2,0,HomeDir+'Adata/higgs-social_network.edgelist.pr'],\
            [68993773,4847571,2,0,HomeDir+"Adata/SNAP/soc-LiveJournal1.txt"],\
            [14855842,456626,2,0,HomeDir+"Adata/higgs-social_network.edgelist"],\
            [117185083,3072441,2,0,HomeDir+"Adata/com-orkut.ungraph.txt.gr"],\
            ]

    MtxDelaunay=[ [3056,1024,2,0,HomeDir+"Adata/Delaunay/delaunay_n10/delaunay_n10.mtx"],\
            [6127,2048,2,0,HomeDir+"Adata/Delaunay/delaunay_n11/delaunay_n11.mtx"] ,\
            [12264, 4096,2,0,HomeDir+"Adata/Delaunay/delaunay_n12/delaunay_n12.mtx"] ,\
            [24547,8192,2,0,HomeDir+"Adata/Delaunay/delaunay_n13/delaunay_n13.mtx"] ,\
            [49122,16384,2,0,HomeDir+"Adata/Delaunay/delaunay_n14/delaunay_n14.mtx"] ,\
            [98274,32768,2,0,HomeDir+"Adata/Delaunay/delaunay_n15/delaunay_n15.mtx"] ,\
            [196575,65536,2,0,HomeDir+"Adata/Delaunay/delaunay_n16/delaunay_n16.mtx"],\
            [393176,131072,2,0,HomeDir+"Adata/Delaunay/delaunay_n17/delaunay_n17.mtx"],\
            [786396,262144,2,0,HomeDir+"Adata/Delaunay/delaunay_n18/delaunay_n18.mtx"],\
            [1572823,524288,2,0,HomeDir+"Adata/Delaunay/delaunay_n19/delaunay_n19.mtx"],\
            [3145686,1048576,2,0,HomeDir+"Adata/Delaunay/delaunay_n20/delaunay_n20.mtx"],\
            [6291408,2097152,2,0,HomeDir+"Adata/Delaunay/delaunay_n21/delaunay_n21.mtx"],\
            [12582869,4194304,2,0,HomeDir+"Adata/Delaunay/delaunay_n22/delaunay_n22.mtx"],\
            [25165784,8388608,2,0,HomeDir+"Adata/Delaunay/delaunay_n23/delaunay_n23.mtx"],\
            [50331601,16777216,2,0,HomeDir+"Adata/Delaunay/delaunay_n24/delaunay_n24.mtx"],\
            ]
    MtxOther=[[28854312,23947347,2,0,HomeDir+"Adata/road_usa/road_usa.mtx"],\
            ]
    BigMtxFile=[ 
            [232705452,214005017,2,0,HomeDir+"Adata/SNAP/kmer_V1r.mtx"],\
            [180292586,170728175,2,0,HomeDir+"Adata/SNAP/kmer_A2a.mtx"],\
            [298113762,18520486,2,0,HomeDir+"Adata/SNAP/uk-2002.mtx"],\
            [936364282,39459925,2,0,HomeDir+"Adata/SNAP/uk-2005.mtx"],\
              ]
    MtxRGG=[ \
            [14487995,2097152,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_21_s0/rgg_n_2_21_s0.mtx"],\
            [30359198,4194304,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_22_s0/rgg_n_2_22_s0.mtx"],\
            [63501393,8388608,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_23_s0/rgg_n_2_23_s0.mtx"],\
            [132557200,16777216,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_24_s0/rgg_n_2_24_s0.mtx"],\
              ]
    MtxKron=[ \
            [2456398,65536,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn16/kron_g500-logn16.mtx"],\
            [5114375,131072,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn17/kron_g500-logn17.mtx"],\
            [10583222,262144,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn18/kron_g500-logn18.mtx"],\
            [21781478,524288,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn19/kron_g500-logn19.mtx"],\
            [44620272,1048576,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn20/kron_g500-logn20.mtx"],\
              ]

    start = time.time()
    for i in EdgeList:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        njit.graph_file_preprocessing(Edges,Vertices,Columns,Directed,str(FileName),0,1,1,0,1,0)
    for i in MtxDelaunay:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        njit.graph_file_preprocessing(Edges,Vertices,Columns,Directed,str(FileName),1,1,1,0,1,0)
    for i in MtxOther:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        njit.graph_file_preprocessing(Edges,Vertices,Columns,Directed,str(FileName),1,1,1,0,1,0)
    for i in MtxRGG:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        njit.graph_file_preprocessing(Edges,Vertices,Columns,Directed,str(FileName),1,1,1,0,1,0)
    for i in MtxKron:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        njit.graph_file_preprocessing(Edges,Vertices,Columns,Directed,str(FileName),1,1,1,0,1,0)
    for i in BigMtxFile:
        Edges=i[0]
        Vertices=i[1]
        Columns=i[2]
        Directed=i[3]
        FileName=i[4]
        print(Edges,",",Vertices,",",Columns,",",Directed,",",str(FileName))
        njit.graph_file_preprocessing(Edges,Vertices,Columns,Directed,str(FileName),1,1,1,0,1,0)
    end = time.time()
    return


def create_parser():
    parser = argparse.ArgumentParser(description="Measure the performance of suffix array building: C= suffix_array(V)")
    parser.add_argument('hostname', help='Hostname of arkouda server')
    parser.add_argument('port', type=int, help='Port of arkouda server')
    return parser


    
if __name__ == "__main__":
    import sys
    
    parser = create_parser()
    args = parser.parse_args()
    ak.verbose = False
    ak.connect(args.hostname, args.port)
    time_ak_write()
    ak.shutdown()
