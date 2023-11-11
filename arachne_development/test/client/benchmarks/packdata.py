#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import os
import random
import string

def packdata(NewDir):

    OriginDir="/rhome/zhihui/"
    HomeDir=""

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
            [2443408,403394,2,0,HomeDir+"Adata/SNAP/amazon0601.txt.pr"],\
            [68993773,4847571,2,0,HomeDir+"Adata/SNAP/soc-LiveJournal1.txt"],\
            [14855842,456626,2,0,HomeDir+"Adata/higgs-social_network.edgelist"],\
            [117185083,3072441,2,0,HomeDir+"Adata/com-orkut.ungraph.txt.gr"],\
            ]
    MtxEdgeList=[ [14496,5242,2,0,HomeDir+"Adata/SNAP/ca-GrQc.mtx"],\
            [25998,9877,2,0,HomeDir+"Adata/SNAP/ca-HepTh.mtx"],\
            [93497,23133,2,0,HomeDir+"Adata/SNAP/ca-CondMat.mtx"],\
            [106762,31379,3,0,HomeDir+"Adata/SNAP/as-caida.mtx"],\
            [118521,12008,2,0,HomeDir+"Adata/SNAP/ca-HepPh.mtx"],\
            [183831,36692,2,0,HomeDir+"Adata/SNAP/email-Enron.mtx"],\
            [198110,18772,2,0,HomeDir+"Adata/SNAP/ca-AstroPh.mtx"],\
            [214078,58228,2,0,HomeDir+"Adata/SNAP/loc-Brightkite.mtx"],\
            [508837,75888,2,0,HomeDir+"Adata/SNAP/soc-Epinions1.mtx"],\
            [1049866,317080,2,0,HomeDir+"Adata/SNAP/com-DBLP.mtx"],\
            [2987624,1134890,2,0,HomeDir+"Adata/SNAP/com-Youtube.mtx"],\
            [3387388,403394,2,0,HomeDir+"Adata/SNAP/amazon0601.mtx"],\
            [14855842,456626,2,0,HomeDir+"Adata/SNAP/higgs-twitter.mtx"],\
            [19753078,1634989,2,0,HomeDir+"Adata/SNAP/wikipedia-20051105.mtx"],\
            [68993773,4847571,2,0,HomeDir+"Adata/SNAP/soc-LiveJournal1.mtx"],\
            [117185083,3072441,2,0,HomeDir+"Adata/SNAP/com-Orkut.mtx"],\
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
            [180292586,170728175,2,0,HomeDir+"Adata/SNAP/kmer_A2a.mtx"],\
            [232705452,214005017,2,0,HomeDir+"Adata/SNAP/kmer_V1r.mtx"],\
            [298113762,18520486,2,0,HomeDir+"Adata/SNAP/uk-2002.mtx"],\
#            [936364282,39459925,2,0,HomeDir+"Adata/SNAP/uk-2005.mtx"],\
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
    ProSNAP=[ [14484,5242,2,0,HomeDir+"Adata/SNAP/ca-GrQc.txt.pr"],\
            [25973,9877,2,0,HomeDir+"Adata/SNAP/ca-HepTh.txt.pr"],\
            [53381,26475,2,0,HomeDir+"Adata/SNAP/as-caida20071105.txt.pr"],\
            [88234,4039,2,0,HomeDir+"Adata/SNAP/facebook_combined.txt.pr"],\
            [93439,23133,2,0,HomeDir+"Adata/SNAP/ca-CondMat.txt.pr"],\
            [118489,12008,2,0,HomeDir+"Adata/SNAP/ca-HepPh.txt.pr"],\
            [198050,18772,2,0,HomeDir+"Adata/SNAP/ca-AstroPh.txt.pr"],\
            [1049866,317080,2,0,HomeDir+'Adata/SNAP/com-dblp.ungraph.txt.gr.pr'],\
            [183831,36692,2,0,HomeDir+"Adata/SNAP/email-Enron.gr.pr"],\
            [214078,58228,2,0,HomeDir+"Adata/SNAP/loc-brightkite_edges.txt.pr"],\
            [405740,75879,2,0,HomeDir+"Adata/SNAP/soc-Epinions1.txt.pr"],\
            [2443408,403394,2,0,HomeDir+"Adata/SNAP/amazon0601.txt.pr"],\
            [2987624,1134890,2,0,HomeDir+"Adata/SNAP/com-youtube.ungraph.txt.pr"],\
            [25004123,4847571,2,0,HomeDir+'Adata/SNAP/soc-LiveJournal1.txt.pr']
            ]
    ProDelaunay=[ [3056,1024,2,0,HomeDir+"Adata/Delaunay/delaunay_n10/delaunay_n10.mtx.pr"],\
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
    ProPBig=[ [14855842,456626,2,0,HomeDir+"Adata/higgs-social_network.edgelist"],\
            [117185083,3072441,2,0,HomeDir+"Adata/com-orkut.ungraph.txt"],\
            [180292586,170728175,2,0,HomeDir+"Adata/SNAP/kmer_A2a.mtx.pr"],\
            [232705452,214005017,2,0,HomeDir+"Adata/SNAP/kmer_V1r.mtx.pr"],\
            [261787258,18484117,2,0,HomeDir+"Adata/SNAP/uk-2002.mtx.pr"],\
            [783027125,39454746,2,0,HomeDir+"Adata/SNAP/uk-2005.mtx.pr"],\
             ]

    TestMtx=[ [28854312,23947347,2,0,HomeDir+"Adata/road_usa/road_usa.mtx"],\
              ]
    ProRGG=[ \
            [14487995,2097148,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_21_s0/rgg_n_2_21_s0.mtx.pr"],\
            [30359198,4194301,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_22_s0/rgg_n_2_22_s0.mtx.pr"],\
            [63501393,8388607,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_23_s0/rgg_n_2_23_s0.mtx.pr"],\
            [132557200,16777215,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_24_s0/rgg_n_2_24_s0.mtx.pr"],\
              ]
    ProKron=[ \
            [2456071,55321,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn16/kron_g500-logn16.mtx.pr"],\
            [5113985,107909,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn17/kron_g500-logn17.mtx.pr"],\
            [10582686,210155,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn18/kron_g500-logn18.mtx.pr"],\
            [21780787,409175,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn19/kron_g500-logn19.mtx.pr"],\
            [44619402,795241,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn20/kron_g500-logn20.mtx.pr"],\
              ]

    start = time.time()
    for i in MtxEdgeList:
        FileName=i[4]
        print("cp -r -f --parent "+OriginDir+FileName+" "+NewDir+"/") 
        os.system("cp -r -f --parent "+OriginDir+FileName+" "+NewDir+"/") 
    return

    for i in MtxOther:
        FileName=i[4]
        print("cp -r -f --parent "+OriginDir+FileName+" "+NewDir+"/") 
        os.system("cp -r -f --parent "+OriginDir+FileName+" "+NewDir+"/") 
    for i in BigMtxFile:
        FileName=i[4]
        print("cp -r -f --parent "+OriginDir+FileName+" "+NewDir+"/") 
        os.system("cp -r -f --parent "+OriginDir+FileName+" "+NewDir+"/") 
    for i in MtxDelaunay:
        FileName=i[4]
        print("cp -r -f --parent "+OriginDir+FileName+" "+NewDir+"/") 
        os.system("cp -r -f --parent "+OriginDir+FileName+" "+NewDir+"/") 
    return


def create_parser():
    parser = argparse.ArgumentParser(description="Copy Adata to another directory")
    parser.add_argument('NewDir', help='Absolute dir')
    return parser


    
if __name__ == "__main__":
    import sys
    parser = create_parser()
    args = parser.parse_args()
    
    print(args.NewDir)
    packdata(args.NewDir)
