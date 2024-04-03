#import tkinter
#import matplotlib
#matplotlib.use('TkAgg')
#matplotlib.use('Agg')
import matplotlib.pyplot as plt
import os
import copy

import numpy as np
import pandas as pd
import sys

FontSize=16

def plotdeg(filename,numbins):
         data = pd.read_csv(filename, sep=' ', header=None)
         plt.rcParams.update({'font.size': FontSize})
         ax=data.hist(column=1,bins=numbins,grid=False)
         name=copy.deepcopy(filename)
         name = os.path.basename(name)  # Remove directory
         name = name.split(".")[0]
         plt.yscale('log',base=2) 

         plt.subplots_adjust(bottom=0.19)
         plt.ylabel("Number of Degrees")
         plt.xlabel("Degree")
         plt.title("Degrees of "+name)
         plt.savefig(filename+"-Hist.png")
         plt.show()
         plt.close()

if (True):

    HomeDir="/rhome/zhihui/"
    EdgeList=[ [117185083,3072441,2,0,HomeDir+"Adata/com-orkut.ungraph.txt.gr"],\
            ]

    MtxFile=[ [3056,1024,2,0,HomeDir+"Adata/Delaunay/delaunay_n10/delaunay_n10.mtx"],\
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
            [28854312,23947347,2,0,HomeDir+"Adata/road_usa/road_usa.mtx"],\
            [180292586,170728175,2,0,HomeDir+"Adata/SNAP/kmer_V1r.mtx"],\
            [232705452,214005017,2,0,HomeDir+"Adata/SNAP/kmer_A2a.mtx"],\
            [298113762,18520486,2,0,HomeDir+"Adata/SNAP/uk-2002.mtx"],\
            [936364282,39459925,2,0,HomeDir+"Adata/SNAP/uk-2005.mtx"],\
            ]
    BigMtxFile=[ [180292586,170728175,2,0,HomeDir+"Adata/SNAP/kmer_V1r.mtx"],\
            [232705452,214005017,2,0,HomeDir+"Adata/SNAP/kmer_A2a.mtx"],\
            [298113762,18520486,2,0,HomeDir+"Adata/SNAP/uk-2002.mtx"],\
            [936364282,39459925,2,0,HomeDir+"Adata/SNAP/uk-2005.mtx"],\
              ]
    TestRGG=[ \
            [14487995,2097152,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_21_s0/rgg_n_2_21_s0.mtx"],\
            [30359198,4194304,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_22_s0/rgg_n_2_22_s0.mtx"],\
            [63501393,8388608,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_23_s0/rgg_n_2_23_s0.mtx"],\
            [132557200,16777216,2,0,HomeDir+"Adata/rgg_n_2/rgg_n_2_24_s0/rgg_n_2_24_s0.mtx"],\
              ]
    TestKron=[ \
            [2456398,65536,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn16/kron_g500-logn16.mtx"],\
            [5114375,131072,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn17/kron_g500-logn17.mtx"],\
            [10583222,262144,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn18/kron_g500-logn18.mtx"],\
            [21781478,524288,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn19/kron_g500-logn19.mtx"],\
            [44620272,1048576,3,0,HomeDir+"Adata/kron_g500-logn/kron_g500-logn20/kron_g500-logn20.mtx"],\
              ]

    for i in EdgeList:
        print(str(i[4])+".deg")
        print(str(i[4])+".deg")
        plotdeg(str(i[4])+".deg",200)
    for i in MtxFile:
        print(str(i[4])+".deg")
        print(str(i[4])+".deg")
        plotdeg(str(i[4])+".deg",200)

