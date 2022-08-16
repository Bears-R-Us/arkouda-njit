#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak
import random
import string
import arkouda_njit as njit

TYPES = ('int64', 'float64', 'bool', 'str')

def time_ak_bfs():
    print("Graph BFS")
    cfg = ak.get_config()
    print("server Hostname =",cfg["serverHostname"])
    print("Number of Locales=",cfg["numLocales"])
    print("number of PUs =",cfg["numPUs"])
    print("Max Tasks =",cfg["maxTaskPar"])
    print("Memory =",cfg["physicalMemory"])
    
    lgNv=5
    Ne_per_v=3
    p=0.40
    directed=0
    weighted=0



    HomeDir="/home/gridsan/zdu/"
    Test=[ [14484,5242,2,0,HomeDir+"Adata/ca-GrQc.txt.pr"]]
    Test1=[ [14484,5242,2,0,HomeDir+"Adata/ca-GrQc.txt.pr"],\
            [25973,9877,2,0,HomeDir+"Adata/ca-HepTh.txt.pr"],\
            [53381,26475,3,0,HomeDir+"Adata/as-caida20071105.txt.pr"],\
            [88234,4039,2,0,HomeDir+"Adata/facebook_combined.txt.pr"],\
            [93439,23133,2,0,HomeDir+"Adata/ca-CondMat.txt.pr"],\
            [118489,12008,2,0,HomeDir+"Adata/ca-HepPh.txt.pr"],\
            [198050,18772,2,0,HomeDir+"Adata/ca-AstroPh.txt.pr"],\
            [183831,36692,2,0,HomeDir+"Adata/email-Enron.gr.pr"],\
            [214078,58228,2,0,HomeDir+"Adata/loc-brightkite_edges.txt.pr"],\
            [405740,75879,2,0,HomeDir+"Adata/soc-Epinions1.txt.pr"],\
            [2443408,403394,2,0,HomeDir+"Adata/amazon0601.txt.pr"],\
            [3056,1024,2,0,HomeDir+"Adata/delaunay_n10.mtx.pr"],\
            [393176,131072,2,0,HomeDir+"Adata/delaunay_n17.mtx.pr"]]

    #print(lgNv,Ne_per_v,p,directed,weighted)
    start = time.time()
    #Graph=ak.graph_file_read(91,20,3,directed,"kang.gr")
    #Graph=ak.graph_file_read(3056,1024,2,directed,"../arkouda/data/"+filename)
    #Graph=ak.graph_file_read(393176,131072,2,directed,"../arkouda/data/"+filename)
    #Graph=ak.graph_file_read(786396,262144,2,directed,"../arkouda/data/delaunay/delaunay_n18.gr")
    #Graph=njit.rmat_gen(lgNv, Ne_per_v, p, directed, weighted)
    #Graph=ak.graph_file_read(103689,8276,2,directed,"data/graphs/wiki")
    #Graph=ak.graph_file_read(2981,2888,2,directed,"data/graphs/fb")
    #Graph=njit.graph_file_read(1000,1001,2,directed,"line.gr")
    #Graph=njit.graph_file_read(6,4,2,0,"/home/z/zd4/Mike/arkouda/t.gr")
    Graph=njit.graph_file_read(14484,5242,2,0,HomeDir+"Adata/ca-GrQc.txt.pr",0,0,0,0,1)
    #Graph=ak.graph_file_read(10000,10001,2,directed,"data/10000-1.gr")
    #Graph=ak.graph_file_read(100,101,2,directed,"data/100-1.gr")
    #Graph=ak.graph_file_read(2000,1002,2,directed,"data/2.gr")
    #Graph=ak.graph_file_read(3000,1003,2,directed,"data/3.gr")
    #Graph=ak.graph_file_read(150,53,2,directed,"data/3-50.gr")
    end = time.time()
    #src=njit.graph_query(Graph,"src")
    timings = []
    totalV=int(Graph.n_vertices)
    trials=20
    selectroot = np.random.randint(0, totalV-1, trials)
    for root in selectroot:
        start = time.time()
        _ = njit.graph_bfs(Graph,int(root))
        end = time.time()
        timings.append(end - start)
    tavg = sum(timings) / trials
    print("Average BFS time = {:.4f} s for {} executions".format(tavg,trials))
    print("number of vertices ={}".format(Graph.n_vertices))
    print("number of edges ={}".format(Graph.n_edges))
    print("Average BFS Edges = {:.4f} M/s".format(int(Graph.n_edges)/tavg/1024/1024))
    print("Average BFS Vertices = {:.4f} M/s".format(int(Graph.n_vertices)/tavg/1024/1024))
    #print("Ne_per_v=",Ne_per_v, " p=" ,p)
    #print("Average rate = {:.2f} GiB/sec".format(bytes_per_sec/2**30))


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

    time_ak_bfs()
    ak.shutdown()
