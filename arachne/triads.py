import arkouda as ak
import arachne as ar
import pandas as pd
import numpy as np
import argparse
import time
import sys

def build_triad(src, dst):
    akarray_src = ak.array(src)
    akarray_dst = ak.array(dst)

    H = ar.PropGraph()
    H.add_edges_from(akarray_src, akarray_dst)

    return H

def get_triads(idx:str):
    src1 = [0, 0]
    dst1 = [1, 2]

    src2 = [0, 2]
    dst2 = [1, 0]

    src3 = [0, 2, 0]
    dst3 = [1, 0, 2]

    src4 = [1, 2]
    dst4 = [0, 0]

    src5 = [1, 2, 2]
    dst5 = [0, 0, 1]

    src6 = [0, 2, 2, 1]
    dst6 = [2, 0, 1, 0]

    src7 = [1, 2, 0]
    dst7 = [0, 0, 2]

    src8 = [1, 2, 0, 0]
    dst8 = [0, 0, 2, 1]

    src9 = [0, 1, 2]
    dst9 = [1, 2, 0]

    src10 = [0, 1, 2, 0]
    dst10 = [1, 2, 0, 2]

    src11 = [0, 1, 2, 2]
    dst11 = [1, 2, 0, 1]

    src12 = [0, 1, 1, 2, 0]
    dst12 = [1, 0, 2, 0, 2]

    src13 = [3, 3, 1, 2]
    dst13 = [1, 0, 2, 3]

    src14 = [0, 1, 2, 0]
    dst14 = [1, 2, 3, 3]

    triads = { "1": (src1, dst1),
               "2": (src2, dst2),
               "3": (src3, dst3),
               "4": (src4, dst4),
               "5": (src5, dst5),
               "6": (src6, dst6),
               "7": (src7, dst7),
               "8": (src8, dst8),
               "9": (src9, dst9),
               "10": (src10, dst10),
               "11": (src11, dst11),
               "12": (src12, dst12),
               "13": (src13, dst13),
               "14": (src14, dst14)
               }
    
    return triads[idx]

def get_gnp_random_graph(n, p, seed):
    G = ar.gnp_random_graph(n, p, create_using=ar.PropGraph, seed=seed)
    print(f"Built G(n,p) graph with {len(G):,} vertices and {G.size():,} edges.")

    return G

def get_scale_free_random_graph(n, m, seed):
    G = ar.barabasi_albert_graph(n, m, create_using=ar.PropGraph, seed=seed)
    print(f"Built scale-free graph with {len(G):,} vertices and {G.size():,} edges.")

    return G

def get_small_world_random_graph(n, k, p, seed):
    G = ar.watts_strogatz_graph(n, k, p, create_using=ar.PropGraph, seed=seed)
    print(f"Built small-world graph with {len(G):,} vertices and {G.size():,} edges.")

    return G

def add_attributes(graph, num_node_lbls, num_edge_lbls, vals_per_lbl, seed):
    nodes = graph.nodes()
    edges = graph.edges()

    n = len(nodes)
    m = len(edges[0])

    node_attributes = []
    edge_attributes = []

    for i in range(num_node_lbls):
        node_attributes.append(ak.randint(0,vals_per_lbl,n,seed=seed*i,dtype=ak.int64))

    for i in range(num_edge_lbls):
        edge_attributes.append(ak.randint(0,vals_per_lbl,m,seed=seed*i,dtype=ak.int64))

    lbls_dict = {"lbl"+str(idx):attribute for idx, attribute in enumerate(node_attributes)}
    rels_dict = {"rel"+str(idx):attribute for idx, attribute in enumerate(edge_attributes)}

    node_dict = {"nodes" : nodes}
    edge_dict = {"src" : edges[0], "dst" : edges[1]}

    node_dict.update(lbls_dict)
    edge_dict.update(rels_dict)

    node_df = ak.DataFrame(node_dict)
    edge_df = ak.DataFrame(edge_dict)

    graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst")
    graph.load_node_attributes(node_df, node_column="nodes")

def to_glasgow_format(graph, file_name):
    print("Converting inputted graph to Glasgow format...")
    # Extract edges
    internal_src, internal_dst = graph._internal_edges()
    src = internal_src.to_list()  
    dst = internal_dst.to_list()

    # Extract edge attributes
    graph_edge_attributes = graph.get_edge_attributes()
    edge_df = graph_edge_attributes.to_pandas()
    edge_df.drop(['src', 'dst'], axis=1, inplace=True)

    # Generate edge data
    print("Preparing edge data...")
    edge_data = []
    for i in range(len(src)):
        edge_str = f"{src[i]}>{dst[i]}"
        if not edge_df.empty:
            attr_values = [str(edge_df.iloc[i][col]) for col in edge_df.columns]
            edge_str += "," + ",".join(attr_values)
        edge_data.append(edge_str)

    # Generate node data
    print("Preparing node data...")
    graph_node_attributes = graph.get_node_attributes()
    if graph_node_attributes.size > 0:
        node_df = graph_node_attributes.to_pandas()
        node_data = [
            f"{idx},," + ",".join(str(row[col]) for col in node_df.columns if col != 'nodes')
            for idx, (_, row) in enumerate(node_df.iterrows())
        ]
    else:
        num_nodes = sorted(set(src).union(dst))
        node_data = [f"{node}," for node in num_nodes]

    # Write to file
    print(f"Writing graph to {file_name}...")
    path_to_write = "/scratch/users/md724/SI_Paper_Graphs/" + file_name
    with open(path_to_write, "w") as f:
        f.write("\n".join(edge_data) + "\n")
        f.write("\n".join(node_data))

    print(f"Graph saved to {file_name}.\n")

def to_vf3p_format(graph, file_name):
    print("Converting inputted graph to VF3P format...")
    src, dst = graph._internal_edges()
    src_list = src.to_list()
    dst_list = dst.to_list()
    edge_df = graph.get_edge_attributes().to_pandas()
    node_df = graph.get_node_attributes().to_pandas()

    nodes = sorted(set(src_list).union(dst_list))
    curr_idx = 0
    edge_df.drop(['src', 'dst'], axis=1, inplace=True)
    lines = []

    lines.append(str(len(nodes)))
    lines.append("")

    print("Preparing node data...")
    if not node_df.empty:
        for node in nodes:
            row = node_df[node_df['nodes'] == node]
            attrs = " ".join(str(row[col].iloc[0]) for col in node_df.columns if col != 'nodes')
            lines.append(f"{node} {attrs}")
    else:
        for node in nodes:
            lines.append(f"{node} 0")
    lines.append("")
            
    print("Preparing edge data...")
    for node in nodes:
        node_edges = []
        while curr_idx < len(src_list) and src_list[curr_idx] == node:
            node_edges.append(curr_idx)
            curr_idx += 1
            
        lines.append(str(len(node_edges)))
        for i in node_edges:
            edge_str = f"{src_list[i]} {dst_list[i]}"
            lines.append(edge_str)
        if node != nodes[-1]: # Don't add empty line after last node
            lines.append("")

    print(f"Writing graph to {file_name}...")
    path_to_write = "/scratch/users/md724/SI_Paper_Graphs/" + file_name
    with open(path_to_write, "w") as f:
        f.write("\n".join(lines) + "\n")

    print(f"Graph saved to {file_name}\n")

def get_real_world_graph(absolute_path_to_file, file_type, src_col, dst_col, id):
    G = ar.PropGraph()
    if file_type == "mtx":
        (src,dst) = ar.read_matrix_market_file(absolute_path_to_file, directed=True, 
                                               only_edges=True)
        if id == "roadNet-CA" or id == "roadNet-TX":
            newSrc = ak.concatenate([src,dst])
            newDst = ak.concatenate([dst,src])
            src = newSrc
            dst = newDst
    elif file_type == "csv":
        df = pd.read_csv(absolute_path_to_file)
        (src,dst) = (ak.array(df[src_col]), ak.array(df[dst_col]))
    else:
        raise ValueError(f"Unrecognized file_type {file_type}")
    G.add_edges_from(src, dst)
    print(f"Built real-world graph with {len(G):,} vertices and {G.size():,} edges.")

    return G

def run_benchmark(G, H, idx, trials, prob_reorder, match_type):
    print(f"Beginning the search for triad {idx} with {trials} iterations...")
    r_s_si = np.array([])
    r_p_si = np.array([])
    for trial in range(1, trials+1):
        print(f"Running trial {trial}...")
        start = time.time()
        matches1 = ar.subgraph_isomorphism(G, H, algorithm_type="si",reorder_type="structural", 
                                         return_isos_as="vertices",match_type=match_type)
        end = time.time()
        r_s_si = np.append(r_s_si, end-start)
        print(f"Structural SI took: {end-start:.4f} sec(s)")
        print(f"Structural SI found: {len(matches1[0])/len(H):,} {match_type}s")

        if prob_reorder:
            start = time.time()
            matches2 = ar.subgraph_isomorphism(G, H, algorithm_type="si",reorder_type="probability", 
                                             return_isos_as="vertices",match_type=match_type)
            end = time.time()
            r_p_si = np.append(r_p_si, end-start)
            print(f"Probability SI took: {end-start:.4f} sec(s)")
            print(f"Probability SI found: {len(matches2[0])/len(H):,} {match_type}s")
        
        print()
    
    print("Final results structural SI:")
    print(f"         min = {np.min(r_s_si):.4f}")
    print(f"         max = {np.max(r_s_si):.4f}")
    print(f"        mean = {np.mean(r_s_si):.4f}")
    print(f"    variance = {np.var(r_s_si):.4f}")
    print(f"         std = {np.std(r_s_si):.4f}")
    print(f"         iqr = {(np.percentile(r_s_si, 75) - np.percentile(r_s_si, 25)):.4f}")
    print(f"      95 per = {np.percentile(r_s_si, 95):.4f}")
    print(f"      99 per = {np.percentile(r_s_si, 99):.4f}")
    print(f"trimmed mean = {np.mean(r_s_si[np.abs(r_s_si-np.mean(r_s_si))<2*np.std(r_s_si)]):.4f}")

    if prob_reorder:
        print(f"         min = {np.min(r_p_si):.4f}")
        print(f"         max = {np.max(r_p_si):.4f}")
        print(f"        mean = {np.mean(r_p_si):.4f}")
        print(f"    variance = {np.var(r_p_si):.4f}")
        print(f"         std = {np.std(r_p_si):.4f}")
        print(f"         iqr = {(np.percentile(r_p_si, 75) - np.percentile(r_p_si, 25)):.4f}")
        print(f"      95 per = {np.percentile(r_p_si, 95):.4f}")
        print(f"      99 per = {np.percentile(r_p_si, 99):.4f}")
        print(f"trimmed mean = {np.mean(r_p_si[np.abs(r_p_si-np.mean(r_p_si))<2*np.std(r_p_si)]):.4f}")

def add_injected_attributes(graph, num_node_lbls, num_edge_lbls, vals_per_lbl, seed, 
                            edge_idx, node_idx):
    nodes = graph.nodes()
    edges = graph.edges()

    n = len(nodes)
    m = len(edges[0])

    node_attributes = []
    edge_attributes = []

    for i in range(num_node_lbls):
        data = ak.randint(1, vals_per_lbl, n, seed=seed*i, dtype=ak.int64)
        data[node_idx] = 0
        node_attributes.append(data)

    for i in range(num_edge_lbls):
        data = ak.randint(1, vals_per_lbl, m, seed=seed*i, dtype=ak.int64)
        data[edge_idx] = 0
        edge_attributes.append(data)

    lbls_dict = {"lbl"+str(idx):attribute for idx, attribute in enumerate(node_attributes)}
    rels_dict = {"rel"+str(idx):attribute for idx, attribute in enumerate(edge_attributes)}

    node_dict = {"nodes" : nodes}
    edge_dict = {"src" : edges[0], "dst" : edges[1]}

    node_dict.update(lbls_dict)
    edge_dict.update(rels_dict)

    node_df = ak.DataFrame(node_dict)
    edge_df = ak.DataFrame(edge_dict)

    graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst")
    graph.load_node_attributes(node_df, node_column="nodes")

def run_data_injection_benchmark(G, H, tri_idx, trials, prob_reorder, match_type, 
                                 num_node_lbls, num_edge_lbls, vals_per_lbl, 
                                 write_graphs, graph_id, seed, initial_num_node_lbls, 
                                 initial_num_edge_lbls, initial_vals_per_lbls, 
                                 num_to_inject):
    (graph_src, graph_dst) = G.edges()
    (subgraph_src, subgraph_dst) = H.edges()

    num_edges = H.size()
    num_nodes = len(H)

    subgraph_edge_idx = ak.arange(num_edges)
    subgraph_node_idx = ak.arange(num_nodes)

    rng = ak.random.default_rng(seed=seed)

    message = f"Running SI with initial {initial_num_node_lbls} node lbls, "\
              f"{initial_num_edge_lbls} edge lbls, and {initial_vals_per_lbls} vals per lbl..."
    print(message)
    start = time.time()
    (match_vertices,_,match_src,match_dst) = ar.subgraph_isomorphism(G, H, algorithm_type="si",
                                                                    reorder_type="structural", 
                                                                    return_isos_as="complete",
                                                                    match_type=match_type)
    end = time.time()
    num_matches = len(match_vertices) // num_nodes
    print(f"Initial search time took {end-start:.4f} secs and found {num_matches} {match_type}s")
    print()

    # Pick the indices for the isos to be data injected from isos as edges. 
    # This will also give us the vertices.
    selected_edges = rng.choice(num_matches, size=num_to_inject, replace=False)

    # Extract the edges.
    offsets = (selected_edges * num_edges).to_ndarray()
    range_array = np.arange(num_edges)
    edges = offsets[:, np.newaxis] + range_array
    edges = edges.flatten()

    # Get the src and dst values to inject to.
    src_to_inject = match_src[ak.array(edges)]
    dst_to_inject = match_dst[ak.array(edges)]

    # Extract the vertices.
    vertices = ak.concatenate([src_to_inject, dst_to_inject])
    vertices_set = ak.GroupBy(vertices).unique_keys

    # Get the edge idx to inject into.
    edge_idx = ak.find([ak.array(src_to_inject),ak.array(dst_to_inject)],[graph_src,graph_dst])
    nonexisting_edges = edge_idx == -1
    edge_idx = edge_idx[~nonexisting_edges]

    # Get the node idx to inject into.
    node_idx = ak.find(vertices_set, G.nodes())

    print("Generating copies of graphs...")
    start = time.time()
    G = ar.PropGraph(); G.add_edges_from(graph_src, graph_dst)
    H = ar.PropGraph(); H.add_edges_from(subgraph_src, subgraph_dst)
    end = time.time()
    print(f"Creating copies of graphs took {end-start:.4f} secs")
    print()

    print(f"Injecting {num_to_inject} {match_type}s...")
    start = time.time()
    add_injected_attributes(G, num_node_lbls, num_edge_lbls, vals_per_lbl, seed, 
                            edge_idx, node_idx)
    add_injected_attributes(H, num_node_lbls, num_edge_lbls, vals_per_lbl, seed, 
                            subgraph_edge_idx, subgraph_node_idx)
    end = time.time()
    print(f"Injecting {match_type}s with {num_to_inject} {match_type}s took {end-start:.4f} secs")
    print()
    
    if write_graphs:
        file_name = "di_triad_" + str(tri_idx) + "_" + str(seed) + "_" + \
                    str(num_node_lbls) + "_" + str(num_edge_lbls) + "_" + \
                    str(vals_per_lbl)
        to_glasgow_format(H, file_name + ".csv")
        file_name = f"di_{graph_id}" + str(num_node_lbls) + "_" + \
                    str(num_edge_lbls) + "_" + str(vals_per_lbl)
        to_glasgow_format(G, file_name + ".csv")
        ak.shutdown()
        sys.exit()
    
    run_benchmark(G, H, tri_idx, trials, prob_reorder, match_type)

def create_parser():
    # Arkouda things.
    parser = argparse.ArgumentParser(description="Benchmark for motif finding directed triads")
    parser.add_argument("hostname", help="Hostname of the arkouda server")
    parser.add_argument("port", type=int, default=5555, help="Port used by the arkouda server")

    # Triad selection.
    parser.add_argument("--idx", type=str, help="Triad idx to run.")

    # Graph type selection.
    parser.add_argument("--gnp", action="store_true", help="G(n,p) graph?")
    parser.add_argument("--scale_free", action="store_true", help="Scale-free graph?")
    parser.add_argument("--small_world", action="store_true", help="Small-world graph?")
    parser.add_argument("--real", action="store_true", help="Real-world graph?")
    parser.add_argument("--filepath", type=str, help="Absolute path to file to use.")
    parser.add_argument("--filetype", type=str, help="mtx or csv.")
    parser.add_argument("--src_col", type=str, default="", help="Source column of csv file.")
    parser.add_argument("--dst_col", type=str, default="", help="Destination column of csv file.")

    # Graph parameters.
    parser.add_argument("--n", type=int, help="Number of nodes")
    parser.add_argument("--p", type=float, help="Edge probability for G(n,p) and small-world")
    parser.add_argument("--m", type=int, help="Number of edges for scale-free")
    parser.add_argument("--k", type=int, help="Initial degree for small-world")
    parser.add_argument("--seed", type=int, help="Random seed")

    # Vertex and edge attribute parameters.
    parser.add_argument("--num_node_lbls", type=int, help="Number of node labels")
    parser.add_argument("--num_edge_lbls", type=int, help="Number of edge labels")
    parser.add_argument("--vals_per_lbl", type=int, help="Number of values per label.")

    # Experimental parameters.
    parser.add_argument("--trials", type=int, help="Number of trials")
    parser.add_argument("--prob_reorder", action="store_true", help="Run probability reorder?")
    parser.add_argument("--match_type", type=str, help="iso or mono")

    # Data injection parameters.
    parser.add_argument("--data_injection", action="store_true", help="Run data injection harness?")
    parser.add_argument("--initial_num_node_lbls", type=int, 
                        help="Initial node label creation uses this.")
    parser.add_argument("--initial_num_edge_lbls", type=int,
                        help="Initial edge label creation uses this.")
    parser.add_argument("--initial_vals_per_lbl", type=int,
                        help="Number of values to use per label first.")
    parser.add_argument("--num_to_inject", type=int,
                        help="Number of subgraphs to inject.")

    # Graph conversion parameters.
    parser.add_argument("--subgraph_to_glasgow", action="store_true", 
                        help="Saves subgraph in Glasgow format. Exits out after saving graph.")
    parser.add_argument("--graph_to_glasgow", action="store_true",
                        help="Saves graph in Glasgow format. Exits out after saving graph.")
    parser.add_argument("--subgraph_to_vf3p", action="store_true",
                        help="Saves subgraph in VF3P format. Exits out after saving graph.")
    parser.add_argument("--graph_to_vf3p", action="store_true",
                        help="Saves graph in VF3P format. Exits out after saving graph.")
    parser.add_argument("--write_all", action="store_true",
                        help="Writes both subgraph and graph to VF3P and Glasgow formats.")
    parser.add_argument("--data_injection_write", action="store_true", 
                        help="Outputs files during data injection benmark.")
    parser.add_argument("--fileid", type=str, help="ID of real-world file.")

    return parser

if __name__ == "__main__":
    parser = create_parser()
    args = parser.parse_args()

    ak.connect(args.hostname, args.port)
    print()

    triad = get_triads(args.idx)

    start = time.time()
    H = build_triad(triad[0], triad[1])
    end = time.time()
    print(f"Data graph construction took: {end-start:.4f} sec(s)")

    start = time.time()
    if not args.data_injection:
        add_attributes(H, args.num_node_lbls, args.num_edge_lbls, args.vals_per_lbl, args.seed)
    else:
        add_attributes(H, args.initial_num_node_lbls, args.initial_num_edge_lbls, 
                       args.initial_vals_per_lbl, args.seed)
    end = time.time()
    print(f"Adding attributes to data graph took: {end-start:2f} sec(s)")
    print()

    if args.subgraph_to_glasgow:
        file_name = "triad_" + str(args.idx) + "_" + str(args.seed) + "_" + \
                    str(args.num_node_lbls) + "_" + str(args.num_edge_lbls) + "_" + str(args.vals_per_lbl)
        to_glasgow_format(H, file_name + ".csv")
        ak.shutdown()
        sys.exit()

    if args.subgraph_to_vf3p:
        file_name = "triad_" + str(args.idx) + "_" + str(args.seed) + "_" + \
                    str(args.num_node_lbls) + "_" + str(args.num_edge_lbls) + "_" + str(args.vals_per_lbl)
        to_vf3p_format(H, file_name + ".grf")
        ak.shutdown()
        sys.exit()

    if args.write_all:
        file_name = "triad_" + str(args.idx) + "_" + str(args.seed) + "_" + \
            str(args.num_node_lbls) + "_" + str(args.num_edge_lbls) + "_" + str(args.vals_per_lbl)
        to_glasgow_format(H, file_name + ".csv")
        file_name = "triad_" + str(args.idx) + "_" + str(args.seed) + "_" + \
            str(args.num_node_lbls) + "_" + str(args.num_edge_lbls) + "_" + str(args.vals_per_lbl)
        to_vf3p_format(H, file_name + ".grf")


    start = time.time()
    if args.gnp:
        G = get_gnp_random_graph(args.n, args.p, args.seed)
        file_name = "gnp_" + str(args.n) + "_" + str(args.p) + "_" + str(args.seed) + "_" + \
                    str(args.num_node_lbls) + "_" + str(args.num_edge_lbls) + "_" + str(args.vals_per_lbl)
        graph_id = "gnp_" + str(args.n) + "_" + str(args.p) + "_" + str(args.seed) + "_"
    elif args.scale_free:
        G = get_scale_free_random_graph(args.n, args.m, args.seed)
        file_name = "sf_" + str(args.n) + "_" + str(args.m) + "_" + str(args.seed) + "_" + \
                    str(args.num_node_lbls) + "_" + str(args.num_edge_lbls) + "_" + str(args.vals_per_lbl)
        graph_id = "sf_" + str(args.n) + "_" + str(args.m) + "_" + str(args.seed) + "_"
    elif args.small_world:
        G = get_small_world_random_graph(args.n, args.k, args.p, args.seed)
        file_name = "sw_" + str(args.n) + "_" + str(args.k) + "_" + str(args.p) + "_" + \
                    str(args.num_node_lbls) + "_" + str(args.num_edge_lbls) + "_" + str(args.vals_per_lbl)
        graph_id = "sw_" + str(args.n) + "_" + str(args.k) + "_" + str(args.p) + "_"
    elif args.real:
        G = get_real_world_graph(args.filepath, args.filetype, args.src_col, args.dst_col, args.fileid)
    else:
        raise ValueError("Must specify graph type (--gnp, --scale_free, --small_world, or --real)")
    end = time.time()
    print(f"Host graph construction took: {end-start:.4f} sec(s)")
        
    start = time.time()
    if not args.data_injection:
        add_attributes(G, args.num_node_lbls, args.num_edge_lbls, args.vals_per_lbl, args.seed)
    else:
        add_attributes(G, args.initial_num_node_lbls, args.initial_num_edge_lbls, 
                       args.initial_vals_per_lbl, args.seed)
    end = time.time()
    print(f"Adding attributes to host graph took: {end-start:2f} sec(s)")
    print()

    if args.real:
        file_name = f"{args.fileid}_" + str(args.seed) + "_" +\
                    str(args.num_node_lbls) + "_" + str(args.num_edge_lbls) + "_" + str(args.vals_per_lbl)
        graph_id = f"{args.fileid}_" + str(args.seed) + "_"

    if args.graph_to_glasgow:
        to_glasgow_format(G, file_name + ".csv")
        ak.shutdown()
        sys.exit()

    if args.graph_to_vf3p:
        to_vf3p_format(G, file_name + ".grf")
        ak.shutdown()
        sys.exit()

    if args.write_all:
        to_glasgow_format(G, file_name + ".csv")
        to_vf3p_format(G, file_name + ".grf")
        ak.shutdown()
        sys.exit()

    if args.data_injection:
        run_data_injection_benchmark(G, H, args.idx, args.trials, args.prob_reorder, args.match_type,
                                     args.num_node_lbls, args.num_edge_lbls, args.vals_per_lbl,
                                     args.data_injection_write, graph_id, args.seed,
                                     args.initial_num_node_lbls, args.initial_num_edge_lbls,
                                     args.initial_vals_per_lbl, args.num_to_inject)
    else:
        run_benchmark(G, H, args.idx, args.trials, args.prob_reorder, args.match_type)

    ak.shutdown()
