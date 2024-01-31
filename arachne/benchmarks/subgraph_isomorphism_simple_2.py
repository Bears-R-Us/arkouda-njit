"""Simple correctness check for subgraph isomorphism."""
import argparse
import time

import networkx as nx
import arachne as ar
import arkouda as ak

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument('--print_isos', action='store_true', help="Print isos?")

    return script_parser

if __name__ == "__main__":
    #### Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()

    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    #### Run NetworkX subgraph isomorphism.
    # Get the NetworkX version
    print("NetworkX version:", nx.__version__)
    # Creating directed graphs
    G = nx.DiGraph()
    H = nx.DiGraph()

    # Clearing graphs (optional in this context)
    G.clear()
    H.clear()

    # Adding nodes and edges to directed graphs
    G.add_nodes_from(range(0, 30))
    G.add_edges_from([(5, 0), (5, 1), (1, 6), (2, 1), (3, 2), (3, 7),(7, 1), (7, 10),(7, 2),
                      (8, 4),(4, 9),(9, 5), (9, 8), (6, 9), (6, 5), (6, 7), (10, 6), (10 , 11),
                      (11, 3), (11, 12), (6, 13), (14, 6), (14, 10), (10, 15), (15, 11),
                      (16, 11), (16, 12), (12, 17), (17, 22), (17, 29), (20, 17),(16, 20), (17, 16),
                      (20, 19), (19, 16),(15, 16), (15, 19), (15, 14), (13, 14), (13, 18), (14, 18), (14, 21),(21, 15), 
                      (19, 21), (21, 23), (23, 25), (25, 26), (25, 24),(27,25), (27, 20), (27, 28),
                      (26, 27)])

    H.add_nodes_from(range(0, 4))
    H.add_edges_from([(0, 1), (1, 2), (2, 0), (1, 3)])

    NODE_LABEL = 'NodeLabel'
    EDGE_LABEL = 'EdgeLabel'
    nx.set_node_attributes(G, NODE_LABEL, 'label1')
    nx.set_edge_attributes(G, EDGE_LABEL, 'Y1')

    nx.set_node_attributes(H, NODE_LABEL, 'label1')
    nx.set_edge_attributes(H, EDGE_LABEL, 'Y1')

    # Measure execution time.
    start_time = time.time()

    # Find subgraph isomorphisms of H in G.
    GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)

    # List of dicts. For each dict, keys is original graph vertex, values are subgraph vertices.
    subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())

    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")

    #### Run Arachne subgraph isomorphism.
    # 1. Create vertices, edges, and attributes for main property graph.
    src_prop_graph = ak.array([5, 5, 1, 6, 6, 7, 7, 7 , 2, 10, 10, 10, 15, 15, 15, 15, 14, 14, 14, 14, 19, 19, 21, 21, 23, 25, 25, 26, 27, 27, 27, 20, 20, 17, 17, 3, 3, 11, 11, 12, 17, 16, 16, 6,  6, 13, 13, 9, 9, 8, 4])
    dst_prop_graph = ak.array([0, 1, 6, 5, 7, 1, 2, 10, 1, 11, 6 , 15, 11, 16, 19, 14, 10,  6, 21, 18, 16, 21, 15, 23, 25, 24, 26, 27, 25, 28, 20, 17, 19, 22, 29, 2, 7,  3, 12, 17, 16, 12, 11, 9, 13, 14, 18, 5, 8, 4, 9])
    labels1_prop_graph = ak.array(["lbl1"] * 30)
    labels2_prop_graph = ak.array(["lbl2"] * 30)
    rels1_prop_graph = ak.array(["rel1"] * 51)
    rels2_prop_graph =  ak.array(["rel2"] * 51)

    # 2. Transer data above into main property graph.
    prop_graph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_prop_graph, "dst":dst_prop_graph,
                            "rels1":rels1_prop_graph, "rels2":rels2_prop_graph})
    node_df_h = ak.DataFrame({"nodes": ak.arange(0,30), "lbls1":labels1_prop_graph,
                              "lbls2":labels2_prop_graph})
    prop_graph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1","rels2"])
    prop_graph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])

    # 3. Create vertices, edges, and attributes for subgraph.
    src_subgraph = ak.array([0, 1, 2, 1])
    dst_subgraph = ak.array([1, 2, 0, 3])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    labels2_subgraph = ak.array(["lbl2", "lbl2", "lbl2", "lbl2"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])
    rels2_subgraph = ak.array(["rel2", "rel2", "rel2", "rel2"])

    # 4. Transer data above into subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph,
                            "rels1":rels1_subgraph, "rels2":rels2_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.arange(0,4), "lbls1":labels1_subgraph,
                              "lbls2":labels2_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1","rels2"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])

    # 5. Run the subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")

    #### Compare Arachne subgraph isomorphism to NetworkX.
    isos_list = isos.to_list()
    isos_sublists = [isos_list[i:i+4] for i in range(0, len(isos_list), 4)]

    isos_as_dicts = []
    subgraph_vertices = [0, 1, 2, 3]
    for iso in isos_sublists:
        isos_as_dicts.append(dict(zip(iso, subgraph_vertices)))

    for iso in isos_as_dicts:
        if iso not in subgraph_isomorphisms:
            print("missing is: ", iso)
            print("ERROR: Subgraph isomorphisms do not match!")
            break
    print("here new")
    if args.print_isos:
        for iso in isos_as_dicts:
            print(iso)

        print()

        for iso in subgraph_isomorphisms:
            print(iso)

    ak.shutdown()
