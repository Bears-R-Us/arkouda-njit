"""Benchmarking file for subgraph isomorphism."""
import argparse
import time
import arachne as ar
import arkouda as ak
import networkx as nx

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    script_parser.add_argument("m", type=int, default=2000, help="Number of edges for graph")
    script_parser.add_argument("x", type=int, default=5, help="Number of labels for graph")
    script_parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")
    script_parser.add_argument("s", type=int, default=2, help="Random seed for reproducibility")

    return script_parser

if __name__ == "__main__":
    #### Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()

    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    ### Get Arkouda server configuration information.
    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")

    ### Build graph from randomly generated source and destination arrays.
    # 1. Use Arkouda's randint to generate the random edge arrays.
    src = ak.randint(0, args.n, args.m, seed=args.s*2)
    dst = ak.randint(0, args.n, args.m, seed=args.s*4)

    # 2. Build temporary property graph to get sorted edges and nodes lists.
    temp_prop_graph = ar.PropGraph()
    start = time.time()
    temp_prop_graph.add_edges_from(src, dst)
    end = time.time()
    build_time = end - start
    print(f"Building property graph with {len(temp_prop_graph)} vertices and "
          f"{temp_prop_graph.size()} "
          f"edges took {round(build_time,2)} seconds.")

    ### Generate node labels and edge relationships for the graph.
    # 1. Extract node and edge information.
    num_edges = temp_prop_graph.size()
    num_nodes = len(temp_prop_graph)
    edges = temp_prop_graph.edges()
    nodes = temp_prop_graph.nodes()

    # 2. Generate sets of node labels and edge relationships.
    labels_set = ak.array(["lbl" + str(x) for x in range(args.x)])
    relationships_set = ak.array(["rel" + str(y) for y in range(args.y)])

    # 3. Give edges and nodes some labels and relationships.
    node_labels = labels_set[ak.randint(0, len(labels_set), num_nodes)]
    edge_relationships = relationships_set[ak.randint(0, len(relationships_set), num_edges)]

    # 4. Create dataframe to load into a new property graph.
    edge_df = ak.DataFrame({"src":edges[0], "dst":edges[1], "relationships":edge_relationships})
    node_df = ak.DataFrame({"nodes":nodes, "labels":node_labels})

    # 5. Create new property graph with node labels and edge relationships.
    prop_graph = ar.PropGraph()
    prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst",
                                    relationship_columns=["relationships"])
    prop_graph.load_node_attributes(node_df, node_column="nodes", label_columns=["labels"])


    ### Create the subgraph we are searching for.
    # 1. Create labels and relationships to search for.
    src_subgraph = ak.array([0, 1, 2])
    dst_subgraph = ak.array([1, 2, 0])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1"])
    labels2_subgraph = ak.array(["lbl2", "lbl2", "lbl2"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1"])
    rels2_subgraph = ak.array(["rel2", "rel2", "rel2"])

    #2. Populate the subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph,
                            "rels1":rels1_subgraph, "rels2":rels2_subgraph})
    node_df_h = ak.DataFrame({"nodes": src_subgraph, "lbls1":labels1_subgraph,
                              "lbls2":labels2_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1","rels2"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])
    print("Till now it is fine")
    ### Run subgraph isomorphism.
    isos = ar.subgraph_isomorphism(prop_graph,subgraph)
    print("isos =", isos)


    print("src prop = ", src)
    print("dst prop = ", dst)    
    
    print("src subgraph = ", src_subgraph)
    print("dst subgraph = ", dst_subgraph)
 
    print("*************************NETWORKX******************")

    ### Convert Arkouda graph to NetworkX graph
    G = nx.DiGraph()
    for src_node, dst_node in zip(src.to_ndarray(), dst.to_ndarray()):
        G.add_edge(src_node, dst_node)

    for u, v, attrs in G.edges(data=True):
        print(f"Edge from {u} to {v} with attributes {attrs}")
    ### Run subgraph isomorphism using NetworkX
    subgraph_nodes = src_subgraph.to_ndarray()
    subgraph_edges = list(zip(src_subgraph.to_ndarray(), dst_subgraph.to_ndarray()))

    subG = nx.DiGraph()
    subG.add_edges_from(subgraph_edges)
    
    start_time = time.time()

    # Use NetworkX's isomorphism checker
    matcher = nx.algorithms.isomorphism.DiGraphMatcher(G, subG)
    isos_networkx = list(matcher.subgraph_monomorphisms_iter())
    print()
    print("Subgraph occurrences found:")
    for iso_mapping in isos_networkx:
        print("Isomorphism mapping:", iso_mapping)
    print("NetworkX subgraph_isomorphism found ISOs:", len(isos_networkx))
    end_time = time.time()
    elapsed_time = end_time - start_time
    print("Elapsed time:", elapsed_time, "seconds")

    ak.shutdown()
