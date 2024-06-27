"""Generate scale-free directed graph and benchmark for subgraph isomorphism."""

import argparse
import time
import arachne as ar
import arkouda as ak
import numpy as np
import networkx as nx
import random
from dotmotif import Motif, GrandIsoExecutor 

def create_parser():
    """Creates the command line parser for this script."""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    script_parser.add_argument("x", type=int, default=5, help="Number of labels for graph")
    script_parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")
    script_parser.add_argument('--print_isos', action='store_true', help="Print isos?")
    return script_parser

def create_scale_free_directed_graph(num_nodes,  alpha=0.41, beta=0.54, gamma=0.05, delta_in=0.2, delta_out=0.2  , seed=42):
#def create_scale_free_directed_graph(num_nodes,  alpha=0.1, beta=0.7, gamma=0.2, delta_in=0.5, delta_out=0.1 , seed=42):
    """
    Generates a scale-free directed graph with specified parameters and returns the src and dst arrays.
    
    Parameters:
    num_nodes (int): Number of nodes in the graph.
    alpha (float): Probability for adding a new node connected to an existing node chosen according to in-degree.
    beta (float): Probability for adding an edge between two existing nodes.
    gamma (float): Probability for adding a new node connected to an existing node chosen according to out-degree.
    delta_in (float): Bias for choosing nodes from in-degree distribution.
    delta_out (float): Bias for choosing nodes from out-degree distribution.
    seed (int): Seed for the random number generator.
    
    Returns:
    tuple: A tuple containing two lists (src, dst) representing the source and destination of each edge.
    """
    scale_free_graph = nx.scale_free_graph(num_nodes, alpha=alpha, beta=beta, gamma=gamma, delta_in=delta_in, delta_out=delta_out, seed=seed)

    # Convert to directed graph and remove self-loops and redundant edges
    G = nx.DiGraph()
    for u, v in scale_free_graph.edges():
        if u != v:  # Remove self-loops
            G.add_edge(u, v)
    
    # Extract src and dst arrays
    src = [edge[0] for edge in G.edges()]
    dst = [edge[1] for edge in G.edges()]
    #print("src = ", src)
    #print("dst = ", dst)
    # Calculate in-degree and out-degree for each node
    #in_degrees = [G.in_degree(n) for n in G.nodes()]
    #out_degrees = [G.out_degree(n) for n in G.nodes()]

    # Print in-degree and out-degree arrays
    #print("In-Degrees:", in_degrees)
    #print("Out-Degrees:", out_degrees)
    #print("src = ", src)
    #print("dst = ", dst)
    return src, dst

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

    ### Generate a scale-free directed graph
    num_nodes = args.n
    print("Beginning of Scale-Free Directed graph generation")
    src, dst = create_scale_free_directed_graph(num_nodes)
    print("Scale-Free Directed graph created")

    src_ak = ak.array(src)
    dst_ak = ak.array(dst)

    # Build temporary property graph to get sorted edges and nodes lists.
    temp_prop_graph = ar.PropGraph()
    start = time.time()
    temp_prop_graph.add_edges_from(src_ak, dst_ak)
    end = time.time()
    build_time = end - start
    print(f"Building property graph with {len(temp_prop_graph)} vertices and "
          f"{temp_prop_graph.size()} "
          f"edges took {round(build_time,2)} seconds.")

    ### Generate node labels and edge relationships for the graph.
    num_edges = temp_prop_graph.size()
    num_nodes = len(temp_prop_graph)
    edges = temp_prop_graph.edges()
    nodes = temp_prop_graph.nodes()

    labels_set = ak.array(["lbl" + str(x) for x in range(1, args.x+1)])
    relationships_set = ak.array(["rel" + str(y) for y in range(1, args.y+1)])

    node_labels = labels_set[ak.randint(0, len(labels_set), num_nodes)]
    edge_relationships = relationships_set[ak.randint(0, len(relationships_set), num_edges)]

    edge_df = ak.DataFrame({"src":edges[0], "dst":edges[1], "rels1":edge_relationships})
    node_df = ak.DataFrame({"nodes":nodes, "lbls1":node_labels})

    # Create new property graph with node labels and edge relationships.
    prop_graph = ar.PropGraph()
    prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst", relationship_columns=["rels1"])
    prop_graph.load_node_attributes(node_df, node_column="nodes", label_columns=["lbls1"])

    ### Create the subgraph we are searching for.
    src_subgraph = ak.array([0, 1, 2, 1])
    dst_subgraph = ak.array([1, 2, 0, 3])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])

    # Populate the subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph, "rels1":rels1_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.array([0,1,2,3]), "lbls1":labels1_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst", relationship_columns=["rels1"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1"])

    print("1st Running Arachne...")
    ### Run subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")


    print("2nd Running Arachne...")
    ### Run subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")
    
    
    print("3rd Running Arachne...")
    ### Run subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")
    
    
    #### Run NetworkX subgraph isomorphism for comparison.
    # Convert Arachne dataframes to NetworkX graph for subgraph isomorphism.
    G = nx.DiGraph()
    G.add_edges_from([(int(src), int(dst)) for src, dst in zip(src_ak.to_ndarray(), dst_ak.to_ndarray())])
    H = nx.DiGraph()
    H.add_edges_from([(int(src), int(dst)) for src, dst in zip(src_subgraph.to_ndarray(), dst_subgraph.to_ndarray())])

    print("Running NetworkX... ")
    
    # Find subgraph isomorphisms of H in G.
    start_time = time.time()
    GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)
    subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())
    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")
    print(f"NetworkX found: {len(subgraph_isomorphisms)} isos")


    motif = Motif("""
    A -> B 
    B -> D
    B -> C
    C -> A
    """)
    print("************************************************************")
    print(" DotMotif....")
    E = GrandIsoExecutor(graph=G)

    # Create the search engine.

    start = time.time()

    results = E.find(motif)
    elapsed_time = time.time() - start_time
    print(f"DotMotif execution time: {elapsed_time} seconds")
    print(f"Dotmotif found: {len(subgraph_isomorphisms)} isos")
    print(len(results))
    
    
    ### Optionally print isomorphisms.
    if args.print_isos:
        print("Arachne isomorphisms:")
        for iso in isos.to_list():
            print(iso)

        print("\nNetworkX isomorphisms:")
        for iso in subgraph_isomorphisms:
            print(iso)

    ### Shutdown Arkouda connection.
    ak.shutdown()
