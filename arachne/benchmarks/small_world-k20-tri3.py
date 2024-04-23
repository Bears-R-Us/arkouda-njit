"""Generate small-world directed graph and benchmark for subgraph isomorphism."""

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

def create_small_world_directed_graph(num_nodes, k=20, p=0.5, seed=42):
    """
    Generates a small-world directed graph using the Watts-Strogatz model and returns the src and dst arrays.

    Parameters:
    num_nodes (int): Number of nodes in the graph.
    k (int): Each node is connected to k nearest neighbors in the ring topology.
    p (float): The probability of rewiring each edge.
    seed (int): Seed for the random number generator.

    Returns:
    tuple: A tuple containing two lists (src, dst) representing the source and destination of each edge.
    """
    # Create a Watts-Strogatz small-world graph
    small_world_graph = nx.watts_strogatz_graph(num_nodes, 20, 0.5, seed)
    print("Create a Watts-Strogatz small-world graph with")
    print("with k = 20, p = 0.5")
    # Convert to a directed graph to simulate directed behavior
    small_world_directed = nx.DiGraph(small_world_graph)

    # Extract src and dst arrays
    src = [edge[0] for edge in small_world_directed.edges()]
    dst = [edge[1] for edge in small_world_directed.edges()]

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

    ### Generate a small-world directed graph
    num_nodes = args.n
    print("Beginning of Small-World Directed graph generation")
    src, dst = create_small_world_directed_graph(num_nodes, k=10, p=0.01)  # Example values for k and p
    print("Small-World Directed graph created")

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
    src_subgraph = ak.array([2, 3, 3, 1])
    dst_subgraph = ak.array([3, 0, 1, 2])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])

    # Populate the subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph, "rels1":rels1_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.array([0,1,2,3]), "lbls1":labels1_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst", relationship_columns=["rels1"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1"])

    print("Running Arachne...")
    ### Run subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")

    ### Shutdown Arkouda connection.
    ak.shutdown()
