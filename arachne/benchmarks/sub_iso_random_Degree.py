import argparse
import time
import arachne as ar
import arkouda as ak
import numpy as np
import networkx as nx
import random
import matplotlib.pyplot as plt

def create_parser():
    """Creates the command line parser for this script"""
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

def create_random_directed_graph(num_nodes, p):
    """
    Generates a random directed graph (Erdős-Rényi model) and returns the src and dst arrays.
    
    Parameters:
    num_nodes (int): Number of nodes in the graph.
    p (float): Probability of creating an edge between two nodes.
    
    Returns:
    tuple: A tuple containing two lists (src, dst) representing the source and destination of each edge.
    """
    # Create a random graph using Erdős–Rényi model
    random_graph = nx.gnp_random_graph(num_nodes, p, seed=42, directed=True)

    # Extract src and dst arrays
    src = [edge[0] for edge in random_graph.edges()]
    dst = [edge[1] for edge in random_graph.edges()]

    return random_graph, src, dst

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

    ### Generate an Erdős-Rényi random graph
    num_nodes = args.n  # Number of nodes
    p = 0.0005  # Probability of edge creation
    print("Beginning of Random Directed graph with P= ", p)

    random_graph, src, dst = create_random_directed_graph(num_nodes, p)
    print("Random Directed graph created")

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

    # Generate sets of node labels and edge relationships.
    labels_set = ak.array(["lbl" + str(x) for x in range(1, args.x+1)])
    relationships_set = ak.array(["rel" + str(y) for y in range(1, args.y+1)])

    # Assign labels and relationships to nodes and edges.
    node_labels = labels_set[ak.randint(0, len(labels_set), num_nodes)]
    edge_relationships = relationships_set[ak.randint(0, len(relationships_set), num_edges)]

    # Create dataframe to load into a new property graph.
    edge_df = ak.DataFrame({"src": edges[0], "dst": edges[1], "rels1": edge_relationships})
    node_df = ak.DataFrame({"nodes": nodes, "lbls1": node_labels})

    # Create new property graph with node labels and edge relationships.
    prop_graph = ar.PropGraph()
    prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1"])
    prop_graph.load_node_attributes(node_df, node_column="nodes", label_columns=["lbls1"])

    # Create the subgraph we are searching for.
    src_subgraph = ak.array([0, 1, 1, 2])
    dst_subgraph = ak.array([1, 2, 3, 0])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])

    # Populate the subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src": src_subgraph, "dst": dst_subgraph, "rels1": rels1_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.array([0, 1, 2, 3]), "lbls1": labels1_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                  relationship_columns=["rels1"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1"])

    print("Running Arachne...")
    # Run subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")

    ### Run NetworkX subgraph isomorphism.
    # Grab vertex and edge data from the Arachne dataframes.
    graph_node_information = prop_graph.get_node_attributes()
    graph_edge_information = prop_graph.get_edge_attributes()
    subgraph_node_information = subgraph.get_node_attributes()
    subgraph_edge_information = subgraph.get_edge_attributes()

    # The 4 for loops below convert internal integer labels to original strings.
    for (column, array) in graph_node_information.items():
        if column != "nodes":
            mapper = prop_graph.label_mapper[column]
            graph_node_information[column] = mapper[array]

    for (column, array) in graph_edge_information.items():
        if column not in ("src", "dst"):
            mapper = prop_graph.relationship_mapper[column]
            graph_edge_information[column] = mapper[array]

    for (column, array) in subgraph_node_information.items():
        if column != "nodes":
            mapper = subgraph.label_mapper[column]
            subgraph_node_information[column] = mapper[array]

    for (column, array) in subgraph_edge_information.items():
        if column not in ("src", "dst"):
            mapper = subgraph.relationship_mapper[column]
            subgraph_edge_information[column] = mapper[array]

    # Convert Arkouda dataframes to Pandas dataframes to NetworkX graph attributes.
    G = nx.from_pandas_edgelist(graph_edge_information.to_pandas(), source='src',
                                target='dst', edge_attr=True, create_using=nx.DiGraph)
    H = nx.from_pandas_edgelist(subgraph_edge_information.to_pandas(), source='src',
                                target='dst', edge_attr=True, create_using=nx.DiGraph)

    # Convert graph node attributes to Pandas dfs, remove nodes, and convert rows to dicts.
    graph_node_attributes = graph_node_information.to_pandas()
    graph_nodes_from_df = list(graph_node_attributes.pop("nodes"))
    graph_node_attributes = graph_node_attributes.to_dict('index')
    graph_node_attributes_final = {}

    # Convert subgraph node attributes to Pandas dfs, remove nodes, and convert rows to dicts.
    subgraph_node_attributes = subgraph_node_information.to_pandas()
    subgraph_nodes_from_df = list(subgraph_node_attributes.pop("nodes"))
    subgraph_node_attributes = subgraph_node_attributes.to_dict('index')
    subgraph_node_attributes_final = {}

    # Convert Pandas index to original node index.
    for key in graph_node_attributes:
        graph_node_attributes_final[graph_nodes_from_df[key]] = graph_node_attributes[key]

    for key in subgraph_node_attributes:
        subgraph_node_attributes_final[subgraph_nodes_from_df[key]] = subgraph_node_attributes[key]

    # Set the node attributes for G and H from dicts.
    nx.set_node_attributes(G, graph_node_attributes_final)
    nx.set_node_attributes(H, subgraph_node_attributes_final)

    print("Running NetworkX... ")

    # Calculate the degrees
    in_degrees = dict(G.in_degree())
    out_degrees = dict(G.out_degree())

    # Calculate the total degrees (sum of in-degree and out-degree)
    total_degrees = {node: in_degrees[node] + out_degrees[node] for node in G.nodes()}

    # Calculate mean degrees
    mean_in_degree = np.mean(list(in_degrees.values()))
    mean_out_degree = np.mean(list(out_degrees.values()))
    mean_total_degree = np.mean(list(total_degrees.values()))

    # Plot the degree distribution
    degrees = list(total_degrees.values())
    plt.figure(figsize=(10, 6))
    plt.hist(degrees, bins=50, color='b', alpha=0.7, edgecolor='black')
    plt.title('Node Degree Distribution')
    plt.xlabel('Degree')
    plt.ylabel('Frequency')
    plt.yscale('log')  # Use a logarithmic scale for better visualization of the distribution
    plt.show()

    # Calculate the expected degree
    expected_in_degree = p * (num_nodes - 1)
    expected_out_degree = p * (num_nodes - 1)
    expected_total_degree = 2 * p * (num_nodes - 1)

    print(f'Expected in-degree: {expected_in_degree}')
    print(f'Expected out-degree: {expected_out_degree}')
    print(f'Expected total degree: {expected_total_degree}')

    print(f'Mean in-degree: {mean_in_degree}')
    print(f'Mean out-degree: {mean_out_degree}')
    print(f'Mean total degree: {mean_total_degree}')
    
    # Find subgraph isomorphisms of H in G.
    start_time = time.time()
    GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)
    subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())
    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")
    print(f"NetworkX found: {len(subgraph_isomorphisms)} isos")


    ak.shutdown()
