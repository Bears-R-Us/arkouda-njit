import arkouda as ak
import arachne as ar
import scipy as sp
import networkx as nx
import matplotlib.pyplot as plt
import os

# Connect to Arkouda server
ak.connect("n115", 5555)

import pandas as pd

cluster_dict = {}

# Read the file and populate the dictionary
with open('/scratch/users/md724/DataSets/wcc/test_clustering.tsv', 'r') as file:
    for line in file:
        # Remove any leading/trailing whitespace
        line = line.strip()
        # Skip empty lines
        if not line:
            continue
        # Split the line into node and cluster number
        node_str, cluster_str = line.split('\t')
        node = int(node_str)
        cluster_num = int(cluster_str)
        # Add the node to the corresponding cluster
        if cluster_num in cluster_dict:
            cluster_dict[cluster_num].append(node)
        else:
            cluster_dict[cluster_num] = [node]

# Read the TSV file using pandas
network_df = pd.read_csv("/scratch/users/md724/DataSets/wcc/test_network.tsv", sep="\t", header=None, names=["src", "dst"])
network_df['type'] = 'T1'

# Create an undirected graph from the data
G = nx.from_pandas_edgelist(network_df, source='src', target='dst', create_using=nx.Graph())

# Print the number of nodes and edges in the graph
num_nodes = G.number_of_nodes()
num_edges = G.number_of_edges()
print(f"Graph has {num_nodes} nodes and {num_edges} edges.")

# Print all clusters and their sizes
for cluster_num, nodes in cluster_dict.items():
    cluster_size = len(nodes)
    print(f"Cluster {cluster_num}: {cluster_size} nodes")

# Check each cluster for nodes with degree < 2
for cluster_num, nodes in cluster_dict.items():
    # Get the subgraph of the current cluster
    G_subgraph = G.subgraph(nodes)

    # Calculate degrees of nodes in the subgraph
    degrees = dict(G_subgraph.degree())

    # Count nodes with degree less than 2
    low_degree_nodes = [node for node, degree in degrees.items() if degree < 2]

    low_degree_count = len(low_degree_nodes)
    size_difference = len(nodes) - low_degree_count  # Calculate the difference

    print(f"In Cluster {cluster_num}: {low_degree_count} < Degree 2. Actual Cluster {cluster_num} size: {size_difference}")

    #if low_degree_nodes:
    #    print(f"Nodes with degree less than 2 in Cluster {cluster_num}: {low_degree_nodes}")

# Create an Arachne Graph.
ar_network_graph = ar.Graph()
ar_network_graph.add_edges_from(ak.array(network_df["src"]), ak.array(network_df["dst"]))

filePath = "/scratch/users/md724/DataSets/wcc/clustering.tsv"
print("Running Arachne") 
clusters = ar.well_connected_components(ar_network_graph, filePath, "/scratch/users/md724/DataSets/wcc")

print("clusters = ", clusters)
print("clusters.size = ", clusters.size)
ak.shutdown()
