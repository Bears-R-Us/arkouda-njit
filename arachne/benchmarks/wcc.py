import arkouda as ak
import arachne as ar
import scipy as sp
import networkx as nx
import matplotlib.pyplot as plt
import os



# NOTE: Make sure to change the server name to whatever is applicable in your environment. If running locally, then use only ak.connect().
ak.connect("kruskal-login1.lps.umd.edu", 5555)

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

# Print all clusters and their sizes
for cluster_num, nodes in cluster_dict.items():
    cluster_size = len(nodes)
    print(f"Cluster {cluster_num}: {cluster_size} nodes")

# Find the cluster with the maximum number of nodes
max_cluster_num = None
max_cluster_nodes = []
max_cluster_size = 0

for cluster_num, nodes in cluster_dict.items():
    cluster_size = len(nodes)
    if cluster_size > max_cluster_size:
        max_cluster_size = cluster_size
        max_cluster_num = cluster_num
        max_cluster_nodes = nodes

# Assign the nodes of the biggest cluster to the variable 'cluster'
cluster = max_cluster_nodes

# Print the cluster and its size
#print(f"cluster = {cluster};")
print(f"Cluster {max_cluster_num} is the biggest cluster with {max_cluster_size} nodes")


# Read the TSV file using pandas
network_df = pd.read_csv("/scratch/users/md724/DataSets/wcc/test_network.tsv", sep="\t", header=None, names=["src", "dst"])
network_df['type'] = 'T1'

# Create an undirected graph from the data
G = nx.from_pandas_edgelist(network_df, source='src', target='dst', create_using=nx.Graph())

# Check for self-loops
self_loops = list(nx.selfloop_edges(G))
if self_loops:
    print(f"Self-loops detected: {self_loops}")
else:
    print("No self-loops detected.")
    
# Create an Arachne Graph.
ar_network_graph = ar.Graph()
ar_network_graph.add_edges_from(ak.array(network_df["src"]), ak.array(network_df["dst"]))

filePath = "/scratch/users/md724/DataSets/wcc/clustering.tsv"
print("Running Arachne") 
clusters = ar.well_connected_components(ar_network_graph,filePath,"/scratch/users/md724/DataSets/wcc")

print("clusters = ", clusters)
print("clusters.size = ", clusters.size)
ak.shutdown()