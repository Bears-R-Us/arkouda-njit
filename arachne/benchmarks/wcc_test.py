# %%
import arkouda as ak
import arachne as ar
import pandas as pd
import time as time
import networkx as nx
import random


# %%
ak.connect("n83", 5555)

# %%
# Initialize a dictionary to store clusters
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

# Print the pandas DataFrame (optional, just to verify)
#print(network_df)
#print(network_df.head())



# %%
# Concatenate 'src' and 'dst' columns and find unique elements for nodes
unique_nodes = pd.concat([network_df['src'], network_df['dst']]).unique()

# Number of unique nodes
num_unique_nodes = len(unique_nodes)
#num_unique_nodes

# %%
# Number of edges is the length of the DataFrame
num_edges = len(network_df)

# Calculate graph density
d = num_edges / (num_unique_nodes * (num_unique_nodes - 1))
print(f"Graph Density: {d}")

print(f"Number of unique nodes: {num_unique_nodes}")
print(f"Number of edges: {num_edges}")


# %%

# Convert the pandas DataFrame to an Arkouda DataFrame
ak_network_df = ak.DataFrame(network_df)
ak_network_df

# %%
# Create an Arachne PropGraph and load the edge attributes
ar_network_graph = ar.PropGraph()
ar_network_graph.load_edge_attributes(ak_network_df, source_column="src", destination_column="dst", relationship_columns=["type"])


# %%
# Get all nodes and create node attributes
all_nodes = ak.concatenate([ak_network_df['src'], ak_network_df['dst']])
unique_nodes = ak.unique(all_nodes)
lbls = ak.array(["1"] * unique_nodes.size)
network_node_df = ak.DataFrame({"nodes": unique_nodes, "lbls": lbls})
network_node_df


# %%

ar_network_graph.load_node_attributes(network_node_df, node_column="nodes", label_columns=["lbls"])
ar_network_graph

# %%
print("Running Arachne")
filePath = "/scratch/users/md724/DataSets/wcc/clustering.tsv"
print(type(ar_network_graph))  # Check if it's PropGraph
print(type(filePath)) 
clusters = ar.well_connected_components(ar_network_graph,filePath)

print("clusters = ", clusters)

ak.shutdown()

