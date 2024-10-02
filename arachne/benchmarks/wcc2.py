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


# Read the TSV file using pandas
network_df = pd.read_csv("/scratch/users/md724/DataSets/UIUC/wiki_topcats/wiki_topcats_cleaned.tsv", sep="\t", header=None, names=["src", "dst"])
network_df['type'] = 'T1'

# Create an undirected graph from the data
G = nx.from_pandas_edgelist(network_df, source='src', target='dst', create_using=nx.Graph())

# Print the number of nodes and edges in the graph
num_nodes = G.number_of_nodes()
num_edges = G.number_of_edges()
print(f"Graph has {num_nodes} nodes and {num_edges} edges.")


# Create an Arachne Graph.
ar_network_graph = ar.Graph()
ar_network_graph.add_edges_from(ak.array(network_df["src"]), ak.array(network_df["dst"]))

filePath = "/scratch/users/md724/DataSets/UIUC/wiki_topcats/S2_wiki_topcats_leiden.0.001_i2_clustering.tsv"
print("Running Arachne...") 
clusters = ar.well_connected_components(ar_network_graph, filePath, "/scratch/users/md724/DataSets/UIUC/wccOutPut")
# Function to extract information
def extract_cluster_info(cluster_array):
    cluster_info = []
    for i in range(0, len(cluster_array), 3):
        cluster_id = cluster_array[i]
        depth = cluster_array[i+1]
        members = cluster_array[i+2]
        cluster_info.append({
            'cluster_id': cluster_id,
            'depth': depth,
            'members': members
        })
    return cluster_info

# Extract information
info = extract_cluster_info(clusters)
print("and it returned these WCC Clusters:")
# Print the extracted information
for cluster in info:
    print(f"Cluster ID: {cluster['cluster_id']}, Depth: {cluster['depth']}, Members: {cluster['members']}")
#print("clusters = ", clusters)
#print("clusters.size = ", clusters.size)
ak.shutdown()
