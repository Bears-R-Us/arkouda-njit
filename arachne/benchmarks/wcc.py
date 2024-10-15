import arkouda as ak
import arachne as ar
import networkx as nx
import pandas as pd
import os

# Connect to Arkouda server. NOTE: Change hostname to your environment's hostname.
ak.connect("n115", 5555)

cluster_dict = {}

# Read the file and populate the dictionary
with open('/scratch/users/md724/arkouda-njit/arachne/data/wcc/test_clustering.tsv', 'r') as file:
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
network_df = pd.read_csv("/scratch/users/md724/arkouda-njit/arachne/data/wcc/test_network.tsv", sep="\t", header=None, names=["src", "dst"])
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


# Create an Arachne graph from a test network file.
ar_network_graph = ar.read_tsv_file(os.path.abspath("/scratch/users/md724/arkouda-njit/arachne/data/wcc/test_network.tsv"))

# Execute wcc with the absolute path to the generate and the create network file.
filePath = os.path.abspath("/scratch/users/md724/DataSets/wcc/test_clustering.tsv")
outputPath = os.path.abspath("/scratch/users/md724/DataSets/wcc/WCC_Output")
clusters = ar.well_connected_components(ar_network_graph, filePath, outputPath, "debug")
print("Number of clusters processed = ", clusters.size)

print("clusters = ", clusters)
print("clusters.size = ", clusters.size)
ak.shutdown()
