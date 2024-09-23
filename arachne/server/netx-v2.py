import networkx as nx
from itertools import combinations
import math

# Define the file paths
network_file = "/scratch/users/md724/DataSets/wcc/test_network.tsv"
clustering_file = "/scratch/users/md724/DataSets/wcc/clustering.tsv"

# Step 1: Load the graph from test_network.tsv as an undirected graph
G = nx.Graph()  # Undirected graph

# Read the test_network.tsv file and add edges to the graph
with open(network_file, 'r') as f:
    for line in f:
        src, dst = map(int, line.strip().split())
        G.add_edge(src, dst)

# Add a default capacity of 1 to all edges in the graph
for u, v in G.edges():
    G[u][v]['capacity'] = 1

# Step 2: Load the clustering.tsv file and store the cluster information
cluster_dict = {}

with open(clustering_file, 'r') as f:
    for line in f:
        node, cluster = map(int, line.strip().split())
        cluster_dict[node] = cluster

# Step 3: Assign cluster information to the nodes in the graph
nx.set_node_attributes(G, cluster_dict, 'cluster')

# Step 4: Print summary of the graph
print("Graph loaded with", G.number_of_nodes(), "nodes and", G.number_of_edges(), "edges.")


# Step 5: Group nodes by cluster
clusters = {}
for node, data in G.nodes(data=True):
    cluster_id = data['cluster']
    if cluster_id not in clusters:
        clusters[cluster_id] = []
    clusters[cluster_id].append(node)

# Step 6: Calculate edge-disjoint paths for each cluster
def calculate_edge_disjoint_paths(G, nodes):
    subgraph = G.subgraph(nodes)  # Create a subgraph for the cluster
    total_paths = 0
    count = 0
    for nodeA, nodeB in combinations(subgraph.nodes(), 2):
        try:
            paths = nx.edge_disjoint_paths(subgraph, nodeA, nodeB)
            num_paths = len(list(paths))  # Convert generator to list and count
            total_paths += num_paths
            count += 1
        except nx.NetworkXNoPath:
            count += 1
        except Exception as e:
            print(f"Error calculating paths between {nodeA} and {nodeB}: {e}")
            continue

    if count > 0:
        return total_paths / count
    else:
        return 0

# Step 7: Compute min-cut for each cluster
def compute_min_cut(subgraph):
    nodes = list(subgraph.nodes)
    if len(nodes) < 2:
        return None, None, 0  # If there are less than 2 nodes, no cut possible

    s = nodes[0]  # Source node
    t = nodes[1]  # Sink node

    # Use NetworkX's minimum cut function with a uniform capacity of 1
    cut_value, (cluster_1, cluster_2) = nx.minimum_cut(subgraph, s, t, capacity='capacity')

    return cluster_1, cluster_2, cut_value

# Step 8: Recursive min-cut process for each cluster
def recursive_min_cut(cluster_id, subgraph, depth=0):
    cluster_size = len(subgraph.nodes)
    if cluster_size < 2:
        print("Cluster size is too small to cut.")
        return

    # Compute the number of edges and connected components in the cluster
    num_edges_in_cluster = subgraph.number_of_edges()
    num_connected_components = nx.number_connected_components(subgraph)

    # Compute Average Edge-Disjoint Paths
    avg_paths = calculate_edge_disjoint_paths(G, subgraph.nodes)

    # Compute the min-cut
    cluster_1, cluster_2, mincut_value = compute_min_cut(subgraph)

    # Print cluster information
    print(f"\n{'-' * (depth * 2)}Cluster ID: {cluster_id} (Depth: {depth})")
    print(f"{'-' * (depth * 2)}Cluster Size: {cluster_size}")
    print(f"{'-' * (depth * 2)}Number of Edges in Cluster: {num_edges_in_cluster}")
    print(f"{'-' * (depth * 2)}Number of Connected Components in Cluster: {num_connected_components}")
    print(f"{'-' * (depth * 2)}Average Edge-Disjoint Paths: {avg_paths}")
    print(f"{'-' * (depth * 2)}Min-Cut Size: {mincut_value}")

    # Check if cluster is well connected
    if mincut_value > math.log10(cluster_size):
        print(f"{'-' * (depth * 2)}(*)Cluster is well connected.")
        return

    # If cluster is not well connected, recursively apply min-cuts to both subclusters
    if cluster_1 and cluster_2:
        print(f"{'-' * (depth * 2)}Cluster 1 Size: {len(cluster_1)}")
        print(f"{'-' * (depth * 2)}Cluster 2 Size: {len(cluster_2)}")

        # Recurse for both clusters
        recursive_min_cut(cluster_id, subgraph.subgraph(cluster_1), depth + 1)
        recursive_min_cut(cluster_id, subgraph.subgraph(cluster_2), depth + 1)

# Step 9: Apply recursive min-cut for each cluster
for cluster_id, nodes in clusters.items():
    subgraph = G.subgraph(nodes)
    recursive_min_cut(cluster_id, subgraph)
