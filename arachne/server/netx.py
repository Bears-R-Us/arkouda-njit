import networkx as nx
from itertools import combinations

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
print("Example node attributes:")
for node in list(G.nodes())[:5]:  # Show example nodes and their attributes
    print(f"Node {node}: Cluster {G.nodes[node].get('cluster')}")

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

# Step 8: Calculate and print details for each cluster
for cluster_id, nodes in clusters.items():
    subgraph = G.subgraph(nodes)

    # 1. Calculate Average Edge-Disjoint Paths
    avg_paths = calculate_edge_disjoint_paths(G, nodes)

    # 2. Compute Minimum Cut
    cluster_1, cluster_2, mincut_value = compute_min_cut(subgraph)

    # 3. Get the number of edges inside the cluster
    num_edges_in_cluster = subgraph.number_of_edges()
    
    # 4. Get the number of connected components inside the cluster
    num_connected_components = nx.number_connected_components(subgraph)
    
    # Print the results for the cluster
    print(f"\nCluster ID: {cluster_id}")
    print(f"Cluster Size: {len(nodes)}")
    print(f"Number of Edges in Cluster: {num_edges_in_cluster}")
    print(f"Number of Connected Components in Cluster: {num_connected_components}")
    print(f"Average Edge-Disjoint Paths: {avg_paths}")
    print(f"Min-Cut Size: {mincut_value}")
    
    if cluster_1 and cluster_2:
        print(f"Cluster 1 Size: {len(cluster_1)}")
        print(f"Cluster 2 Size: {len(cluster_2)}")
    else:
        print("Cluster too small to compute min-cut.")
