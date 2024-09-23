import networkx as nx
from itertools import combinations

# Function to calculate edge-disjoint paths for a given subgraph (clique in this case)
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

# Function to compute the min-cut between the first two nodes in the subgraph
def compute_min_cut(subgraph):
    nodes = list(subgraph.nodes)
    if len(nodes) < 2:
        return None, None, 0  # If there are less than 2 nodes, no cut possible

    s = nodes[0]  # Source node
    t = nodes[1]  # Sink node

    # Add default capacity to each edge
    for u, v in subgraph.edges():
        subgraph[u][v]['capacity'] = 1

    # Use NetworkX's minimum cut function with a uniform capacity of 1
    cut_value, (cluster_1, cluster_2) = nx.minimum_cut(subgraph, s, t, capacity='capacity')

    return cluster_1, cluster_2, cut_value

# Calculate and print average edge-disjoint paths and min-cut for cliques of sizes 2 to 10
for size in range(2, 11):
    # Create a complete graph (clique) of size 'n'
    G_clique = nx.complete_graph(size)
    
    # Compute the average edge-disjoint paths for the clique
    avg_paths = calculate_edge_disjoint_paths(G_clique, G_clique.nodes)
    
    # Compute the min-cut for the clique
    cluster_1, cluster_2, mincut_value = compute_min_cut(G_clique)
    
    # Print the results
    print(f"Clique Size: {size}")
    print(f"  Average Edge-Disjoint Paths: {avg_paths}")
    print(f"  Min-Cut Value: {mincut_value}")
    if cluster_1 and cluster_2:
        print(f"  Cluster 1 Size: {len(cluster_1)}")
        print(f"  Cluster 2 Size: {len(cluster_2)}")
    print("-----------------------------------------------------")
def print_results(G, label):
    # Compute the average edge-disjoint paths
    avg_paths = calculate_edge_disjoint_paths(G, G.nodes)
    
    # Compute the min-cut for the graph
    cluster_1, cluster_2, mincut_value = compute_min_cut(G)
    
    # Print the results
    print(f"{label}")
    print(f"  Average Edge-Disjoint Paths: {avg_paths}")
    print(f"  Min-Cut Value: {mincut_value}")
    if cluster_1 and cluster_2:
        print(f"  Cluster 1 Size: {len(cluster_1)}")
        print(f"  Cluster 2 Size: {len(cluster_2)}")
    print("-----------------------------------------------------")

# Create a graph representing a triangle with a tail
G_triangle_with_tail = nx.Graph()

# Add the triangle part (nodes 0, 1, 2 fully connected)
G_triangle_with_tail.add_edges_from([(0, 1), (1, 2), (2, 0),(1, 3)])



# Print results for the triangle with a tail
print_results(G_triangle_with_tail, "Triangle with a Tail")