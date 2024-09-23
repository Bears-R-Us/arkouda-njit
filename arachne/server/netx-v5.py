import networkx as nx
from itertools import combinations
import math

# Function to calculate edge-disjoint paths for a given subgraph (cluster or clique)
def calculate_edge_disjoint_paths(G, nodes):
    subgraph = G.subgraph(nodes).copy()  # Create a copy to modify if needed
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
        avg_paths = total_paths / count
        return avg_paths
    else:
        return 0

# Function to compute the min-cut between two specified nodes in the subgraph
def compute_min_cut(subgraph, source, sink):
    nodes = list(subgraph.nodes)
    if len(nodes) < 2:
        return None, None, 0  # If there are less than 2 nodes, no cut possible

    # Add default capacity to each edge
    for u, v in subgraph.edges():
        subgraph[u][v]['capacity'] = 1

    try:
        # Use NetworkX's minimum cut function with a uniform capacity of 1
        cut_value, (cluster_1, cluster_2) = nx.minimum_cut(subgraph, source, sink, capacity='capacity')
        return cluster_1, cluster_2, cut_value
    except nx.NetworkXUnbounded:
        print(f"Min-cut computation resulted in unbounded flow for nodes {source} and {sink}.")
        return None, None, float('inf')
    except Exception as e:
        print(f"Error computing min-cut between {source} and {sink}: {e}")
        return None, None, 0

# Function to remove all degree-1 nodes from a subgraph
def remove_degree_one_nodes(subgraph):
    initial_node_count = subgraph.number_of_nodes()
    initial_edge_count = subgraph.number_of_edges()
    
    # Identify degree-1 nodes
    degree_one_nodes = [node for node, degree in subgraph.degree() if degree == 1]
    
    # Remove degree-1 nodes
    subgraph.remove_nodes_from(degree_one_nodes)
    
    final_node_count = subgraph.number_of_nodes()
    final_edge_count = subgraph.number_of_edges()
    
    return initial_node_count, final_node_count, initial_edge_count, final_edge_count

# Function to calculate graph density
def calculate_graph_density(subgraph):
    n = subgraph.number_of_nodes()
    if n < 2:
        return 0
    e = subgraph.number_of_edges()
    density = (2 * e) / (n * (n - 1))
    return density

# Function to calculate minimum node degree
def calculate_min_degree(subgraph):
    if subgraph.number_of_nodes() == 0:
        return 0
    return min(dict(subgraph.degree()).values())

# Recursive min-cut process for each cluster
def recursive_min_cut(cluster_id, subgraph, G, depth=0):
    indent = '--' * depth  # Indentation for readability based on recursion depth

    # Remove degree-1 nodes and get node counts
    initial_nodes, final_nodes, initial_edges, final_edges = remove_degree_one_nodes(subgraph)

    # Print node counts before and after removal
    print(f"\n{indent}Cluster ID: {cluster_id} (Depth: {depth})")
    print(f"{indent}Nodes before removal: {initial_nodes}")
    print(f"{indent}Nodes after removal: {final_nodes}")

    # If no nodes left after removal, exit
    if final_nodes == 0:
        print(f"{indent}No nodes left in the cluster after removing degree-1 nodes.")
        return

    # Compute number of edges and connected components after removal
    num_edges_in_cluster = subgraph.number_of_edges()
    num_connected_components = nx.number_connected_components(subgraph)

    # Compute Average Edge-Disjoint Paths
    avg_paths = calculate_edge_disjoint_paths(G, subgraph.nodes())

    # Compute additional metrics
    avg_paths_per_node = avg_paths / final_nodes if final_nodes > 0 else 0
    avg_paths_per_edge = avg_paths / num_edges_in_cluster if num_edges_in_cluster > 0 else 0
    graph_density = calculate_graph_density(subgraph)
    min_degree = calculate_min_degree(subgraph)

    # Compute standard min-cut (between first two nodes)
    if len(subgraph.nodes) >= 2:
        nodes_list = list(subgraph.nodes)
        s_standard = nodes_list[0]
        t_standard = nodes_list[1]
        cluster_1_std, cluster_2_std, mincut_value_std = compute_min_cut(subgraph.copy(), s_standard, t_standard)
    else:
        mincut_value_std = 0
        cluster_1_std = cluster_2_std = None

    # Compute degree-based min-cut (between min degree node and max degree node)
    if len(subgraph.nodes) >= 2:
        degrees = dict(subgraph.degree())
        min_degree_node = min(degrees, key=lambda x: degrees[x])
        max_degree_node = max(degrees, key=lambda x: degrees[x])
        # Avoid choosing the same node
        if min_degree_node == max_degree_node and len(subgraph.nodes) > 1:
            # Choose second max degree node
            sorted_degrees = sorted(degrees.items(), key=lambda x: x[1], reverse=True)
            if len(sorted_degrees) > 1:
                max_degree_node = sorted_degrees[1][0]
        cluster_1_deg, cluster_2_deg, mincut_value_deg = compute_min_cut(subgraph.copy(), min_degree_node, max_degree_node)
    else:
        mincut_value_deg = 0
        cluster_1_deg = cluster_2_deg = None

    # Print cluster information
    print(f"{indent}Cluster Size: {final_nodes}")
    print(f"{indent}Number of Edges in Cluster: {num_edges_in_cluster}")
    print(f"{indent}Number of Connected Components in Cluster: {num_connected_components}")
    print(f"{indent}Average Edge-Disjoint Paths: {avg_paths}")
    print(f"{indent}Average Edge-Disjoint Paths / Number of Nodes: {avg_paths_per_node}")
    print(f"{indent}Average Edge-Disjoint Paths / Number of Edges: {avg_paths_per_edge}")
    print(f"{indent}Graph Density: {graph_density:.4f}")
    print(f"{indent}Minimum Node Degree: {min_degree}")

    # Print Standard Min-Cut Results
    print(f"{indent}Standard Min-Cut Size: {mincut_value_std}")
    if cluster_1_std and cluster_2_std:
        print(f"{indent}Standard Min-Cut Cluster 1 Size: {len(cluster_1_std)}")
        print(f"{indent}Standard Min-Cut Cluster 2 Size: {len(cluster_2_std)}")
    else:
        print(f"{indent}Standard Min-Cut: Not applicable.")

    # Print Degree-Based Min-Cut Results
    print(f"{indent}Degree-Based Min-Cut Size: {mincut_value_deg}")
    if cluster_1_deg and cluster_2_deg:
        print(f"{indent}Degree-Based Min-Cut Cluster 1 Size: {len(cluster_1_deg)}")
        print(f"{indent}Degree-Based Min-Cut Cluster 2 Size: {len(cluster_2_deg)}")
    else:
        print(f"{indent}Degree-Based Min-Cut: Not applicable.")

    # Define thresholds
    log_n = math.log10(final_nodes) if final_nodes > 0 else 0
    density_threshold = 0.1  # Example threshold for graph density
    min_degree_threshold = 2  # Example threshold for minimum node degree

    # Check if cluster meets all criteria to be considered well connected
    if (avg_paths >= log_n and
        graph_density >= density_threshold and
        min_degree >= min_degree_threshold):
        print(f"{indent}Cluster is well connected based on multi-criteria.")
        return

    # If cluster is not well connected, recursively apply min-cuts to the standard min-cut subclusters
    if cluster_1_std and cluster_2_std:
        print(f"{indent}Proceeding with recursive min-cut based on Standard Min-Cut.")

        # Create subgraphs for the resulting clusters from standard min-cut
        subgraph_1_std = subgraph.subgraph(cluster_1_std).copy()
        subgraph_2_std = subgraph.subgraph(cluster_2_std).copy()

        # Recursively apply min-cut to the resulting subclusters
        recursive_min_cut(cluster_id, subgraph_1_std, G, depth + 1)
        recursive_min_cut(cluster_id, subgraph_2_std, G, depth + 1)
    else:
        print(f"{indent}Cannot perform further min-cut on this cluster.")

# Main Execution
def main():
    # Define the file paths
    network_file = "/scratch/users/md724/DataSets/wcc/test_network.tsv"
    clustering_file = "/scratch/users/md724/DataSets/wcc/clustering.tsv"

    # Step 1: Load the graph from test_network.tsv as an undirected graph
    G = nx.Graph()  # Undirected graph

    # Read the test_network.tsv file and add edges to the graph
    try:
        with open(network_file, 'r') as f:
            for line in f:
                parts = line.strip().split()
                if len(parts) != 2:
                    continue  # Skip malformed lines
                src, dst = map(int, parts)
                G.add_edge(src, dst)
    except FileNotFoundError:
        print(f"Error: File '{network_file}' not found.")
        return
    except Exception as e:
        print(f"Error reading '{network_file}': {e}")
        return

    # Add a default capacity of 1 to all edges in the graph
    for u, v in G.edges():
        G[u][v]['capacity'] = 1

    # Step 2: Load the clustering.tsv file and store the cluster information
    cluster_dict = {}

    try:
        with open(clustering_file, 'r') as f:
            for line in f:
                parts = line.strip().split()
                if len(parts) != 2:
                    continue  # Skip malformed lines
                node, cluster = map(int, parts)
                cluster_dict[node] = cluster
    except FileNotFoundError:
        print(f"Error: File '{clustering_file}' not found.")
        return
    except Exception as e:
        print(f"Error reading '{clustering_file}': {e}")
        return

    # Step 3: Assign cluster information to the nodes in the graph
    nx.set_node_attributes(G, cluster_dict, 'cluster')

    # Step 4: Print summary of the graph
    print("Graph loaded with", G.number_of_nodes(), "nodes and", G.number_of_edges(), "edges.")
    print("Example node attributes:")
    example_nodes = list(G.nodes())[:5]  # Show example nodes and their attributes
    for node in example_nodes:
        cluster = G.nodes[node].get('cluster', 'No Cluster')
        print(f"Node {node}: Cluster {cluster}")

    # Step 5: Group nodes by cluster
    clusters = {}
    for node, data in G.nodes(data=True):
        cluster_id = data.get('cluster')
        if cluster_id is None:
            continue  # Skip nodes without a cluster assignment
        if cluster_id not in clusters:
            clusters[cluster_id] = []
        clusters[cluster_id].append(node)

    # Step 6: Recursive min-cut process for each cluster
    for cluster_id, nodes in clusters.items():
        subgraph = G.subgraph(nodes).copy()
        recursive_min_cut(cluster_id, subgraph, G)

# triangle with a tail
def test_triangle_with_tail():
    # Create a graph representing a triangle with a tail
    G_triangle_with_tail = nx.Graph()

    # Add the triangle part (nodes 0, 1, 2 fully connected)
    G_triangle_with_tail.add_edges_from([(0, 1), (1, 2), (2, 0)])

    # Add the tail (a path starting from node 2)
    tail_nodes = [2, 3, 4, 5, 6]  # Adding a tail starting at node 2
    G_triangle_with_tail.add_edges_from([(tail_nodes[i], tail_nodes[i+1]) for i in range(len(tail_nodes) - 1)])

    # Assign a cluster ID (e.g., 999) to all nodes in this test graph
    cluster_id = 999
    cluster_nodes = list(G_triangle_with_tail.nodes())
    clusters = {cluster_id: cluster_nodes}

    print("\n--- Testing Triangle with a Tail ---")
    subgraph = G_triangle_with_tail.copy()
    recursive_min_cut(cluster_id, subgraph, G_triangle_with_tail)

if __name__ == "__main__":
    main()
    # Uncomment the following line to run the test for a triangle with a tail
    # test_triangle_with_tail()
