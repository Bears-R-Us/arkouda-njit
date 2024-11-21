import networkx as nx

# Function to analyze the graph and calculate various metrics for each cluster
def analyze_graph_clusters(G, clusters):
    print("\n--- Analyzing Graph and Clusters ---")
    for cluster_id, nodes in clusters.items():
        print(f"\n--- Analysis for Cluster {cluster_id} ---")
        subgraph = G.subgraph(nodes)

        # Ensure subgraph is non-empty
        if len(subgraph.nodes()) == 0:
            print(f"Cluster {cluster_id} is empty.")
            continue

        # Calculate basic metrics
        internal_edges = subgraph.number_of_edges()
        max_possible_edges = len(subgraph.nodes()) * (len(subgraph.nodes()) - 1) // 2
        density = nx.density(subgraph)
        sparsity = 1 - density

        print(f"Cluster Size: {len(subgraph.nodes())}")
        print(f"Internal Edges: {internal_edges}")
        print(f"Max Possible Edges: {max_possible_edges}")
        print(f"Density: {density:.6f}")
        print(f"Sparsity: {sparsity:.6f}")

        # Triangle count
        triangles = nx.triangles(subgraph)
        total_triangles = sum(triangles.values()) // 3
        print(f"Total Triangles: {total_triangles}")

        # Clustering coefficients
        global_clustering = nx.transitivity(subgraph)
        avg_local_clustering = nx.average_clustering(subgraph)
        print(f"Global Clustering Coefficient: {global_clustering:.4f}")
        print(f"Average Local Clustering Coefficient: {avg_local_clustering:.4f}")

        # Core decomposition
        core_numbers = nx.core_number(subgraph)
        max_core_number = max(core_numbers.values())
        max_core_nodes = [node for node, core in core_numbers.items() if core == max_core_number]
        max_core_subgraph = subgraph.subgraph(max_core_nodes)
        max_core_size = max_core_subgraph.number_of_nodes()
        max_core_density = nx.density(max_core_subgraph) if max_core_size > 1 else 0.0

        print(f"Max Core Number: {max_core_number}")
        print(f"Max Core Size: {max_core_size}")
        print(f"Max Core Density: {max_core_density:.4f}")

        # Betweenness centrality
        betweenness = nx.betweenness_centrality(subgraph, normalized=True)
        max_betweenness = max(betweenness.values()) if betweenness else 0.0
        avg_betweenness = sum(betweenness.values()) / len(betweenness) if betweenness else 0.0
        print(f"Max Betweenness: {max_betweenness:.4f}")
        print(f"Average Betweenness: {avg_betweenness:.4f}")

        # Diameter
        if nx.is_connected(subgraph):
            diameter = nx.diameter(subgraph)
            print(f"Diameter: {diameter}")
        else:
            print(f"Diameter: Undefined (Cluster is disconnected)")

# Function to load a graph from a TSV file
# Function to load a graph from a TSV file
def load_graph(file_path):
    G = nx.Graph()
    with open(file_path, 'r') as f:
        for line in f:
            parts = line.strip().split('\t')
            if len(parts) == 2:  # Ensure the line has exactly two values
                src, dst = map(int, parts)
                G.add_edge(src, dst)
    return G


# Function to load clusters from a TSV file
def load_clusters(file_path):
    clusters = {}
    with open(file_path, 'r') as f:
        for line in f:
            parts = line.strip().split('\t')
            if len(parts) == 2:  # Ensure the line has exactly two values
                node, cluster_id = map(int, parts)
                if cluster_id not in clusters:
                    clusters[cluster_id] = []
                clusters[cluster_id].append(node)
            else:
                print(f"Skipping malformed line: {line.strip()}")
    return clusters


# Main function
if __name__ == "__main__":
    # File paths
    network_file = "test_network_simple_5.tsv"
    cluster_file = "test_clustering_simple_5.tsv"

    # Load graph and clusters
    G = load_graph(network_file)
    clusters = load_clusters(cluster_file)

    # Analyze clusters
    analyze_graph_clusters(G, clusters)
