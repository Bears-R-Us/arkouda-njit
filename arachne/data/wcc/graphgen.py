import networkx as nx
import random

# Function to generate a graph with a large connected component and additional structures
def generate_graph_with_structures(output_network_file, output_cluster_file, 
                                   num_nodes=20000):
    G = nx.Graph()  # Initialize the graph
    clusters = {}   # Initialize clusters

    # --- Step 1: Create a large connected component (20000 nodes) ---
    #base_graph = nx.powerlaw_cluster_graph(num_nodes, m=5, p=0.1)
    base_graph = nx.erdos_renyi_graph(num_nodes, p=0.01)  # p is the edge probability

    G.add_nodes_from(base_graph.nodes())
    G.add_edges_from(base_graph.edges())
    clusters[0] = list(base_graph.nodes())  # Assign all nodes to cluster 0

    # --- Step 2: Add a lollipop graph ---
    lollipop_cluster_id = 1
    lollipop_nodes = list(range(num_nodes, num_nodes + 100))  # 100 nodes
    lollipop_graph = nx.lollipop_graph(m=50, n=50)  # Clique of 50, path of 50
    nx.relabel_nodes(lollipop_graph, mapping=dict(zip(range(100), lollipop_nodes)), copy=False)
    G.add_nodes_from(lollipop_graph.nodes())
    G.add_edges_from(lollipop_graph.edges())
    clusters[lollipop_cluster_id] = lollipop_nodes

    # --- Step 3: Add a wheel graph ---
    wheel_cluster_id = 2
    wheel_nodes = list(range(num_nodes + 100, num_nodes + 150))  # 50 nodes
    wheel_graph = nx.wheel_graph(len(wheel_nodes))
    nx.relabel_nodes(wheel_graph, mapping=dict(zip(range(len(wheel_nodes)), wheel_nodes)), copy=False)
    G.add_nodes_from(wheel_graph.nodes())
    G.add_edges_from(wheel_graph.edges())
    clusters[wheel_cluster_id] = wheel_nodes

    # --- Step 4: Add a grid graph ---
    grid_cluster_id = 3
    grid_side = 10  # 10x10 grid
    grid_nodes = list(range(num_nodes + 150, num_nodes + 250))  # 100 nodes
    grid_graph = nx.grid_2d_graph(grid_side, grid_side)
    nx.relabel_nodes(grid_graph, mapping=dict(zip(grid_graph.nodes(), grid_nodes)), copy=False)
    G.add_nodes_from(grid_graph.nodes())
    G.add_edges_from(grid_graph.edges())
    clusters[grid_cluster_id] = grid_nodes

    # --- Step 5: Add a two-dense-part structure ---
    dense_part_cluster_id = 4
    dense_part_nodes = list(range(num_nodes + 250, num_nodes + 350))  # 100 nodes
    dense_part_graph = nx.Graph()
    part1 = dense_part_nodes[:50]  # First dense part
    part2 = dense_part_nodes[50:]  # Second dense part
    dense_part_graph.add_edges_from((u, v) for u in part1 for v in part1 if u != v)
    dense_part_graph.add_edges_from((u, v) for u in part2 for v in part2 if u != v)
    # Connect the two dense parts with some bridge edges
    for _ in range(5):
        u = random.choice(part1)
        v = random.choice(part2)
        dense_part_graph.add_edge(u, v)
    G.add_nodes_from(dense_part_graph.nodes())
    G.add_edges_from(dense_part_graph.edges())
    clusters[dense_part_cluster_id] = dense_part_nodes

    # --- Write the graph to a file ---
    with open(output_network_file, 'w') as f:
        for src, dst in G.edges():
            f.write(f"{src}\t{dst}\n")

    # --- Write the clusters to a file ---
    with open(output_cluster_file, 'w') as f:
        for cluster_id, nodes in clusters.items():
            for node in nodes:
                f.write(f"{node}\t{cluster_id}\n")

    return G, clusters

# Main function
if __name__ == "__main__":
    # File paths
    network_file = "structured_network.tsv"
    cluster_file = "structured_clusters.tsv"

    # Generate graph with structured clusters
    G, clusters = generate_graph_with_structures(network_file, cluster_file, num_nodes=20000)

    print(f"Graph and clusters generated.")
    print(f"Network saved to {network_file}, clusters saved to {cluster_file}.")
