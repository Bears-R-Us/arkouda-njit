import networkx as nx

# Define the src and dst lists as multi-line strings
src_str = """
0 0 0 1 1 2 2 2 2 2 2 2 3 3 4 4 5 5 5 5 5 5 6 6 6 7 7 8 8 8 8 8 8 8 8 8 8 8 8 8 9 9 9 10 10 11 11 12 12 12 13 13 13 13 13 13 13 13 13 13 14 14 14 14 15 15 15 15 16 16 16 16 17 17 17 17 17 18 18 18 19 19 20 20 20 21 21 22 22 23 23 24 24 24 25 25 25 25 25 25 25 25 25 25 25 25 25 25 25 26 26 26 26 26 26 26 26 27 27 27 27 27 27 27 27 27 27 28 28 28 28 28 29 29 29 29 30 30 30 31 31 31 32 32 32 32 32 32 32 32 33 33 33 33 33 33 33 33 33 33 33 33 33 33 33 34 34 34 34 34 34 34 34 34 34 34 35 35 35 35 35 35 35 35 35 35 35 35 35 36 36 36 36 36 36 36 36 36 36 36 36 36 36 36 36 36 37 37 37 37 38 38 38 38 38 38 38 38 38 39 39 39
"""

dst_str = """
15 33 36 19 22 5 8 17 20 33 36 37 25 29 33 36 2 6 16 33 35 36 5 33 36 23 28 2 13 17 25 26 27 32 33 34 35 36 37 38 18 31 34 25 28 25 29 33 35 36 8 14 24 25 26 27 32 34 35 38 13 25 27 38 0 21 33 36 5 33 35 36 2 8 33 36 37 9 31 34 1 22 2 33 36 15 36 1 19 7 28 13 25 27 3 8 10 11 13 14 24 26 27 28 29 32 34 35 38 8 13 25 27 32 34 35 38 8 13 14 24 25 26 32 34 35 38 7 10 23 25 29 3 11 25 28 33 36 39 9 18 34 8 13 25 26 27 34 35 38 0 2 4 5 6 8 12 15 16 17 20 30 35 36 39 8 9 13 18 25 26 27 31 32 35 38 5 8 12 13 16 25 26 27 32 33 34 36 38 0 2 4 5 6 8 12 15 16 17 20 21 30 33 35 37 39 2 8 17 36 8 13 14 25 26 27 32 34 35 30 33 36
"""

def parse_edge_list(edge_str):
    """Parse a space-separated string of integers into a list."""
    return list(map(int, edge_str.strip().split()))

def main():
    # Parse the src and dst lists
    src = parse_edge_list(src_str)
    dst = parse_edge_list(dst_str)

    # Ensure both lists have the same length
    if len(src) != len(dst):
        print("Error: 'src' and 'dst' lists must have the same number of elements.")
        return

    # Create an undirected graph
    G = nx.Graph()

    # Add edges to the graph
    edges = zip(src, dst)
    G.add_edges_from(edges)

    # Optionally, add isolated nodes (nodes without edges)
    # Find all unique nodes in src and dst
    nodes_in_edges = set(src) | set(dst)
    all_nodes = set(src) | set(dst)
    # If you have nodes that are completely isolated (no edges), you can add them here
    # For example:
    # isolated_nodes = {0, 1, 2, ..., N}
    # G.add_nodes_from(isolated_nodes - nodes_in_edges)

    # Determine if the graph is connected
    if nx.is_connected(G):
        print("The graph is connected.")
    else:
        num_cc = nx.number_connected_components(G)
        print(f"The graph is not connected and has {num_cc} connected components.\n")

        # Get all connected components
        connected_components = list(nx.connected_components(G))

        # Print each connected component with its nodes
        for idx, component in enumerate(connected_components, 1):
            sorted_component = sorted(component)
            print(f"Connected Component {idx} ({len(sorted_component)} nodes):")
            print(sorted_component)
            print()  # For better readability

if __name__ == "__main__":
    main()
