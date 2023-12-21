import networkx as nx
import random

# Create a random directed graph with nodes in the range 100 to 200
random.seed(42)  # Setting seed for reproducibility
num_nodes = random.randint(100, 120)
random_directed_graph = nx.DiGraph()

# Add nodes to the graph
random_directed_graph.add_nodes_from(range(num_nodes))

# Add directed edges with random weights
for i in range(num_nodes):
    for j in range(num_nodes):
        if random.random() < 0.009:  # Adjust the probability for edge creation
            random_directed_graph.add_edge(i, j, weight=random.random())

# Set node labels and edge labels
nx.set_node_attributes(random_directed_graph, 'label', 'label1')
nx.set_edge_attributes(random_directed_graph, 'label', 'Y1')




# Extracting src and dst arrays from random_directed_graph
edges = random_directed_graph.edges()
src = [edge[0] for edge in edges]
dst = [edge[1] for edge in edges]

# Extracting all_nodes array
vertex_ids = list(random_directed_graph.nodes())
vertex_labels = ['label1'] * len(vertex_ids)
edge_relationships = ['Y1'] * len(vertex_ids)


# Printing src, dst, and all_nodes arrays
print("src:", src)
print("dst:", dst)
print("vertex_ids:", vertex_ids)

print("vertex_labels:", vertex_labels)



# Create the subgraph
subgraph_nodes = [0, 1, 2, 3]
subgraph_edges = [(0, 1), (1, 2), (2, 0), (1, 3)]
subgraph = nx.DiGraph()
subgraph.add_nodes_from(subgraph_nodes)
subgraph.add_edges_from(subgraph_edges)

# Use DiGraphMatcher to find subgraph isomorphisms
matcher = nx.algorithms.isomorphism.DiGraphMatcher(random_directed_graph, subgraph)
subgraph_isomorphisms = list(matcher.subgraph_monomorphisms_iter())
# Print the number of occurrences and mappings of the subgraph in the random graph
print("Number of occurrences of the subgraph within the random directed graph:", len(subgraph_isomorphisms))
print("Subgraph occurrences found:")
for iso_mapping in subgraph_isomorphisms:
    print("Isomorphism mapping:", iso_mapping)
    