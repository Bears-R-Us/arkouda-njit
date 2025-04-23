import arkouda as ak
import arachne as ar
import scipy as sp
import networkx as nx
import matplotlib.pyplot as plt
import os
import time

ak.connect("n28", 5555)
p = 0.5
num_nodes = 10

seed = 42

# Define probabilities for labels and relationships
node_lbl_probs = {"lbls2": [1, 0.0],  # Probabilities for integers 10 and 11
                  "lbls3": [1, 0.0]}  # Probabilities for True and False
edge_rel_probs = {"rels1": [1, 0.0],  # Probabilities for integers 5 and 10
                  "rels2": [1, 0.0]}  # Probabilities for True and False


start = time.time()
temp_prop_graph = ar.gnp(num_nodes, p, create_using=ar.PropGraph, seed=seed)
end = time.time()
build_time = end - start

print(f"Building property graph with {len(temp_prop_graph)} vertices and "
      f"{temp_prop_graph.size()} "
      f"edges took {round(build_time,2)} seconds.")

### Generate node labels and edge relationships for the graph.
# 1. Extract node and edge information.
num_edges = temp_prop_graph.size()
num_nodes = len(temp_prop_graph)
edges = temp_prop_graph.edges()
nodes = temp_prop_graph.nodes()

##############################################
# Generate random node and edge attributes for the main graph
##############################################

# # For nodes:
# node_ints = ak.randint(10, 12, num_nodes, seed=seed)
# node_bools = ak.randint(0, 2, num_nodes, dtype=ak.bool, seed=seed)

# # For edges:
# edge_ints = ak.randint(10, 12, num_edges, seed=seed)

# For nodes
node_ints = ak.where(ak.randint(0, 100, num_nodes, seed=seed) < node_lbl_probs["lbls2"][0] * 100, 10, 11)
node_bools = ak.randint(0, 100, num_nodes, seed=seed) < node_lbl_probs["lbls3"][0] * 100

# For edges
edge_ints = ak.where(ak.randint(0, 100, num_edges, seed=seed) < edge_rel_probs["rels1"][0] * 100, 5, 10)
edge_bools = ak.randint(0, 100, num_edges, seed=seed) < edge_rel_probs["rels2"][0] * 100


# Create dataframes with the new attributes
edge_df = ak.DataFrame({
    "src": edges[0],
    "dst": edges[1],
    "rels1": edge_ints,
    "rels2": edge_bools
})

node_df = ak.DataFrame({
    "nodes": nodes,
    "lbls2": node_ints,
    "lbls3": node_bools
})

# Create the new property graph with these attributes
prop_graph = ar.PropGraph()
prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst")
prop_graph.load_node_attributes(node_df, node_column="nodes")
print("Property graph created with random node and edge attributes.")

##############################################
# Create the subgraph and assign random attributes
##############################################

# Subgraph structure
src_list = [2, 3, 1, 3]
dst_list = [3, 1, 2, 0]
src_subgraph = ak.array(src_list)
dst_subgraph = ak.array(dst_list)

subgraph_nodes = list(set(src_list) | set(dst_list))
subgraph_nodes.sort()

# Generate random node and edge attributes for the subgraph
num_subgraph_nodes = len(subgraph_nodes)
num_subgraph_edges = len(src_list)

# subgraph_node_ints = ak.randint(10, 12, num_subgraph_nodes, seed=seed)
# subgraph_node_bools = ak.randint(0, 2, num_subgraph_nodes, dtype=ak.bool, seed=seed)
# subgraph_edge_ints = ak.randint(10, 12, num_subgraph_edges, seed=seed)

# # Subgraph attributes
# subgraph_node_ints = ak.where(ak.randint(0, 100, num_subgraph_nodes, seed=seed) < node_lbl_probs["lbls2"][0] * 100, 10, 11)
# subgraph_node_bools = ak.randint(0, 100, num_subgraph_nodes, seed=seed) < node_lbl_probs["lbls3"][0] * 100

# subgraph_edge_ints = ak.where(ak.randint(0, 100, num_subgraph_edges, seed=seed) < edge_rel_probs["rels1"][0] * 100, 5, 10)
# subgraph_edge_bools = ak.randint(0, 100, num_subgraph_edges, seed=seed) < edge_rel_probs["rels2"][0] * 100

# Fixed attributes
subgraph_node_ints = ak.array([10, 10, 10, 10])
subgraph_node_bools = ak.array([True, True, True, True])
subgraph_edge_ints = ak.array([5, 5, 5, 5])
subgraph_edge_bools = ak.array([True, True, True, True])

# Create dataframes for subgraph attributes
edge_df_h = ak.DataFrame({
    "src": src_subgraph,
    "dst": dst_subgraph,
    "rels1": subgraph_edge_ints,
    "rels2": subgraph_edge_bools
})

node_df_h = ak.DataFrame({
    "nodes": ak.array(subgraph_nodes),
    "lbls2": subgraph_node_ints,
    "lbls3": subgraph_node_bools
})

# Create the subgraph with these attributes
sg = ar.PropGraph()
sg.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst")
sg.load_node_attributes(node_df_h, node_column="nodes")



print("Subgraph created with random node and edge attributes.")
import numpy as np

# Copy the main graph node dataframe
original_node_df = node_df.copy()
print("Original node dataframe copied.")

# Perform subgraph isomorphism search
isos_as_vertices = ar.subgraph_isomorphism(
    prop_graph, sg,
    semantic_check="and", algorithm_type="ps",
    reorder_type=None, return_isos_as="vertices"
)

# Calculate the number of isomorphisms found
num_isos = len(isos_as_vertices[0]) // len(src_subgraph)
print(f"We found {num_isos} monos inside of the graph")

if num_isos == 0:
    print("No isomorphisms found. Exiting.")
else:
    # Display the node dataframe before changes
    print("\nNode dataframe before changes:")
    print(node_df)

    # Pick 1% of isomorphisms randomly
    num_to_modify = max(1, int(0.01 * num_isos))  # Ensure at least 1 isomorphism is modified
    selected_indices = np.random.choice(range(num_isos), size=num_to_modify, replace=False)

    print(f"\nSelected isomorphism indices: {selected_indices}")

    # Fixed attributes for the subgraph
    new_node_ints = ak.array([20, 30, 40, 50])
    new_node_bools = ak.array([True, True, True, True])

    for iso_idx in selected_indices:
        # Get nodes corresponding to this isomorphism
        iso_nodes = isos_as_vertices[0].to_ndarray()  # Convert to NumPy array
        iso_nodes_for_iso = iso_nodes[iso_idx * len(src_subgraph):(iso_idx + 1) * len(src_subgraph)]

        iso_mapping = {subgraph_idx: iso_node for subgraph_idx, iso_node in enumerate(iso_nodes_for_iso)}

        print(f"\nProcessing Isomorphism {iso_idx}:")
        print(f"Subgraph to Main Graph Mapping: {iso_mapping}")

        # Update node attributes
        for subgraph_idx, iso_node in iso_mapping.items():
            old_int = node_df["lbls2"][iso_node]
            old_bool = node_df["lbls3"][iso_node]

            # Assign new attributes
            node_df["lbls2"][iso_node] = new_node_ints[subgraph_idx]
            node_df["lbls3"][iso_node] = new_node_bools[subgraph_idx]

            print(f"Updated node {iso_node}: lbls2 {old_int} -> {new_node_ints[subgraph_idx]}, "
                  f"lbls3 {old_bool} -> {new_node_bools[subgraph_idx]}")

    # Display the node dataframe after changes
    print("\nNode dataframe after changes:")
    print(node_df)

    # Reload the graph with updated attributes
    edge_df = ak.DataFrame({
        "src": edges[0],
        "dst": edges[1],
        "rels1": edge_ints,
        "rels2": edge_bools
    })

    updated_node_df = ak.DataFrame({
        "nodes": nodes,
        "lbls2": node_df["lbls2"],
        "lbls3": node_df["lbls3"]
    })

    prop_graph = ar.PropGraph()
    prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst")
    prop_graph.load_node_attributes(updated_node_df, node_column="nodes")

    print("Property graph reloaded with updated node and edge attributes.")
    subgraph_node_ints = ak.array([20, 30, 40, 50])
subgraph_node_bools = ak.array([True, True, True, True])
subgraph_edge_ints = ak.array([5, 5, 5, 5])
subgraph_edge_bools = ak.array([True, True, True, True])

# Create dataframes for subgraph attributes
edge_df_h = ak.DataFrame({
    "src": src_subgraph,
    "dst": dst_subgraph,
    "rels1": subgraph_edge_ints,
    "rels2": subgraph_edge_bools
})

node_df_h = ak.DataFrame({
    "nodes": ak.array(subgraph_nodes),
    "lbls2": subgraph_node_ints,
    "lbls3": subgraph_node_bools
})

# Create the subgraph with these attributes
sg = ar.PropGraph()
sg.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst")
sg.load_node_attributes(node_df_h, node_column="nodes")



print("Subgraph created with random node and edge attributes.")
"""VF2-SI """
isos_as_vertices = ar.subgraph_isomorphism(prop_graph, sg, 
                                           semantic_check = "and", algorithm_type = "si",
                                           reorder_type = "structural", return_isos_as = "vertices")

print(f"We found {len(isos_as_vertices[0])/len(sg)} monos inside of the graph")
print(isos_as_vertices[0])