# %%
import arkouda as ak
import arachne as ar
import pandas as pd
import time as time
import networkx as nx
import random
import argparse

ak.connect("n81", 5555)

### Get Arkouda server configuration information.
config = ak.get_config()
num_locales = config["numLocales"]
num_pus = config["numPUs"]
print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")

# Probabilities for node and edge attributes
P_Alpha = 0.6
P_Beta = 0.4
node_lbl_probs = {
    "lbls2": [P_Alpha, P_Beta],  # Probabilities for integers 10 and 11
    "lbls3": [P_Alpha, P_Beta]   # Probabilities for True and False
}
edge_rel_probs = {
    "rels1": [P_Alpha, P_Beta],  # Probabilities for integers 5 and 6
    "rels2": [P_Alpha, P_Beta]   # Probabilities for True and False
}
    
# with all 0.8, 0.2 and subgraph 11 and False and 6 and False we have 1 ISO

hemibrain_traced_roi_connections = pd.read_csv("/scratch/users/oaa9/experimentation/data/connectome/hemibrain/exported-traced-adjacencies-v1.2/traced-roi-connections.csv")
# hemibrain_traced_roi_connections
# hemibrain_traced_roi_connections['type'] = 'T1'
# hemibrain_traced_roi_connections

neuron_dfs_in_pandas = [hemibrain_traced_roi_connections]
neuron_dfs_in_arkouda = [ak.DataFrame(pd_df) for pd_df in neuron_dfs_in_pandas]

ak_hemibrain_traced_roi_connections = neuron_dfs_in_arkouda[0]

ak_hemibrain_traced_roi_connections_gb = ak_hemibrain_traced_roi_connections.groupby(["bodyId_pre", "bodyId_post"])
ak_hemibrain_traced_roi_connections_sorted = ak_hemibrain_traced_roi_connections[ak_hemibrain_traced_roi_connections_gb.permutation[ak_hemibrain_traced_roi_connections_gb.segments]]
#ak_hemibrain_traced_roi_connections_sorted

  

ak_hemibrain_traced_roi_connections_sorted['src'] = ak_hemibrain_traced_roi_connections_sorted['bodyId_pre']
del ak_hemibrain_traced_roi_connections_sorted['bodyId_pre']  # Remove the original column

ak_hemibrain_traced_roi_connections_sorted['dst'] = ak_hemibrain_traced_roi_connections_sorted['bodyId_post']
del ak_hemibrain_traced_roi_connections_sorted['bodyId_post']  # Remove the original column

print(ak_hemibrain_traced_roi_connections_sorted.columns)

# Collect all unique nodes from src and dst
src_list = ak_hemibrain_traced_roi_connections_sorted['src'].to_ndarray().tolist()
dst_list = ak_hemibrain_traced_roi_connections_sorted['dst'].to_ndarray().tolist()
all_nodes = list(set(src_list) | set(dst_list))
all_nodes.sort()

# Generate attributes
num_nodes = len(all_nodes)
num_edges = len(src_list)

seed = 42
# node_lbls2 = ak.array([10] * num_nodes)  # lbls2 set to 10
# node_lbls3 = ak.array([True] * num_nodes)  # lbls3 set to True
# edge_rels1 = ak.array([5] * num_edges)  # rels1 set to 5
# edge_rels2 = ak.array([True] * num_edges)  # rels2 set to True

# Randomly generate node attributes
node_lbls2 = ak.where(
        ak.randint(0, 100, num_nodes) < node_lbl_probs["lbls2"][0] * 100, 10, 11
)
node_lbls3 = ak.randint(0, 100, num_nodes) < node_lbl_probs["lbls3"][0] * 100

# Randomly generate edge attributes
edge_rels1 = ak.where(
    ak.randint(0, 100, num_edges) < edge_rel_probs["rels1"][0] * 100, 5, 6
)
edge_rels2 = ak.randint(0, 100, num_edges) < edge_rel_probs["rels2"][0] * 100


# Create dataframes
edge_df = ak.DataFrame({
    "src": ak.array(src_list),
    "dst": ak.array(dst_list),
    "rels1": edge_rels1,
    "rels2": edge_rels2
})

node_df = ak.DataFrame({
    "nodes": ak.array(all_nodes),
    "lbls2": node_lbls2,
    "lbls3": node_lbls3
})

# Create the property graph
prop_graph = ar.PropGraph()
prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst")
prop_graph.load_node_attributes(node_df, node_column="nodes")

print("Property graph created with fixed node (lbls2=10, lbls3=True) and edge attributes (rels1=5, rels2=True).")


print("Data loaded now we are loading the subraph....")




# %%
src_list = [1, 1]
dst_list = [0, 2]
src_subgraph = ak.array(src_list)
dst_subgraph = ak.array(dst_list)

subgraph_nodes = list(set(src_list) | set(dst_list))
subgraph_nodes.sort()

# Generate random node and edge attributes for the subgraph
num_subgraph_nodes = len(subgraph_nodes)
num_subgraph_edges = len(src_list)

subgraph_node_ints = ak.array([11]*num_subgraph_nodes)
subgraph_node_bools = ak.array([False]*num_subgraph_nodes)
subgraph_edge_ints = ak.array([6]*num_subgraph_edges)
subgraph_edge_bools = ak.array([False]*num_subgraph_edges)

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
subgraph = ar.PropGraph()
subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst")
subgraph.load_node_attributes(node_df_h, node_column="nodes")



print("Subgraph created with fixed node and edge attributes.")
print(" Run Arachne....")

# %%
"""VF2-SI """
start_time = time.time()

isos_as_vertices = ar.subgraph_isomorphism(prop_graph, subgraph, 
                                           semantic_check = "and", algorithm_type = "si",
                                           reorder_type = "structural", return_isos_as = "vertices")

print(f"We found {len(isos_as_vertices[0])/len(subgraph)} monos inside of the graph")
# Stop the timer
end_time = time.time()

# Calculate elapsed time
elapsed_time = end_time - start_time

# Print results
num_monos = len(isos_as_vertices[0]) / len(subgraph) if len(subgraph) > 0 else 0
print(f"VF2-SI completed in {elapsed_time:.4f} seconds.")
print(f"We found {num_monos} monos inside of the graph.")


def save_graph_to_csv(graph, file_name):
    """
    Save a graph in CSV format with directed edges and optional labels.
    :param graph: Arachne property graph.
    :param file_name: Output CSV file name.
    """
    # Extract internal edges and attributes
    internal_src, internal_dst = graph._internal_edges()
    src = internal_src.to_list()
    dst = internal_dst.to_list()

    # print("src = ", src)
    # print("dst = ", dst)
    # Extract edge attributes.
    graph_edge_attributes = graph.get_edge_attributes()
    edge_df = graph_edge_attributes.to_pandas()
    edge_rels1 = edge_df['rels1'] if 'rels1' in edge_df.columns else None
    edge_rels2 = edge_df['rels2'] if 'rels2' in edge_df.columns else None
    
    print("HERE HERE 1")
    # Generate edge data
    edge_data = []
    for i in range(len(src)):
        if edge_rels1 is not None and edge_rels2 is not None:
            edge_data.append(f"{src[i]}>{dst[i]},{edge_rels1[i]},{edge_rels2[i]}")
        else:
            edge_data.append(f"{src[i]}>{dst[i]}")

    print("Preparing node data...")
    graph_node_attributes = graph.get_node_attributes()
    if graph_node_attributes.size > 0:
        node_df = graph_node_attributes.to_pandas()
        node_data = [
            f"{index},,{row['lbls2']},{row['lbls3']}"
            for index, row in node_df.iterrows()
        ]
    else:
        # Use default labels if no node attributes are available
        unique_nodes = sorted(set(src).union(dst))
        node_data = [f"{node},," for node in unique_nodes]

    print(" Write to CSV")

    # Write to CSV
    with open(file_name, "w") as f:
        # f.write("\n".join(edge_data + node_data))
        # f.write("\n".join(edge_data))
        f.write("\n".join(edge_data) + "\n")
        f.write("\n".join(node_data) + "\n")

    print(f"Graph saved to {file_name}")
    
# # Save the main graph to a CSV file
print("Processing main graph...")
save_graph_to_csv(prop_graph, "main_graph_Hemi-1.csv")
print("Main graph saved ")

# Save the main graph to a CSV file
print("Processing subgraph...")
save_graph_to_csv(subgraph, "Hemi-1.csv")
print("subgraph saved  ....")


"""VF2-SI PROBABILITY-MVE"""
print("Running VF2-SI PROBABILITY-MVE...")
start_time = time.time()

isos_as_vertices = ar.subgraph_isomorphism(
    prop_graph, subgraph,
    semantic_check="and", algorithm_type="si",
    reorder_type="probability", return_isos_as="vertices"
)

end_time = time.time()
elapsed_time = end_time - start_time

num_monos = len(isos_as_vertices[0]) / len(subgraph) if len(subgraph) > 0 else 0
print(f"VF2-SI PROBABILITY-MVE completed in {elapsed_time:.4f} seconds.")
print(f"We found {num_monos} monos inside of the graph.")


"""VF2-PS DEFAULT"""
print("Running VF2-PS DEFAULT...")
start_time = time.time()

isos_as_vertices = ar.subgraph_isomorphism(
    prop_graph, subgraph,
    semantic_check="and", algorithm_type="ps",
    reorder_type=None, return_isos_as="vertices"
)

end_time = time.time()
elapsed_time = end_time - start_time

num_monos = len(isos_as_vertices[0]) / len(subgraph) if len(subgraph) > 0 else 0
print(f"VF2-PS DEFAULT completed in {elapsed_time:.4f} seconds.")
print(f"We found {num_monos} monos inside of the graph.")
ak.shutdown()

