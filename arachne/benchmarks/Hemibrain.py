import arkouda as ak
import arachne as ar
import pandas as pd
import time as time
import networkx as nx
import random
import argparse
import numpy as np

ak.connect("n82", 5555)

### Get Arkouda server configuration information.
config = ak.get_config()
num_locales = config["numLocales"]
num_pus = config["numPUs"]
print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")



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

node_lbls2 = ak.array([10] * num_nodes)  # lbls2 set to 10
node_lbls3 = ak.array([True] * num_nodes)  # lbls3 set to True
edge_rels1 = ak.array([5] * num_edges)  # rels1 set to 5
edge_rels2 = ak.array([True] * num_edges)  # rels2 set to True

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

src_list = [0, 1, 1, 0]
dst_list = [1, 0, 2, 2]
src_subgraph = ak.array(src_list)
dst_subgraph = ak.array(dst_list)

subgraph_nodes = list(set(src_list) | set(dst_list))
subgraph_nodes.sort()

# Generate random node and edge attributes for the subgraph
num_subgraph_nodes = len(subgraph_nodes)
num_subgraph_edges = len(src_list)

subgraph_node_ints = ak.array([10]*num_subgraph_nodes)
subgraph_node_bools = ak.array([True]*num_subgraph_nodes)
subgraph_edge_ints = ak.array([5]*num_subgraph_edges)
subgraph_edge_bools = ak.array([True]*num_subgraph_edges)

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



print(" running Arachne....")


# """VF2-SI """
# isos_as_vertices = ar.subgraph_isomorphism(prop_graph, subgraph, 
#                                            semantic_check = "and", algorithm_type = "si",
#                                            reorder_type = "structural", return_isos_as = "vertices")

# print(f"We found {len(isos_as_vertices[0])/len(subgraph)} monos inside of the graph")

# """VF2-PS DEFAULT"""
# isos_as_vertices = ar.subgraph_isomorphism(prop_graph, subgraph, 
#                                            semantic_check = "and", algorithm_type = "ps", 
#                                            reorder_type = None, return_isos_as = "vertices")

# print(f"We found {len(isos_as_vertices[0])/len(subgraph)} monos inside of the graph")
# #print(isos_as_vertices)

# Run VF2-SI and VF2-PS DEFAULT 3 times each, printing times and results
def run_vf2_test(algorithm_type):
    times = []
    isos_count = []

    for i in range(3):
        start_time = time.time()
        isos_as_vertices = ar.subgraph_isomorphism(
            prop_graph, subgraph,
            # semantic_check="and", algorithm_type=algorithm_type,
            # reorder_type="structural" if algorithm_type == "si" else None,
            # return_isos_as="vertices"
            semantic_check = "and", algorithm_type = "ps", 
            reorder_type = None, return_isos_as = "vertices"
        )
        end_time = time.time()

        isos_count.append(len(isos_as_vertices[0]))
        times.append(end_time - start_time)
        print(f"We found {len(isos_as_vertices[0])/len(subgraph)} monos inside of the graph")
        print(f"Run {i+1} - {algorithm_type} Isomorphisms: {len(isos_as_vertices[0])/len(subgraph)}, Time: {round(end_time - start_time, 2)} seconds")

    # avg_isos = np.mean(isos_count)
    # avg_time = np.mean(times)

    # print(f"\nAverage {algorithm_type} Isomorphisms: {avg_isos}")
    # print(f"Average {algorithm_type} Time: {round(avg_time, 2)} seconds")

# Running the tests
print("\nRunning VF2-SI...")
run_vf2_test("si")

print("\nRunning VF2-PS DEFAULT...")
run_vf2_test("ps")