"""Script to run subgraph isomorphism for H01 dataset."""
import time

import arachne as ar
import arkouda as ak

ak.connect("n83", 5555)

start = time.time()
connectome_links = ak.read("/scratch/users/oaa9/testing_files/data/connectome/edges*")
connectome_links = ak.DataFrame(connectome_links)
new_types = ak.cast(connectome_links["type_label"], str)
connectome_links["type_label"] = new_types
end = time.time()
print(f"Loading in connectome edge HDF5 data with {len(connectome_links)} rows took "
      f"{end-start} secs")

start = time.time()
connectome_nodes = ak.read("/scratch/users/oaa9/testing_files/data/connectome/nodes*")
connectome_nodes = ak.DataFrame(connectome_nodes)
new_node_types = ak.cast(connectome_nodes["node_type_label"], str)
connectome_nodes["node_type_label"] = new_node_types
end = time.time()
print(f"Loading in connectome node HDF5 data with {len(connectome_nodes)} rows took "
      f"{end-start} secs")

graph = ar.PropGraph()
start = time.time()
graph.load_edge_attributes(connectome_links,
                           source_column="src_neuron_id",
                           destination_column="dst_neuron_id",
                           relationship_columns=["type_label"]
                        )
end = time.time()
print(f"Building graph from edge attributes took {end-start} secs")

start = time.time()
graph.load_node_attributes(connectome_nodes,
                           node_column="neuron_id",
                           label_columns=["node_type_label"]
                        )
end = time.time()
print(f"Loading in node attributes took {end-start} secs")

del connectome_nodes
del connectome_links

subgraph = ar.PropGraph()
src_subgraph = ak.array([2, 1, 0])
dst_subgraph = ak.array([1, 0, 2])
lbls_subgraph = ak.array(["1", "1", "1"])
rels_subgraph = ak.array(["1", "1", "1"])
edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph, "rels":rels_subgraph})
node_df_h = ak.DataFrame({"nodes": ak.arange(0,3), "lbls":lbls_subgraph})
subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                relationship_columns=["rels"])
subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls"])
print("Calling Arachne....")
start = time.time()
isos = ar.subgraph_isomorphism(graph, subgraph)
end = time.time()
print(f"Finding {len(isos)/3} monomorphisms took {end-start} secs")