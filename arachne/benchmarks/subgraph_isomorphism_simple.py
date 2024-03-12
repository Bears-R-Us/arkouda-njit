"""Script to run subgraph isomorphism for H01 dataset."""
import time

import arachne as ar
import arkouda as ak

ak.connect("n118", 5555)
graph = ar.PropGraph()
graph = ar.PropGraph()
src_graph = ak.array([1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 7, 7, 8, 8, 9])
dst_graph = ak.array([0, 3, 1, 4, 4, 7, 0, 1, 5, 8, 2, 9, 4, 6, 5, 7, 8])
lbls_graph = ak.array(["1", "1", "1","1", "1", "1","1", "1", "1", "1"])
rels_graph = ak.array(["1", "1", "1","1", "1", "1","1", "1", "1","1", "1", "1","1", "1", "1", "1", "1"])
edge_df_g = ak.DataFrame({"src":src_graph, "dst":dst_graph, "rels":rels_graph})
node_df_g = ak.DataFrame({"nodes": ak.arange(0,10), "lbls":lbls_graph})
graph.load_edge_attributes(edge_df_g, source_column="src", destination_column="dst",
                                relationship_columns=["rels"])
graph.load_node_attributes(node_df_g, node_column="nodes", label_columns=["lbls"])
####################################

subgraph = ar.PropGraph()
src_subgraph = ak.array([0, 1, 1, 0])
dst_subgraph = ak.array([1, 2, 3, 2])
lbls_subgraph = ak.array(["1", "1", "1", "1"])
rels_subgraph = ak.array(["1", "1", "1", "1"])
edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph, "rels":rels_subgraph})
node_df_h = ak.DataFrame({"nodes": ak.arange(0,4), "lbls":lbls_subgraph})
subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                relationship_columns=["rels"])
subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls"])
print("Calling Arachne....")
start = time.time()
isos = ar.subgraph_isomorphism(graph, subgraph)
end = time.time()
print(f"Finding {len(isos)/4} monomorphisms took {end-start} secs")
print("isos = ", isos)