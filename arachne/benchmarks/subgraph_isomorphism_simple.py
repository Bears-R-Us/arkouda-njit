"""Script to run subgraph isomorphism for H01 dataset."""
import time

import arachne as ar
import arkouda as ak
import networkx as nx

ak.connect("n117", 5555)
graph = ar.PropGraph()
graph = ar.PropGraph()
src_graph = ak.array([1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 7, 7, 8, 8, 9, 5 , 5])
dst_graph = ak.array([0, 3, 1, 4, 4, 7, 0, 1, 5, 8, 2, 9, 4, 6, 5, 7, 8, 10, 11])
lbls_graph = ak.array(["1", "1", "1","1", "1", "1","1", "1", "1", "1", "1", "1"])
rels_graph = ak.array(["1", "1", "1","1", "1", "1","1", "1", "1","1", "1", "1","1", "1", "1", "1", "1", "1", "1"])
edge_df_g = ak.DataFrame({"src":src_graph, "dst":dst_graph, "rels":rels_graph})
node_df_g = ak.DataFrame({"nodes": ak.arange(0,12), "lbls":lbls_graph})
graph.load_edge_attributes(edge_df_g, source_column="src", destination_column="dst",
                                relationship_columns=["rels"])
graph.load_node_attributes(node_df_g, node_column="nodes", label_columns=["lbls"])
####################################

subgraph = ar.PropGraph()
src_subgraph = ak.array([0, 1, 1, 2])
dst_subgraph = ak.array([1, 3, 2, 0])
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

G = nx.DiGraph()
H = nx.DiGraph()

# Clearing graphs (optional in this context)
G.clear()
H.clear()

# Adding nodes and edges to directed graphs
G.add_nodes_from(range(0, 30))
G.add_edges_from([(3, 0), (1, 3), (4, 1), (2, 4), (5, 2), (3, 4), (4, 5),
                      (3, 7), (7, 6), (4, 8), (5, 9), (1, 0), (2, 1), (8, 7), (7,4), (8, 5), (9,8), (5, 10),(5, 11)])

H.add_nodes_from(range(0, 4))
H.add_edges_from([(0, 1), (1, 3 ), (1, 2), (2, 0)])

NODE_LABEL = 'NodeLabel'
EDGE_LABEL = 'EdgeLabel'
nx.set_node_attributes(G, NODE_LABEL, 'label1')
nx.set_edge_attributes(G, EDGE_LABEL, 'Y1')

nx.set_node_attributes(H, NODE_LABEL, 'label1')
nx.set_edge_attributes(H, EDGE_LABEL, 'Y1')

# Measure execution time.
start_time = time.time()

# Find subgraph isomorphisms of H in G.
GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)

# List of dicts. For each dict, keys is original graph vertex, values are subgraph vertices.
subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())

elapsed_time = time.time() - start_time
print(f"NetworkX execution time: {elapsed_time} seconds")
print(f"NetworkX found: {len(subgraph_isomorphisms)} isos")

for iso in subgraph_isomorphisms:
    print(iso)

ak.shutdown()