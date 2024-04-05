import arkouda as ak
import arachne as ar
import pandas as pd
import time as time
import networkx as nx
import random

from dotmotif import Motif, GrandIsoExecutor 

ak.connect("n115", 5555)

microns = pd.read_csv("/scratch/users/oaa9/experimentation/data/connectome/MICrONS/soma_subgraph_synapses_spines_v185.csv")
microns


microns.columns

hemibrain_traced_roi_connections = pd.read_csv("/scratch/users/oaa9/experimentation/data/connectome/hemibrain/exported-traced-adjacencies-v1.2/traced-roi-connections.csv")
hemibrain_traced_roi_connections

c_elegans = pd.read_csv("/scratch/users/oaa9/experimentation/data/connectome/c.elegans/celegans_actual.csv")
print(c_elegans)
c_elegans.columns = c_elegans.columns.str.replace(" ", "")
c_elegans.columns = c_elegans.columns.str.strip()
c_elegans["post1"] = c_elegans["post1"].astype(str)
c_elegans["post2"] = c_elegans["post2"].astype(str)
c_elegans["post3"] = c_elegans["post3"].astype(str)
c_elegans["post4"] = c_elegans["post4"].astype(str)
#c_elegans

temp_cols = list(c_elegans.columns)
temp_cols.remove("post1")
temp_cols.remove("post2")
temp_cols.remove("post3")
temp_cols.remove("post4")
temp = {k:[] for k in temp_cols}
for index,row in c_elegans.iterrows():
    if row["post1"] != "nan":
        for k in temp_cols:
            if k == "post":
                temp[k].append(row["post1"])
            else:
                temp[k].append(row[k])
    if row["post2"] != "nan":
        for k in temp_cols:
            if k == "post":
                temp[k].append(row["post2"])
            else:
                temp[k].append(row[k])
    if row["post3"] != "nan":
        for k in temp_cols:
            if k == "post":
                temp[k].append(row["post3"])
            else:
                temp[k].append(row[k])
    if row["post4"] != "nan":
        for k in temp_cols:
            if k == "post":
                temp[k].append(row["post4"])
            else:
                temp[k].append(row[k])

c_elegans_from_dict = pd.DataFrame.from_dict(temp)
c_elegans_from_dict

neuron_dfs_in_pandas = [c_elegans_from_dict, microns, hemibrain_traced_roi_connections]


neuron_dfs_in_arkouda = [ak.DataFrame(pd_df) for pd_df in neuron_dfs_in_pandas]

ak_celegans = neuron_dfs_in_arkouda[0]
ak_microns = neuron_dfs_in_arkouda[1]
ak_hemibrain_traced_roi_connections = neuron_dfs_in_arkouda[2]

ak_celegans_gb = ak_celegans.groupby(["pre", "post"])
print(ak_celegans_gb)


ak_celegans_sorted = ak_celegans[ak_celegans_gb.permutation[ak_celegans_gb.segments]]
chemical_synapses = ak_celegans_sorted["type"] == "chemical"
ak_celegans_sorted = ak_celegans_sorted[chemical_synapses]

ak_celegans_nodes = ak.concatenate([ak_celegans_sorted["pre"], ak_celegans_sorted["post"]])
gb_celegans_nodes = ak.GroupBy(ak_celegans_nodes)
new_vertex_range = ak.arange(gb_celegans_nodes.unique_keys.size)
all_vertices = gb_celegans_nodes.broadcast(new_vertex_range)
ak_celegans_sorted["pre"] = all_vertices[0:ak_celegans_sorted.shape[0]]
ak_celegans_sorted["post"] = all_vertices[ak_celegans_sorted.shape[0]:]
#ak_celegans_sorted

ak_microns_gb = ak_microns.groupby(["pre_root_id", "post_root_id"])
ak_microns_sorted = ak_microns[ak_microns_gb.permutation[ak_microns_gb.segments]]
#ak_microns_sorted

ak_hemibrain_traced_roi_connections_gb = ak_hemibrain_traced_roi_connections.groupby(["bodyId_pre", "bodyId_post"])
ak_hemibrain_traced_roi_connections_sorted = ak_hemibrain_traced_roi_connections[ak_hemibrain_traced_roi_connections_gb.permutation[ak_hemibrain_traced_roi_connections_gb.segments]]
#ak_hemibrain_traced_roi_connections_sorted

#ak_celegans_sorted.columns



ak_celegans_sorted['src'] = ak_celegans_sorted['pre']
del ak_celegans_sorted['pre']  # Remove the original column

ak_celegans_sorted['dst'] = ak_celegans_sorted['post']
del ak_celegans_sorted['post']  # Remove the original column

#ak_celegans_sorted.columns


#ak_microns_sorted.columns


ak_microns_sorted['src'] = ak_microns_sorted['pre_root_id']
del ak_microns_sorted['pre_root_id']  # Remove the original column

ak_microns_sorted['dst'] = ak_microns_sorted['post_root_id']
del ak_microns_sorted['post_root_id']  # Remove the original column

#ak_microns_sorted.columns

ak_hemibrain_traced_roi_connections_sorted['src'] = ak_hemibrain_traced_roi_connections_sorted['bodyId_pre']
del ak_hemibrain_traced_roi_connections_sorted['bodyId_pre']  # Remove the original column

ak_hemibrain_traced_roi_connections_sorted['dst'] = ak_hemibrain_traced_roi_connections_sorted['bodyId_post']
del ak_hemibrain_traced_roi_connections_sorted['bodyId_post']  # Remove the original column

#ak_hemibrain_traced_roi_connections_sorted.columns

ak_microns_sorted['type'] = ak.array(["chemical"] *ak_microns_sorted.shape[0])

print(ak_microns_sorted)

ar_microns = ar.PropGraph()
ar_microns.load_edge_attributes(ak_microns_sorted, source_column="src", destination_column="dst", relationship_columns=["type"])
all_nodes = ak.concatenate([ak_microns_sorted['src'], ak_microns_sorted['dst']])
unique_nodes = ak.unique(all_nodes)
#unique_nodes.size
lbls = ak.array(["1"]*unique_nodes.size)
microns_node_df = ak.DataFrame({"nodes": unique_nodes, "lbls":lbls})

ar_microns.load_node_attributes(microns_node_df,node_column="nodes", label_columns=["lbls"])
                                 

print("Data loaded now we are loading the subraph....")
subgraph = ar.PropGraph()
motif = Motif("""
A -> B 
B -> A
A -> C
C -> A
B -> C
""")
src_subgraph = ak.array([0, 1, 0, 2, 1])
dst_subgraph = ak.array([1, 0, 2, 0, 2])
lbls_subgraph = ak.array(["1"]*3)
rels_subgraph = ak.array([  "chemical"]*len(src_subgraph))
edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph, "rels":rels_subgraph})
node_df_h = ak.DataFrame({"nodes": ak.arange(0,3), "lbls":lbls_subgraph})
subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                relationship_columns=["rels"])
subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls"])


#prop_graph= ar_celegans
prop_graph= ar_microns
# Grab vertex and edge data from the Arachne dataframes.
graph_node_information = prop_graph.get_node_attributes()
graph_edge_information = prop_graph.get_edge_attributes()
subgraph_node_information = subgraph.get_node_attributes()
subgraph_edge_information = subgraph.get_edge_attributes()




# Convert Arkouda dataframes to Pandas dataframes to NetworkX graph attributes.
G = nx.from_pandas_edgelist(graph_edge_information.to_pandas(), source='src',
                            target='dst', edge_attr=True, create_using=nx.DiGraph)
H = nx.from_pandas_edgelist(subgraph_edge_information.to_pandas(), source='src',
                                target='dst', edge_attr=True, create_using=nx.DiGraph)

# Convert graph node attributes to Pandas dfs, remove nodes, and convert rows to dicts.
graph_node_attributes = graph_node_information.to_pandas()
graph_nodes_from_df = list(graph_node_attributes.pop("nodes"))
graph_node_attributes = graph_node_attributes.to_dict('index')
graph_node_attributes_final = {}

# Convert subgraph node attributes to Pandas dfs remove nodes, and convert rows to dicts.
subgraph_node_attributes = subgraph_node_information.to_pandas()
subgraph_nodes_from_df = list(subgraph_node_attributes.pop("nodes"))
subgraph_node_attributes = subgraph_node_attributes.to_dict('index')
subgraph_node_attributes_final = {}


    # Convert Pandas index to original node index.
for key in graph_node_attributes:
    graph_node_attributes_final[graph_nodes_from_df[key]] = graph_node_attributes[key]

for key in subgraph_node_attributes:
        subgraph_node_attributes_final[subgraph_nodes_from_df[key]] = subgraph_node_attributes[key]



    # Set the node attributes for G and H from dicts.
nx.set_node_attributes(G, graph_node_attributes_final)
nx.set_node_attributes(H, subgraph_node_attributes_final)



print(" Arachne....")
start = time.time()
#isos = ar.subgraph_isomorphism(ar_celegans, subgraph)
isos = ar.subgraph_isomorphism(ar_microns, subgraph)
end = time.time()
print(f"Finding {len(isos)/3} monomorphisms took {end-start} secs")
print("************************************************************")
print(" NetworkX... ")

    # Find subgraph isomorphisms of H in G.
start_time = time.time()
GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)
subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())
elapsed_time = time.time() - start_time
print(f"NetworkX execution time: {elapsed_time} seconds")
print(f"NetworkX found: {len(subgraph_isomorphisms)} isos")
print("************************************************************")
print(" DotMotif....")
E = GrandIsoExecutor(graph=G)

# Create the search engine.

start = time.time()

results = E.find(motif)
elapsed_time = time.time() - start_time
print(f"DotMotif execution time: {elapsed_time} seconds")
print(f"Dotmotif found: {len(subgraph_isomorphisms)} isos")
print(len(results))

ak.shutdown()
