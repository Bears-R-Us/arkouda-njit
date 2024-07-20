import arkouda as ak
import arachne as ar
import pandas as pd
import time as time
import networkx as nx
import random
import argparse
from dotmotif import Motif, GrandIsoExecutor 

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    #script_parser.add_argument("m", type=int, default=2000, help="Number of edges for graph")
    script_parser.add_argument("x", type=int, default=5, help="Number of labels for graph")
    script_parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")
    #script_parser.add_argument("s", type=int, default=2, help="Random seed for reproducibility")
    script_parser.add_argument('--print_isos', action='store_true', help="Print isos?")

    return script_parser
def compute_degrees(src, dst):
    # Find unique nodes
    unique_nodes = ak.unique(ak.concatenate([src, dst]))
    
    # Initialize degree arrays
    in_degree = ak.zeros(len(unique_nodes), dtype=ak.int64)
    out_degree = ak.zeros(len(unique_nodes), dtype=ak.int64)
    
    # Convert Arkouda arrays to Python lists for iteration
    unique_nodes_list = unique_nodes.to_list()
    
    # Create a dictionary to map nodes to their index in unique_nodes
    node_to_index = {node: idx for idx, node in enumerate(unique_nodes_list)}
    
    # Calculate out-degrees
    for node in src.to_list():
        out_degree[node_to_index[node]] += 1
    
    # Calculate in-degrees
    for node in dst.to_list():
        in_degree[node_to_index[node]] += 1
    
    # Calculate total degrees
    total_degree = in_degree + out_degree
    
    return unique_nodes_list, node_to_index, in_degree.to_list(), out_degree.to_list(), total_degree.to_list()

def update_degrees(src_temp, dst_temp, unique_nodes_list):
    # Recompute degrees based on updated src_temp and dst_temp
    node_to_index = {node: idx for idx, node in enumerate(unique_nodes_list)}
    in_degree = [0] * len(unique_nodes_list)
    out_degree = [0] * len(unique_nodes_list)
    
    for i in range(len(src_temp)):
        out_degree[node_to_index[src_temp[i]]] += 1
        in_degree[node_to_index[dst_temp[i]]] += 1
    
    total_degree = [in_degree[i] + out_degree[i] for i in range(len(unique_nodes_list))]
    
    return in_degree, out_degree, total_degree

def SubgraphMatchingOrder(src, dst):
    # Make copies of src and dst
    src_temp = src.to_list()
    dst_temp = dst.to_list()
    
    #print("Initial src_temp:", src_temp)
    #print("Initial dst_temp:", dst_temp)
    
    # Compute degrees
    unique_nodes_list, node_to_index, in_degree, out_degree, total_degree = compute_degrees(src, dst)
    
    #print("Unique Nodes:", unique_nodes_list)
    #print("In-Degree:", in_degree)
    #print("Out-Degree:", out_degree)
    #print("Total Degree:", total_degree)
    
    # Step 1: Find the node with the highest degree, breaking ties with out-degree
    candidates = [(unique_nodes_list[i], total_degree[i], out_degree[i]) for i in range(len(unique_nodes_list))]
    candidates.sort(key=lambda x: (-x[1], -x[2]))
    #print("candidates = ", candidates)
    replaced_nodes = []  # List to keep track of replaced nodes
    
    if candidates:
        selected_node = candidates[0][0]
        sorted_index = 0
        #print("replaced_nodes:", replaced_nodes)

        #print(f"\nInitial Selected Node: {selected_node}, Sorted Index: {sorted_index}")
        
        # Step 2: Exchange selected_node with unique_nodes_list[sorted_index] in src_temp and dst_temp
        for i in range(len(src_temp)):
            if src_temp[i] == selected_node:
                src_temp[i] = unique_nodes_list[sorted_index]
            elif src_temp[i] == unique_nodes_list[sorted_index]:
                src_temp[i] = selected_node
            
            if dst_temp[i] == selected_node:
                dst_temp[i] = unique_nodes_list[sorted_index]
            elif dst_temp[i] == unique_nodes_list[sorted_index]:
                dst_temp[i] = selected_node
        
        replaced_nodes.append(unique_nodes_list[sorted_index])  # Mark the node placed in the sorted position
        
        #print("1 replaced_nodes:", replaced_nodes)
        #print("Updated src_temp:", src_temp)
        #print("Updated dst_temp:", dst_temp)
        #print("////////////////////////////////////////////////////////////")
    
    # Process nodes until all are sorted
    while len(replaced_nodes) < len(unique_nodes_list):
        current_node = replaced_nodes[-1]
        #print("************while begin**************")
        #print("current_node = ", current_node)
        
        # Recompute degrees based on updated src_temp and dst_temp
        in_degree, out_degree, total_degree = update_degrees(src_temp, dst_temp, unique_nodes_list)
        
        # Process out-neighbors
        out_neighbors = [dst_temp[i] for i in range(len(src_temp)) if src_temp[i] == current_node and dst_temp[i] not in replaced_nodes]
        out_neighbors.sort(key=lambda x: (-total_degree[node_to_index[x]], -out_degree[node_to_index[x]]))
        
        #print("Out-Neighbors:", out_neighbors)
        
        if out_neighbors:
            next_node = out_neighbors[0]
            sorted_index = len(replaced_nodes)
            
            # Exchange next_node with unique_nodes_list[sorted_index] in src_temp and dst_temp
            for i in range(len(src_temp)):
                if src_temp[i] == next_node:
                    src_temp[i] = unique_nodes_list[sorted_index]
                elif src_temp[i] == unique_nodes_list[sorted_index]:
                    src_temp[i] = next_node
                
                if dst_temp[i] == next_node:
                    dst_temp[i] = unique_nodes_list[sorted_index]
                elif dst_temp[i] == unique_nodes_list[sorted_index]:
                    dst_temp[i] = next_node
            
            replaced_nodes.append(unique_nodes_list[sorted_index])  # Mark the node placed in the sorted position
            
            #print(f"\nNext Selected Node: {next_node}, Sorted Index: {sorted_index}")
            #print("Updated src_temp:", src_temp)
            #print("Updated dst_temp:", dst_temp)
        else:
            # If no out-neighbors, find the next node with the highest degree from remaining nodes
            remaining_candidates = [(unique_nodes_list[i], total_degree[i], out_degree[i]) for i in range(len(unique_nodes_list)) if unique_nodes_list[i] not in replaced_nodes]
            remaining_candidates.sort(key=lambda x: (-x[1], -x[2]))
            if remaining_candidates:
                selected_node = remaining_candidates[0][0]
                sorted_index = len(replaced_nodes)
                
                # Exchange selected_node with unique_nodes_list[sorted_index] in src_temp and dst_temp
                for i in range(len(src_temp)):
                    if src_temp[i] == selected_node:
                        src_temp[i] = unique_nodes_list[sorted_index]
                    elif src_temp[i] == unique_nodes_list[sorted_index]:
                        src_temp[i] = selected_node
                    
                    if dst_temp[i] == selected_node:
                        dst_temp[i] = unique_nodes_list[sorted_index]
                    elif dst_temp[i] == unique_nodes_list[sorted_index]:
                        dst_temp[i] = selected_node
                
                replaced_nodes.append(unique_nodes_list[sorted_index])  # Mark the node placed in the sorted position
                
                #print(f"\nSelected Node (No Out-Neighbors): {selected_node}, Sorted Index: {sorted_index}")
                #print("Updated src_temp:", src_temp)
                #print("Updated dst_temp:", dst_temp)
    
    # Convert updated src_temp and dst_temp back to Arkouda arrays
    updated_src = ak.array(src_temp)
    updated_dst = ak.array(dst_temp)
    
    return updated_src, updated_dst, unique_nodes_list, replaced_nodes


if __name__ == "__main__":
    #### Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()
    #check
    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    ### Get Arkouda server configuration information.
    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")



    hemibrain_traced_roi_connections = pd.read_csv("/scratch/users/oaa9/experimentation/data/connectome/hemibrain/exported-traced-adjacencies-v1.2/traced-roi-connections.csv")
    hemibrain_traced_roi_connections
    hemibrain_traced_roi_connections['type'] = 'T1'
    hemibrain_traced_roi_connections
    
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

    #ak_celegans_sorted

    ar_hemibrain = ar.PropGraph()
    ar_hemibrain.load_edge_attributes(ak_hemibrain_traced_roi_connections_sorted, source_column="src", destination_column="dst", relationship_columns=["type"])

    all_nodes = ak.concatenate([ak_hemibrain_traced_roi_connections_sorted['src'], ak_hemibrain_traced_roi_connections_sorted['dst']])
    unique_nodes = ak.unique(all_nodes)
    #unique_nodes.size
    lbls = ak.array(["1"]*unique_nodes.size)
    hemibrain_node_df = ak.DataFrame({"nodes": unique_nodes, "lbls":lbls})

    ar_hemibrain.load_node_attributes(hemibrain_node_df,node_column="nodes", label_columns=["lbls"])
                                    

    print("Data loaded now we are loading the subraph....")

    subgraph = ar.PropGraph()
    motif = Motif("""
    B -> A 
    B -> C
    """)
    src_subgraph = ak.array([0,1])
    dst_subgraph = ak.array([1,2])
    lbls_subgraph = ak.array(["1"]*3)
    rels_subgraph = ak.array(["T1"]*len(src_subgraph))



    updated_src, updated_dst, unique_nodes_list, replaced_nodes = SubgraphMatchingOrder(src_subgraph, dst_subgraph)
    print("\nFinal Results:")
    print("Unique Nodes:", unique_nodes_list)
    print("Replaced Nodes:", replaced_nodes)
    print("Updated src_temp:", updated_src.to_list())
    print("Updated dst_temp:", updated_dst.to_list())
    
    src_subgraph = updated_src
    dst_subgraph = updated_dst

    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph, "rels":rels_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.arange(0,3), "lbls":lbls_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls"])


    #prop_graph= ar_celegans
    prop_graph= ar_hemibrain
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
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    end = time.time()
    print(f"Finding {len(isos)/4} monomorphisms took {end-start} secs")
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
