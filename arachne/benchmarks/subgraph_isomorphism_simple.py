"""Simple correctness check for subgraph isomorphism."""
import argparse
import time

import networkx as nx
import arachne as ar
import arkouda as ak

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
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
def graph_to_grf(G, output_file):
    with open(output_file, 'w') as f:
        # Write the number of nodes
        f.write(f"{G.number_of_nodes()}\n")

        # Write each node and its label (assuming label is 1 for all nodes)
        for node in sorted(G.nodes()):
            f.write(f"{node} 1\n")  # Replace 1 with your label logic if needed

        # Write the number of outgoing edges and the edges themselves
        for node in sorted(G.nodes()):
            out_edges = list(G.successors(node))  # Get the list of successors (outgoing edges)
            f.write(f"{len(out_edges)}\n")  # Write the number of outgoing edges
            for target in out_edges:
                f.write(f"{node} {target}\n")  # Write each edge on a new line

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

    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    #### Run Arachne subgraph isomorphism.
    # 1. Create vertices, edges, and attributes for main property graph.
    src_prop_graph = ak.array([1, 2, 3, 3, 5, 6, 7, 1, 6, 2, 7, 3, 8, 4, 5, 10, 6 , 11, 7 , 11, 8, 9 , 10, 11, 8 , 13])
    dst_prop_graph = ak.array([0, 1, 2, 4, 6, 7, 8, 5, 1, 6, 2, 7, 3, 8, 9, 5 , 10, 6 , 11, 8, 12, 10, 11, 12, 13, 14])
    
   
    labels1_prop_graph = ak.array(["lbl1"] * 15)
    labels2_prop_graph = ak.array(["lbl2"] * 15)
    rels1_prop_graph = ak.array(["rel1"] * src_prop_graph.size)
    rels2_prop_graph =  ak.array(["rel2"] * src_prop_graph.size)

    # 2. Transer data above into main property graph.
    prop_graph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_prop_graph, "dst":dst_prop_graph,
                            "rels1":rels1_prop_graph, "rels2":rels2_prop_graph})
    node_df_h = ak.DataFrame({"nodes": ak.arange(0,15), "lbls1":labels1_prop_graph,
                              "lbls2":labels2_prop_graph})
    prop_graph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1","rels2"])
    prop_graph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])

    # 3. Create vertices, edges, and attributes for subgraph.
    src_subgraph = ak.array([0, 1, 1, 2])
    dst_subgraph = ak.array([1, 2, 3, 0])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    labels2_subgraph = ak.array(["lbl2", "lbl2", "lbl2", "lbl2"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])
    rels2_subgraph = ak.array(["rel2", "rel2", "rel2", "rel2"])

    #updated_src, updated_dst, unique_nodes_list, replaced_nodes = SubgraphMatchingOrder(src_subgraph, dst_subgraph)
    updated_src = src_subgraph
    updated_dst = dst_subgraph

    
    src_subgraph = updated_src
    dst_subgraph = updated_dst
    # 4. Transer data above into subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph,
                            "rels1":rels1_subgraph, "rels2":rels2_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.arange(0,4), "lbls1":labels1_subgraph,
                              "lbls2":labels2_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1","rels2"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])

    # 5. Run the subgraph isomorphism.
    print("Arachne running ...")
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    print("isos = ",isos)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")

    #### Run NetworkX subgraph isomorphism.
    # Get the NetworkX version
    #print("NetworkX version:", nx.__version__)

    # Grab vertex and edge data from the Arachne dataframes.
    graph_node_information = prop_graph.get_node_attributes()
    graph_edge_information = prop_graph.get_edge_attributes()
    subgraph_node_information = subgraph.get_node_attributes()
    subgraph_edge_information = subgraph.get_edge_attributes()

    # The 4 for loops below convert internal integer labels to original strings.
    for (column,array) in graph_node_information.items():
        if column != "nodes":
            mapper = prop_graph.label_mapper[column]
            graph_node_information[column] = mapper[array]

    for (column,array) in graph_edge_information.items():
        if column not in ("src", "dst"):
            mapper = prop_graph.relationship_mapper[column]
            graph_edge_information[column] = mapper[array]

    for (column,array) in subgraph_node_information.items():
        if column != "nodes":
            mapper = subgraph.label_mapper[column]
            subgraph_node_information[column] = mapper[array]

    for (column,array) in subgraph_edge_information.items():
        if column not in ("src", "dst"):
            mapper = subgraph.relationship_mapper[column]
            subgraph_edge_information[column] = mapper[array]

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

    # Measure execution time.
    start_time = time.time()

    # Find subgraph isomorphisms of H in G.
    GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)

    # List of dicts. For each dict, keys is original graph vertex, values are subgraph vertices.
    subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())
    #print("Networkx found = ")
    #print(subgraph_isomorphisms)
    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")
    print(f"NetworkX found: {len(subgraph_isomorphisms)} isos")
    
    graph_to_grf(G, 'simple_graph.grf')
    graph_to_grf(H, 'simple_sub_graph.grf')

    #### Compare Arachne subgraph isomorphism to NetworkX.
    isos_list = isos.to_list()
    isos_sublists = [isos_list[i:i+4] for i in range(0, len(isos_list), 4)]

    isos_as_dicts = []
    subgraph_vertices = [0, 1, 2, 3]
    for iso in isos_sublists:
        isos_as_dicts.append(dict(zip(iso, subgraph_vertices)))

    for iso in isos_as_dicts:
        if iso not in subgraph_isomorphisms:
            print (iso)
            print("ERROR: Subgraph isomorphisms do not match!")
            

    if args.print_isos:
        for iso in isos_as_dicts:
            print(iso)

        print()

        for iso in subgraph_isomorphisms:
            print(iso)

    ak.shutdown()
