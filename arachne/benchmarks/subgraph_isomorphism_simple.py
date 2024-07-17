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
def SubgraphMatchingOrder(src, dst):
    # Find unique nodes
    unique_nodes = ak.unique(ak.concatenate([src, dst]))
    
    # Initialize degree arrays
    in_degree = ak.zeros(len(unique_nodes), dtype=ak.int64)
    out_degree = ak.zeros(len(unique_nodes), dtype=ak.int64)
    
    # Convert Arkouda arrays to Python lists for iteration
    unique_nodes_list = unique_nodes.to_list()
    src_list = src.to_list()
    dst_list = dst.to_list()
    
    # Create a dictionary to map nodes to their index in unique_nodes
    node_to_index = {node: idx for idx, node in enumerate(unique_nodes_list)}
    
    # Calculate out-degrees
    for node in src_list:
        out_degree[node_to_index[node]] += 1
    
    # Calculate in-degrees
    for node in dst_list:
        in_degree[node_to_index[node]] += 1
    
    # Calculate total degrees
    total_degree = in_degree + out_degree
    
    # Combine the degrees into a single list of tuples for sorting
    nodes_with_degrees = [(unique_nodes[i], total_degree[i], out_degree[i], in_degree[i]) for i in range(len(unique_nodes))]
    
    # Sort nodes to determine the starting node
    nodes_with_degrees.sort(key=lambda x: (-x[1], -x[2]))
    
    sorted_nodes = []
    selected_set = set()
    
    def select_node(node):
        sorted_nodes.append(node)
        selected_set.add(node)
    
    # Select the initial node
    initial_node = nodes_with_degrees[0][0]
    select_node(initial_node)
    
    current_node = initial_node
    
    while len(sorted_nodes) < len(unique_nodes):
        # Find out-neighbors of the current node that are not yet selected
        out_neighbors = [dst_list[i] for i in range(len(src_list)) if src_list[i] == current_node and dst_list[i] not in selected_set]
        
        if out_neighbors:
            # Sort out-neighbors based on the criteria
            out_neighbors_degrees = [(node, total_degree[node_to_index[node]], out_degree[node_to_index[node]]) for node in out_neighbors]
            out_neighbors_degrees.sort(key=lambda x: (-x[1], -x[2]))
            next_node = out_neighbors_degrees[0][0]
        else:
            # If no out-neighbors, pick the highest degree node from remaining unselected nodes
            remaining_nodes_degrees = [(node, total_degree[node_to_index[node]], out_degree[node_to_index[node]]) for node in unique_nodes_list if node not in selected_set]
            remaining_nodes_degrees.sort(key=lambda x: (-x[1], -x[2]))
            next_node = remaining_nodes_degrees[0][0]
        
        select_node(next_node)
        current_node = next_node
    
    # Create a mapping from original node to sorted node
    node_to_sorted = {original: sorted_nodes[i] for i, original in enumerate(unique_nodes_list)}
    
    # Update src and dst based on the sorted nodes
    updated_src = ak.array([node_to_sorted[node] for node in src_list])
    updated_dst = ak.array([node_to_sorted[node] for node in dst_list])
    
    return updated_src, updated_dst, sorted_nodes, unique_nodes

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
    src_subgraph = ak.array([1, 0, 0, 3])
    dst_subgraph = ak.array([0, 2, 3, 1])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    labels2_subgraph = ak.array(["lbl2", "lbl2", "lbl2", "lbl2"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])
    rels2_subgraph = ak.array(["rel2", "rel2", "rel2", "rel2"])

    updated_src, updated_dst, Subgraph_new_key, Subgraph_old_key = SubgraphMatchingOrder(src_subgraph, dst_subgraph)
    print("Subgraph Original Key:", Subgraph_old_key)
    print("Subgraph Updated Key:", Subgraph_new_key)

    print("Updated src:", updated_src)
    print("Updated dst:", updated_dst)
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
