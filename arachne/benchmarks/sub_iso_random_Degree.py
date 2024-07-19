import argparse
import time
import arachne as ar
import arkouda as ak
import numpy as np
import networkx as nx
import random
import matplotlib.pyplot as plt

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("p", type=float, default=0.0005, help="Port of arkouda server")
    script_parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    script_parser.add_argument("x", type=int, default=5, help="Number of labels for graph")
    script_parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")
    script_parser.add_argument('--print_isos', action='store_true', help="Print isos?")

    return script_parser

def create_random_directed_graph(num_nodes, p):
    """
    Generates a random directed graph (Erdős-Rényi model) and returns the src and dst arrays.
    
    Parameters:
    num_nodes (int): Number of nodes in the graph.
    p (float): Probability of creating an edge between two nodes.
    
    Returns:
    tuple: A tuple containing two lists (src, dst) representing the source and destination of each edge.
    """
    # Create a random graph using Erdős–Rényi model
    random_graph = nx.gnp_random_graph(num_nodes, p, seed=42, directed=True)

    # Extract src and dst arrays
    src = [edge[0] for edge in random_graph.edges()]
    dst = [edge[1] for edge in random_graph.edges()]

    return random_graph, src, dst


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

    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    ### Get Arkouda server configuration information.
    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")

    ### Generate an Erdős-Rényi random graph
    num_nodes = args.n  # Number of nodes
    p = args.p  # Probability of edge creation
    print("Beginning of Random Directed graph with P= ", p)

    random_graph, src, dst = create_random_directed_graph(num_nodes, p)
    print("Random Directed graph created")

    src_ak = ak.array(src)
    dst_ak = ak.array(dst)

    # Build temporary property graph to get sorted edges and nodes lists.
    temp_prop_graph = ar.PropGraph()
    start = time.time()
    temp_prop_graph.add_edges_from(src_ak, dst_ak)
    end = time.time()
    build_time = end - start
    print(f"Building property graph with {len(temp_prop_graph)} vertices and "
          f"{temp_prop_graph.size()} "
          f"edges took {round(build_time,2)} seconds.")

    ### Generate node labels and edge relationships for the graph.
    num_edges = temp_prop_graph.size()
    num_nodes = len(temp_prop_graph)
    edges = temp_prop_graph.edges()
    nodes = temp_prop_graph.nodes()

    # Generate sets of node labels and edge relationships.
    labels_set = ak.array(["lbl" + str(x) for x in range(1, args.x+1)])
    relationships_set = ak.array(["rel" + str(y) for y in range(1, args.y+1)])

    # Assign labels and relationships to nodes and edges.
    node_labels = labels_set[ak.randint(0, len(labels_set), num_nodes)]
    edge_relationships = relationships_set[ak.randint(0, len(relationships_set), num_edges)]

    # Create dataframe to load into a new property graph.
    edge_df = ak.DataFrame({"src": edges[0], "dst": edges[1], "rels1": edge_relationships})
    node_df = ak.DataFrame({"nodes": nodes, "lbls1": node_labels})

    # Create new property graph with node labels and edge relationships.
    prop_graph = ar.PropGraph()
    prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1"])
    prop_graph.load_node_attributes(node_df, node_column="nodes", label_columns=["lbls1"])

    # Create the subgraph we are searching for.
    src_subgraph = ak.array([0, 1, 1, 2])
    dst_subgraph = ak.array([1, 2, 3, 0])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    rels1_subgraph = ak.array(["rel1", "rel1","rel1", "rel1"])

    updated_src, updated_dst, unique_nodes_list, replaced_nodes = SubgraphMatchingOrder(src_subgraph, dst_subgraph)

    print("\nFinal Results:")
    print("Unique Nodes:", unique_nodes_list)
    print("Replaced Nodes:", replaced_nodes)
    print("Updated src_temp:", updated_src.to_list())
    print("Updated dst_temp:", updated_dst.to_list())
    
    src_subgraph = updated_src
    dst_subgraph = updated_dst
    
    # Populate the subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src": src_subgraph, "dst": dst_subgraph, "rels1": rels1_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.array([0, 1, 2,3]), "lbls1": labels1_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                  relationship_columns=["rels1"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1"])

    print("first Running Arachne...")
    # Run subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")

    """
    print("2nd Running Arachne...")
    # Run subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")
    
    print("3rd Running Arachne...")
    # Run subgraph isomorphism.
    start_time = time.time()
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")
    """
    ### Run NetworkX subgraph isomorphism.
    # Grab vertex and edge data from the Arachne dataframes.
    graph_node_information = prop_graph.get_node_attributes()
    graph_edge_information = prop_graph.get_edge_attributes()
    subgraph_node_information = subgraph.get_node_attributes()
    subgraph_edge_information = subgraph.get_edge_attributes()

    # The 4 for loops below convert internal integer labels to original strings.
    for (column, array) in graph_node_information.items():
        if column != "nodes":
            mapper = prop_graph.label_mapper[column]
            graph_node_information[column] = mapper[array]

    for (column, array) in graph_edge_information.items():
        if column not in ("src", "dst"):
            mapper = prop_graph.relationship_mapper[column]
            graph_edge_information[column] = mapper[array]

    for (column, array) in subgraph_node_information.items():
        if column != "nodes":
            mapper = subgraph.label_mapper[column]
            subgraph_node_information[column] = mapper[array]

    for (column, array) in subgraph_edge_information.items():
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

    # Convert subgraph node attributes to Pandas dfs, remove nodes, and convert rows to dicts.
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

    print("Running NetworkX... ")

    # Calculate the degrees
    in_degrees = dict(G.in_degree())
    out_degrees = dict(G.out_degree())

    # Calculate the total degrees (sum of in-degree and out-degree)
    total_degrees = {node: in_degrees[node] + out_degrees[node] for node in G.nodes()}

    # Calculate mean degrees
    mean_in_degree = np.mean(list(in_degrees.values()))
    mean_out_degree = np.mean(list(out_degrees.values()))
    mean_total_degree = np.mean(list(total_degrees.values()))

    # Plot the degree distribution
    degrees = list(total_degrees.values())
    plt.figure(figsize=(10, 6))
    plt.hist(degrees, bins=50, color='b', alpha=0.7, edgecolor='black')
    plt.title('Node Degree Distribution')
    plt.xlabel('Degree')
    plt.ylabel('Frequency')
    plt.yscale('log')  # Use a logarithmic scale for better visualization of the distribution
    plt.show()

    # Calculate the expected degree
    expected_in_degree = p * (num_nodes - 1)
    expected_out_degree = p * (num_nodes - 1)
    expected_total_degree = 2 * p * (num_nodes - 1)

    print(f'Expected in-degree: {expected_in_degree}')
    print(f'Expected out-degree: {expected_out_degree}')
    print(f'Expected total degree: {expected_total_degree}')

    print(f'Mean in-degree: {mean_in_degree}')
    print(f'Mean out-degree: {mean_out_degree}')
    print(f'Mean total degree: {mean_total_degree}')
    
    # Find subgraph isomorphisms of H in G.
    start_time = time.time()
    GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)
    subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())
    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")
    print(f"NetworkX found: {len(subgraph_isomorphisms)} isos")


    ak.shutdown()
