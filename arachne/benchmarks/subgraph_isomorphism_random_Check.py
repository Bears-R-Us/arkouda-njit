"""Generate random graph with the Erdős-Rényi model."""

import argparse
import time
import arachne as ar
import arkouda as ak
import numpy as np
import networkx as nx
import random

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

def create_random_graph(n, p):
    """Generate a random graph using the Erdős-Rényi model."""
    src = []
    dst = []

    # Iterate over all possible pairs of nodes
    for i in range(n):
        for j in range(i+1, n):
            if np.random.random() < p:
                src.append(i)
                dst.append(j)

    return src, dst

def create_dindoost_random_graph(n):
    num_nodes = n
    random_directed_graph = nx.DiGraph()
    random_edges_per_node = [random.randint(5,10) for _ in range(num_nodes)]
    random_directed_graph.add_nodes_from(range(num_nodes))

    # Add directed edges with random weights
    for i in range(num_nodes):
        for _ in range(random_edges_per_node[i]):
            if random.random() < 0.5:  # Adjusted probability for edge creation (denser graph)
                j = random.randint(0, num_nodes - 1)  # Random destination node
                random_directed_graph.add_edge(i, j, weight=random.random())
    
    edges = random_directed_graph.edges()
    src = [edge[0] for edge in edges]
    dst = [edge[1] for edge in edges]

    return src, dst
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

    return src, dst

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
    # This approach will create a random graph where the presence of
    # each edge is determined independently with probability p. The Erdős-Rényi
    # model is effective for creating graphs with a specified average degree,
    # but it's important to note that it produces graphs with a Poisson degree distribution,
    # which might not always accurately model real-world networks!
    num_nodes = args.n  # Number of nodes
    p = 1  # Probability of edge creation
    print("Begining of Random Directed graph with P= ",p)
    # src, dst = create_random_graph(n, p)
    src, dst = create_random_directed_graph(num_nodes, p)
    print("Random Directed graph created")

    src_ak = ak.array(src)
    dst_ak = ak.array(dst)

    # 2. Build temporary property graph to get sorted edges and nodes lists.
    temp_prop_graph = ar.PropGraph()
    start = time.time()
    temp_prop_graph.add_edges_from(src_ak, dst_ak)
    end = time.time()
    build_time = end - start
    print(f"Building property graph with {len(temp_prop_graph)} vertices and "
          f"{temp_prop_graph.size()} "
          f"edges took {round(build_time,2)} seconds.")

    ### Generate node labels and edge relationships for the graph.
    # 1. Extract node and edge information.
    num_edges = temp_prop_graph.size()
    num_nodes = len(temp_prop_graph)
    edges = temp_prop_graph.edges()
    nodes = temp_prop_graph.nodes()

    # 2. Generate sets of node labels and edge relationships.
    labels_set = ak.array(["lbl" + str(x) for x in range(1, args.x+1)])
    relationships_set = ak.array(["rel" + str(y) for y in range(1, args.y+1)])

    # 3. Give edges and nodes some labels and relationships.
    node_labels = labels_set[ak.randint(0, len(labels_set), num_nodes)]
    edge_relationships = relationships_set[ak.randint(0, len(relationships_set), num_edges)]

    # 4. Create dataframe to load into a new property graph.
    edge_df = ak.DataFrame({"src":edges[0], "dst":edges[1], "rels1":edge_relationships})
    node_df = ak.DataFrame({"nodes":nodes, "lbls1":node_labels})

    # 5. Create new property graph with node labels and edge relationships.
    prop_graph = ar.PropGraph()
    prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1"])
    prop_graph.load_node_attributes(node_df, node_column="nodes", label_columns=["lbls1"])
    #print(node_df.__str__)
    #print(edge_df.__str__)

    ### Create the subgraph we are searching for.
    # 1. Create labels and relationships to search for.
    src_subgraph = ak.array([0, 1, 2, 1])
    dst_subgraph = ak.array([1, 2, 0, 3])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    #labels2_subgraph = ak.array(["lbl2", "lbl2", "lbl2", "lbl2"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])
    #rels2_subgraph = ak.array(["rel2", "rel2", "rel2", "rel2"])

    # 2. Populate the subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph,
                            "rels1":rels1_subgraph})
                            #"rels1":rels1_subgraph, "rels2":rels2_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.array([0,1,2,3]), "lbls1":labels1_subgraph,
                              })
                              #"lbls2":labels2_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1"])
                                    #relationship_columns=["rels1","rels2"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1"])
    #subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])
    #print(node_df_h.__str__)
    #print(edge_df_h.__str__)
    print("Running Arachne ")
    ### Run subgraph isomorphism.
    start_time = time.time()
    #print("start_time = ", start_time)
    Arachne_isos = ar.subgraph_isomorphism(prop_graph,subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(Arachne_isos)/4} isos")


    #### Run NetworkX subgraph isomorphism.
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

    # print(f"graph_node_attributes = {graph_node_attributes}")
    # print(f"graph_nodes_from_df = {graph_nodes_from_df}")

    # print(f"graph_node_attributes = {graph_node_attributes}")
    # print(f"graph_nodes_from_df = {graph_nodes_from_df}")

    # Convert Pandas index to original node index.
    for key in graph_node_attributes:
        graph_node_attributes_final[graph_nodes_from_df[key]] = graph_node_attributes[key]

    for key in subgraph_node_attributes:
        subgraph_node_attributes_final[subgraph_nodes_from_df[key]] = subgraph_node_attributes[key]

    # print(f"graph_node_attributes_final = {graph_node_attributes_final}")
    # print(f"subgraph_node_attributes_final = {subgraph_node_attributes_final}")

    # Set the node attributes for G and H from dicts.
    nx.set_node_attributes(G, graph_node_attributes_final)
    nx.set_node_attributes(H, subgraph_node_attributes_final)

    # Find subgraph isomorphisms of H in G.
    start_time = time.time()
    GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)
    nx_isomorphisms = list(GM.subgraph_monomorphisms_iter())

    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")
    print(f"NetworkX found: {len(nx_isomorphisms)} isos")
    
    
    
    #### Compare Arachne subgraph isomorphism to NetworkX.
    from collections import Counter
    import numpy as np
    
    # Function to transform the list into a list of dictionaries
    def transform_arachne_isos(arachne_isos):
        transformed = []
        for i in range(0, len(arachne_isos), 4):
            mapping = {j: arachne_isos[i + j] for j in range(4)}
            transformed.append(mapping)
        return transformed

    transformed_Arachne_isos = transform_arachne_isos(Arachne_isos)

    def dicts_to_sorted_tuples(dicts):
        #Convert a list of dictionaries to a list of sorted tuples.
        return [tuple(sorted(d.items())) for d in dicts]

    def compare_isomorphisms(isos1, isos2):
        #Compare two lists of isomorphisms and return differences.
        tuples1 = set(dicts_to_sorted_tuples(isos1))
        tuples2 = set(dicts_to_sorted_tuples(isos2))

        if tuples1 == tuples2:
            return True, None, None

        missing_in_isos2 = tuples1 - tuples2
        missing_in_isos1 = tuples2 - tuples1

        return False, missing_in_isos2, missing_in_isos1

    # Compare the two lists of isomorphisms
    print("begining the comparision")
    equal, missing_in_nx, missing_in_arachne = compare_isomorphisms(nx_isomorphisms, transformed_Arachne_isos)

    if equal:
        print("Isomorphisms are equal")
    else:
        print("Isomorphisms are not equal")
        if missing_in_nx:
            print("Missing in transformed_Arachne_isos:", missing_in_nx)
        if missing_in_arachne:
            print("Missing in nx_isomorphisms:", missing_in_arachne)
        
    ak.shutdown()
