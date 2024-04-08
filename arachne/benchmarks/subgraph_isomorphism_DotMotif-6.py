"""Generate random graph with the Erdős-Rényi model."""

import argparse
import time
import arachne as ar
import arkouda as ak
import numpy as np
import networkx as nx
import random
from dotmotif import Motif, GrandIsoExecutor 

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    #script_parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    #script_parser.add_argument("m", type=int, default=2000, help="Number of edges for graph")
    script_parser.add_argument("x", type=int, default=5, help="Number of labels for graph")
    script_parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")
    #script_parser.add_argument("s", type=int, default=2, help="Random seed for reproducibility")
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

    return src, dst


def generate_erdos_renyi_directed():
    # Sample the number of nodes uniformly between 100 and 300
    n = np.random.randint(100, 301)
    #print("n randomly choosen (100,300) = ", n)
    # Sample the density (probability for edge creation) uniformly between 0 and 0.3
    p = np.random.uniform(0, 0.3)
    #print("p densities randomly choosen (0,0.3) = ", p)

    # Generate the Erdős–Rényi directed graph
    random_graph = nx.gnp_random_graph(n, p, directed=True)
    
    # Extract src and dst arrays
    src = [edge[0] for edge in random_graph.edges()]
    dst = [edge[1] for edge in random_graph.edges()]

    return src, dst, random_graph.number_of_nodes(), random_graph.number_of_edges(),nx.density(random_graph)


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


    src, dst, num_nodes, num_edges, density = generate_erdos_renyi_directed()
    print("Generated Graph Details:")
    print("num_nodes = ", num_nodes)
    print("num_edges = ", num_edges)
    print("density = ", density)
    
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
    src_subgraph = ak.array([0, 0, 2, 3])
    dst_subgraph = ak.array([1, 2, 3, 0])
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
    print("Running Arachne...")
    ### Run subgraph isomorphism.
    start_time = time.time()
    #print("start_time = ", start_time)
    isos = ar.subgraph_isomorphism(prop_graph,subgraph)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")


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
    print("**********************************************")

    print("Running NetworkX... ")

    # Find subgraph isomorphisms of H in G.
    start_time = time.time()
    GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)
    subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())
    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")
    print(f"NetworkX found: {len(subgraph_isomorphisms)} isos")


    motif = Motif("""
    A -> C 
    A -> B
    C -> D
    D -> A
    """)
    print("************************************************************")
    print(" DotMotif....")
    E = GrandIsoExecutor(graph=G)

    # Create the search engine.

    start = time.time()

    results = E.find(motif)
    elapsed_time = time.time() - start_time
    print(f"DotMotif execution time: {elapsed_time} seconds")
    print(f"Dotmotif found: {len(results)} isos")
    #print(len(results))
    """

    #### Compare Arachne subgraph isomorphism to NetworkX.
    #print("isos = ", isos)
    isos_list = isos.to_list()
    isos_sublists = [isos_list[i:i+3] for i in range(0, len(isos_list), 3)]
    for elm in isos_sublists:
        #print(elm.len())
        if len(elm) != 4:
            print ("Error in len = ",len(elm))
        
    isos_as_dicts = []
    subgraph_vertices = [0, 1, 2]
    print("making dict")
    for iso in isos_sublists:
        isos_as_dicts.append(dict(zip(iso, subgraph_vertices)))
    
    print("checking for correctness")
    counter = 0
    print("**********************************************")
    for iso in isos_as_dicts:
        if iso not in subgraph_isomorphisms:
            #print("missing is: ", iso)
            counter += 1
            #print("ERROR: Subgraph isomorphisms do not match!")
            #break
    print("checking for printing or not")

    if args.print_isos:
        for iso in isos_as_dicts:
            print(iso)

        print()
        print("NetworkX:")
        for iso in subgraph_isomorphisms:
            print(iso)

    print ("Number of missing is ", counter)
"""
    ak.shutdown()