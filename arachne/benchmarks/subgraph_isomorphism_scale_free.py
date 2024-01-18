# Generating scale-free networks, which are characterized by a power-law degree distribution. 
#   here a few nodes having many connections while most nodes have few. The most famous algorithm
#   is the Barabási-Albert (BA) model. This model grows a network by attaching new nodes to 
#   existing nodes with a probability proportional to the number of links that the existing nodes 
#   already have. This process is known as "preferential attachment."
import argparse
import time
import arachne as ar
import networkx as nx
import numpy as np
import networkx as nx

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
    script_parser.add_argument("s", type=int, default=2, help="Random seed for reproducibility")
    script_parser.add_argument('--print_isos', action='store_true', help="Print isos?")

    return script_parser

def add_edges_pref_attach(src, dst, m, current_node, node_degrees):
    """Add edges to new node using preferential attachment."""
    total_degree = np.sum(node_degrees)
    if total_degree > 0:
        probs = node_degrees[:current_node] / total_degree  # Consider only existing nodes
        existing_nodes = np.arange(current_node)  # Array of existing node indices
        target_nodes = np.random.choice(existing_nodes, size=m, replace=False, p=probs)
        for target_node in target_nodes:
            src.append(current_node)
            dst.append(target_node)
            node_degrees[target_node] += 1
    return src, dst, node_degrees


if __name__ == "__main__":
    #### Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()

    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    #### Get Arkouda server configuration information.
    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")

    ### Generate a scale-free network
    m = 5  # Number of edges to attach from new node to existing nodes
    m0 = max(5, m)  # Initial number of interconnected nodes

    src = []
    dst = []
    node_degrees = np.zeros(args.n) #n is number of vertices for graph
    print("here 1")

    # Create initial interconnected network
    for i in range(m0):
        for j in range(i+1, m0):
            src.append(i)
            dst.append(j)
            node_degrees[i] += 1
            node_degrees[j] += 1
    print("here 2")
    # Add new nodes with preferential attachment
    for current_node in range(m0, args.n):
        src, dst, node_degrees = add_edges_pref_attach(src, dst, m, current_node, node_degrees)


    src_ak = ak.array(src)
    dst_ak = ak.array(dst)
    print("here 3")

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
    # 1. Extract node and edge information.
    num_edges = temp_prop_graph.size()
    num_nodes = len(temp_prop_graph)
    edges = temp_prop_graph.edges()
    nodes = temp_prop_graph.nodes()

    # 2. Generate https://njit.webex.com/njit/j.php?MTID=m7cd808ee0056d40c8b8c04b308e8ca5fsets of node labels and edge relationships.
    labels_set = ak.array(["lbl" + str(x) for x in range(1, args.x +1)])
    relationships_set = ak.array(["rel" + str(y) for y in range(1, args.y+1)])

    print("labels_set = ", labels_set)
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
    print("here 4")

    ### Create the subgraph we are searching for.
    # 1. Create labels and relationships to search for.
    src_subgraph = ak.array([0, 1, 0])
    dst_subgraph = ak.array([1, 2, 2])
    

    
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1"])
    labels2_subgraph = ak.array(["lbl2", "lbl2", "lbl2"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1"])
    rels2_subgraph = ak.array(["rel2", "rel2", "rel2"])

    # 2. Populate the subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph,
                            "rels1":rels1_subgraph, "rels2":rels2_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.array([0,1,2]), "lbls1":labels1_subgraph,
                              "lbls2":labels2_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1","rels2"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])
    print("here 5")

    ### Run subgraph isomorphism.
    start_time = time.time()

    isos = ar.subgraph_isomorphism(prop_graph,subgraph)
    #print("isos =", isos)
    
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")

    #### Run NetworkX subgraph isomorphism.
    # Get the NetworkX version
    print("NetworkX version:", nx.__version__)

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
    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")

    #### Compare Arachne subgraph isomorphism to NetworkX.
    isos_list = isos.to_list()
    isos_sublists = [isos_list[i:i+3] for i in range(0, len(isos_list), 3)]

    isos_as_dicts = []
    subgraph_vertices = [0, 1, 2]
    for iso in isos_sublists:
        isos_as_dicts.append(dict(zip(iso, subgraph_vertices)))

    for iso in isos_as_dicts:
        if iso not in subgraph_isomorphisms:
            print("ERROR: Subgraph isomorphisms do not match!")
            break

    if args.print_isos:
        for iso in isos_as_dicts:
            print(iso)

        print()

        for iso in subgraph_isomorphisms:
            print(iso)

    ak.shutdown()
