import argparse
import time
import arkouda as ak
import arachne as ar
import networkx as nx
import random

def create_barabasi_albert_graph(num_nodes, m):
    """
    Generates a directed Barabási-Albert graph (Scale-Free Networks).
    
    Parameters:
    num_nodes (int): Number of nodes in the graph.
    m (int): Number of edges to attach from a new node to existing nodes.
    
    Returns:
    nx.DiGraph: A directed Barabási-Albert graph.
    """
    UndirectedG = nx.barabasi_albert_graph(num_nodes, m, seed=42)
    DirectedG = UndirectedG.to_directed()
    for u, v in list(DirectedG.edges()):
        if random.random() < 0.5:  # probability for edge removal
            DirectedG.remove_edge(v, u)  # Remove one direction of the edge

    return DirectedG    

def create_watts_strogatz_graph(num_nodes, k, p):
    """
    Generates a Watts-Strogatz (small-world graph).

    Parameters:
    num_nodes (int): Number of nodes in the graph.
    k (int): Each node is joined with its `k` nearest neighbors in a ring topology.
    p (float): Probability of rewiring each edge.

    Returns:
    nx.Graph: A Watts-Strogatz small-world graph.
    """
   # Create an undirected Watts-Strogatz graph
    undirected_graph = nx.watts_strogatz_graph(num_nodes, k, p, seed=42)
    
    # Convert to a directed graph
    directed_graph = nx.DiGraph(undirected_graph)

    for u, v in list(directed_graph.edges()):
        if random.random() < 0.99:  # probability for edge removal
            directed_graph.remove_edge(v, u)  # Remove one direction of the edge

    return directed_graph    
def create_random_directed_graph(num_nodes, p):
    """
    Generates a random directed graph (Erdős-Rényi model).
    
    Parameters:
    num_nodes (int): Number of nodes in the graph.
    p (float): Probability of creating an edge between two nodes.
    
    Returns:
    nx.DiGraph: A random directed graph.
    """
    # Create a random graph using Erdős–Rényi model
    random_graph = nx.gnp_random_graph(num_nodes, p, seed=42, directed=True)
    return random_graph
def create_linear_directed_graph(num_nodes, extra_nodes):
    """
    Generates a linear directed graph with specified number of nodes.
    
    Parameters:
    num_nodes (int): Number of nodes in the graph, where each node has an edge to the next.
    
    Returns:
    nx.DiGraph: A linear directed graph.
    """
    G = nx.DiGraph()
    G.add_nodes_from(range(num_nodes))
    
    # Add edges for the linear path
    for i in range(num_nodes - 1):
        G.add_edge(i, i + 1)

    # Add extra random nodes
    max_node = max(G.nodes)
    for i in range(extra_nodes):
        new_node = max_node + 1 + i
        G.add_node(new_node)

        # Connect the new node to a random existing node
        random_node = random.choice(list(G.nodes))
        if random.random() < 0.5:
            # Randomly decide the direction of the edge
            G.add_edge(new_node, random_node)
        else:
            G.add_edge(random_node, new_node)

    return G
def create_complex_graph(m, X, Y, T):
    """
    Creates a complex graph based on specified parameters.
    
    Parameters:
    m (int): Number of nodes in the initial ring.
    X (int): Number of linear paths to add.
    Y (int): Size of each linear path.
    T (int): Number of additional random edges.
    
    Returns:
    nx.DiGraph: The generated complex graph.
    """
    G = nx.DiGraph()
    
    # Create a ring graph
    G.add_nodes_from(range(m))
    for i in range(m):
        G.add_edge(i, (i + 1) % m, weight=random.random())  # Ring structure
    
    # Add X linear paths of size Y
    max_node = max(G.nodes)
    for _ in range(X):
        start_node = random.choice(list(G.nodes))
        for i in range(Y):
            new_node = max_node + 1
            if random.random() < 0.5:
                G.add_edge(start_node, new_node, weight=random.random())
            else:
                G.add_edge(new_node, start_node, weight=random.random())
            start_node = new_node
            max_node = new_node
    
    # Add T random edges
    for _ in range(T):
        node_a, node_b = random.sample(G.nodes(), 2)
        if random.random() < 0.5:
            G.add_edge(node_a, node_b, weight=random.random())
        else:
            G.add_edge(node_b, node_a, weight=random.random())

    return G
def create_random_directed_graph(num_nodes, p):
    """
    Generates a random directed graph (Erdős-Rényi model) with randomly chosen edge directions
    and no self-loops.
    
    Parameters:
    num_nodes (int): Number of nodes in the graph.
    p (float): Probability of creating an edge between two nodes.
    
    Returns:
    nx.DiGraph: A random directed graph.
    """
    random_graph = nx.DiGraph()

    # Add nodes
    random_graph.add_nodes_from(range(num_nodes))

    # Add edges with random direction
    for i in range(num_nodes):
        for j in range(num_nodes):
            if i != j and random.random() < p:
                if random.random() < 0.5:
                    # Add edge with one direction
                    random_graph.add_edge(i, j)
                else:
                    # Add edge with opposite direction
                    random_graph.add_edge(j, i)

    return random_graph
def modify_graph_with_self_loops(graph, percentage=0.10):
    """
    Randomly deletes a percentage of edges and adds the same number of self-loops.
    
    Parameters:
    graph (nx.DiGraph): The directed graph to modify.
    percentage (float): Percentage of edges to delete and number of self-loops to add.
    """
    num_edges_to_remove = int(graph.number_of_edges() * percentage)
    edges = list(graph.edges())
    nodes = list(graph.nodes())

    # Randomly remove edges
    for _ in range(num_edges_to_remove):
        edge_to_remove = random.choice(edges)
        graph.remove_edge(*edge_to_remove)
        edges.remove(edge_to_remove)

    # Add self-loops
    for _ in range(num_edges_to_remove):
        node_for_self_loop = random.choice(nodes)
        graph.add_edge(node_for_self_loop, node_for_self_loop)

    return graph
def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Simple script showcasing all the functionality of Arachne on a random property\
                    graph of size specified by the user."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("nodes", type=int, default=10000, help="Port of arkouda server")

    return script_parser
if __name__ == "__main__":
    # Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()

    # Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)
        
        

    random.seed(5)  # Setting seed for reproducibility

    num_nodes = args.nodes
    #random_directed_graph = nx.DiGraph()
    """
    # Parameters for random model
    p = 0.05  # Probability of edge creation
    random_directed_graph = create_random_directed_graph(num_nodes, p)
    
    # Parameters for small-world model
    k = 4  # Number of nearest neighbors
    p = 0.1  # Rewiring probability
    random_directed_graph = create_watts_strogatz_graph(num_nodes, k, p)
    
    # Parameters for scale-free model
    m = 15  # Number of edges to attach from a new node to existing nodes
    
    # Generate a directed Barabási-Albert graph using the function
    random_directed_graph = create_barabasi_albert_graph(num_nodes, m)
    
    random_directed_graph = create_linear_directed_graph(args.nodes, 500)
    
    m = 5   # Size of the ring
    X = 5    # Number of linear paths
    Y = 100    # Size of each linear path
    T = 5000   # Number of additional random nodes
    random_directed_graph = create_complex_graph(m, X, Y, T)
    
    p = 0.05         # Probability of edge creation
    random_directed_graph_temp = create_random_directed_graph(num_nodes, p)
    random_directed_graph = modify_graph_with_self_loops(random_directed_graph_temp, 0.10)
    """
    m = 15  # Number of edges to attach from a new node to existing nodes
    
    # Generate a directed Barabási-Albert graph using the function
    random_directed_graph = create_barabasi_albert_graph(num_nodes, m)
    # Set node labels and edge labels
    nx.set_node_attributes(random_directed_graph, 'label', 'label1')
    nx.set_edge_attributes(random_directed_graph, 'label', 'Y1')

    # Create the subgraph
    subgraph_nodes = [0, 1, 2, 3]
    subgraph_edges = [(0, 1), (1, 2), (2, 0), (1, 3)]
    subgraph = nx.DiGraph()
    subgraph.add_nodes_from(subgraph_nodes)
    subgraph.add_edges_from(subgraph_edges)
    print("End of preparing data")
    print("****************************************")
    print("Number of edges:", random_directed_graph.number_of_edges())
    print("Number of nodes:", random_directed_graph.number_of_nodes())
    print()
    start_time = time.time()

    # Use DiGraphMatcher to find subgraph isomorphisms
    matcher = nx.algorithms.isomorphism.DiGraphMatcher(random_directed_graph, subgraph)
  
    subgraph_isomorphisms = list(matcher.subgraph_monomorphisms_iter())
    # Print the number of occurrences and mappings of the subgraph in the random graph

    print()
    print("Subgraph occurrences found:")

    print("NetworkX subgraph_isomorphism found ISOs:", len(subgraph_isomorphisms))
    end_time = time.time()
    elapsed_time = end_time - start_time
    print("Elapsed time:", elapsed_time, "seconds")
    print("*********************************************************************************")

    
    #print("Subgraph occurrences found:")
    #for iso_mapping in subgraph_isomorphisms:
        #print("Isomorphism mapping:", iso_mapping)
    

    
    # Extracting src and dst arrays from random_directed_graph
    edges = random_directed_graph.edges()
    src = [edge[0] for edge in edges]
    dst = [edge[1] for edge in edges]

    print("number of edges: ", len(edges))

    
    # Extracting all_nodes array
    vertex_ids = list(random_directed_graph.nodes())
    vertex_labels = ['label1'] * len(vertex_ids)
    edge_relationships = ['Y1'] * len(src)
    
    print("number of nodes: ", len(vertex_ids))
    print("Begining of loading data to Prop_Graph")
    prop_graph = ar.PropGraph()
    
    prop_graph.add_edges_from(ak.array(src),ak.array(dst))
    
    node_labels = ak.DataFrame({"vertex_ids" : ak.array(vertex_ids), 
                                "vertex_labels" : ak.array(vertex_labels)})
    edge_relationships = ak.DataFrame({"src" : ak.array(src), 
                                       "dst" : ak.array(dst), 
                    "edge_relationships" : ak.array(edge_relationships)})
    prop_graph.add_node_labels(node_labels)
    prop_graph.add_edge_relationships(edge_relationships)
    
    
    
    
    
    # Extracting src and dst arrays from H
    edgesH = subgraph.edges()
    srcH = [edge[0] for edge in edgesH]
    dstH = [edge[1] for edge in edgesH]

    print("number of edges: ", len(edgesH))

    
    # Extracting all_nodes array H
    vertex_idsH = list(subgraph.nodes())
    vertex_labelsH = ['label1'] * len(vertex_idsH)
    edge_relationshipsH = ['Y1'] * len(srcH)
    
    print("number of nodes: ", len(vertex_idsH))

    subgraph = ar.PropGraph()
    
    subgraph.add_edges_from(ak.array(srcH),ak.array(dstH))
    
    node_labelsH = ak.DataFrame({"vertex_ids" : ak.array(vertex_idsH), 
                                "vertex_labels" : ak.array(vertex_labelsH)})
    edge_relationshipsH = ak.DataFrame({"src" : ak.array(srcH), 
                                       "dst" : ak.array(dstH), 
                    "edge_relationships" : ak.array(edge_relationshipsH)})
    subgraph.add_node_labels(node_labelsH)
    subgraph.add_edge_relationships(edge_relationshipsH)
    

    print("Executing algorithm")
    start_time = time.time()

    mappings_df1 = ar.subgraph_isomorphism_VF2(prop_graph, subgraph, "VF2")
    #print(type(mappings_df)) 
    # for i in range(0, len(mappings_df1), 4):
    #     print(mappings_df1[i:i+4])

    
    # Access the DataFrame data
    print("VF2 subgraph_isomorphism run and this is the found ISOs")
    print(len(mappings_df1)/4)
    
    end_time = time.time()
    elapsed_time = end_time - start_time
    print("Elapsed time:", elapsed_time, "seconds")
    print("*********************************************************************************")

    ak.shutdown()
    



