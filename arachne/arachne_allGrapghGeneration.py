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
    return nx.barabasi_albert_graph(num_nodes, m, seed=42, create_using=nx.DiGraph())

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
    Generates a random directed graph (Erdős–Rényi model).
    
    Parameters:
    num_nodes (int): Number of nodes in the graph.
    p (float): Probability of creating an edge between two nodes.
    
    Returns:
    nx.DiGraph: A random directed graph.
    """
    # Create a random graph using Erdős–Rényi model
    random_graph = nx.gnp_random_graph(num_nodes, p, seed=42, directed=True)
    return random_graph

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

    # Parameters for random model
    p = 0.05  # Probability of edge creation
    random_directed_graph = create_random_directed_graph(num_nodes, p)
    """
    # Parameters for small-world model
    k = 4  # Number of nearest neighbors
    p = 0.1  # Rewiring probability
    random_directed_graph = create_watts_strogatz_graph(num_nodes, k, p)
    
    # Parameters for scale-free model
    m = 2  # Number of edges to attach from a new node to existing nodes

    # Generate a directed Barabási-Albert graph using the function
    random_directed_graph = create_barabasi_albert_graph(num_nodes, m)
    """

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
    



