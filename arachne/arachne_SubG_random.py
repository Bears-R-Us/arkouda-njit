"""Sample Arachne Script for Property Graphs

This script provides an example on how a graph is built in Arachne from two Arkouda arrays and then
analyzed using Arachne functions. The graphs are randomly generated by using the ak.randint function
with the range of the vertex names being picked from 0..<n and the number of edges m. No special
distribution is used to generated the graph e.g. RMAT. We also generate random strings to behave
as relationships and labels for the property graphs.

The values of n and m are accepted from command line input. It requires Arkouda and Arachne to both
be pip installed in the environment. 

Assumes Arkouda server is running. It will shutdown the Arkouda server upon completion.

Sample usage: python3 arachne_simple_tests.py n51 5555 5000 20000

"""
import argparse
import time
import arkouda as ak
import arachne as ar
import networkx as nx
import random


def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Simple script showcasing all the functionality of Arachne on a random property\
                    graph of size specified by the user."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    script_parser.add_argument("m", type=int, default=2000, help="Number of edges for graph")
    script_parser.add_argument("x", type=int, default=5, help="Number of labels for graph")
    script_parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")

    return script_parser
if __name__ == "__main__":
    # Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()

    # Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)
        
        

    # Create a random directed graph with nodes in the range 100 to 200
    random.seed(5)  # Setting seed for reproducibility
    #num_nodes = random.randint(0, 100000)
    num_nodes = 500000
    random_directed_graph = nx.DiGraph()

    # Add nodes to the graph

    random_edges_per_node = [random.randint(5,10) for _ in range(num_nodes)]  # Random edges per node
    random_directed_graph.add_nodes_from(range(num_nodes))

    # Add directed edges with random weights
    for i in range(num_nodes):
        for _ in range(random_edges_per_node[i]):
            if random.random() < 0.5:  # Adjusted probability for edge creation (denser graph)
                j = random.randint(0, num_nodes - 1)  # Random destination node
                random_directed_graph.add_edge(i, j, weight=random.random())
                #print(i, j)
    


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
    print()
    
    start_time = time.time()

    # Use DiGraphMatcher to find subgraph isomorphisms
    matcher = nx.algorithms.isomorphism.DiGraphMatcher(random_directed_graph, subgraph)
  
    subgraph_isomorphisms = list(matcher.subgraph_monomorphisms_iter())
    # Print the number of occurrences and mappings of the subgraph in the random graph

    print()
    print("Subgraph occurrences found:")
    for iso_mapping in subgraph_isomorphisms:
        print("Isomorphism mapping:", iso_mapping)
    print("NetworkX subgraph_isomorphism found ISOs:", len(subgraph_isomorphisms))
    end_time = time.time()
    elapsed_time = end_time - start_time
    print("Elapsed time:", elapsed_time, "seconds")
    print("*********************************************************************************")

    
    #print("Subgraph occurrences found:")
    #for iso_mapping in subgraph_isomorphisms:
        #print("Isomorphism mapping:", iso_mapping)
    
    print("Number of edges:", random_directed_graph.number_of_edges())
    print("Number of nodes:", random_directed_graph.number_of_nodes())
    print()
    
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
    for i in range(0, len(mappings_df1), 4):
        print(mappings_df1[i:i+4])

    
    # Access the DataFrame data
    print("VF2 subgraph_isomorphism run and this is the found ISOs")
    print(len(mappings_df1))
    
    end_time = time.time()
    elapsed_time = end_time - start_time
    print("Elapsed time:", elapsed_time, "seconds")
    print("*********************************************************************************")
    
    """
    start_time = time.time()

    mappings_df = ar.subgraph_isomorphism(prop_graph, subgraph, "ullmann")
    #print(type(mappings_df)) 
    # Access the DataFrame data
    print("Ullmann subgraph_isomorphism run and this is the found ISOs")
    print(mappings_df)
    print(len(mappings_df))
    
    end_time = time.time()
    elapsed_time = end_time - start_time
    print("Elapsed time:", elapsed_time, "seconds")
    print("*********************************************************************************")
    """
    ak.shutdown()
    



