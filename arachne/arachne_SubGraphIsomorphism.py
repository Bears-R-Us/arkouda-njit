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
    """
    ### Build graph from randomly generated source and destination arrays.
    # 1. Use Arkouda's randint to generate the random edge arrays.
    src = ak.randint(0, args.n, args.m, seed=2048)
    dst = ak.randint(0, args.n, args.m, seed=1024)

    # 2. Build property graph.
    start = time.time()
    prop_graph = ar.PropGraph()
    ################################################################################
    
    src= ak.array([2, 3, 5, 6, 7, 9])
    dst= ak.array([5, 6, 1, 6, 9, 2, 7, 10, 3, 8])
    ################################################################################

    prop_graph.add_edges_from(src, dst)
    end = time.time()
    print(f"Building property graph with {len(prop_graph)} vertices and {prop_graph.size()} "
          f"edges took {end-start} seconds.")

    ### Populate property graph with vertex labels.
    # 1. Generate labels.
    LBL = "label"
    #labels = [LBL + str(x) for x in range(args.x)]
    ###############################################################################
    lables=["1", "2", "3", "4", "5", "6", "7", "8", "9", "10"]
    ###############################################################################
    labels = ak.array(labels)

    # 2. Generate random array of vertices with original vertex values.
    vertices = prop_graph.nodes()
    vertices_with_labels = ak.randint(0, len(prop_graph), len(prop_graph), seed=512)
    
    vertices_with_labels = vertices[vertices_with_labels]

    # 3. Generate random array of labels of the same size as the random array of vertices above.
    random_labels = ak.randint(0, len(labels), len(vertices_with_labels), seed=256)
    random_labels = labels[random_labels]

    # 4. Pack the values into a dataframe and populate them into the graph.
    label_df = ak.DataFrame({"vertex_ids" : vertices_with_labels, "vertex_labels" : random_labels})
    start = time.time()
    
    #prop_graph.add_node_labels(label_df, "DipSLLaddNodeLabels")
    prop_graph.add_node_labels(label_df)
    
    end = time.time()
    print(f"Populating property graph with {len(random_labels)} labels took {end-start} seconds.")

    ### Populate property graph with edge relationships.
    # 1. Generate labels.
    #REL = "relationship"
    #relationships = [REL + str(y) for y in range(args.y)]
    ##########################################################################
    relationships = ["Y", "Y", "B", "R", "W", "G", "R", "W", "G", "B"]
    ############################################################################
    relationships = ak.array(relationships)

    # 2. Generate random array of edges with original vertex values.
    edges_with_relationships = ak.randint(0, len(src), len(src), seed=128)
    src_vertices_with_relationships = src[edges_with_relationships]
    dst_vertices_with_relationships = dst[edges_with_relationships]

    # 3. Generate random array of relationships of the same size as the random array of edges above.
    random_relationships = ak.randint(0, len(relationships), len(edges_with_relationships), seed=64)
    random_relationships = relationships[random_relationships]

    # 4. Pack the values into a dataframe and populate them into the graph.
    relationships_df = ak.DataFrame({"src" : src_vertices_with_relationships, "dst" : dst_vertices_with_relationships, "edge_relationships" : random_relationships})
    start = time.time()
    prop_graph.add_edge_relationships(relationships_df)
    end = time.time()
    print(f"Populating property graph with {len(random_relationships)} relationships took {end-start} seconds.")
    """
    prop_graph = ar.PropGraph()
    
    src= ak.array([101, 102, 104, 104, 104, 105, 105, 105, 106, 108])
    dst= ak.array([104, 105, 100, 105, 108, 101, 106, 109, 102, 107])
    
    prop_graph.add_edges_from(src,dst)
    node_labels = ak.DataFrame({"vertex_ids" : ak.array([100,101,102,103,104,105,106,107,108,109]), 
                                "vertex_labels" : ak.array(["label1", "label1", "label1", "label1", "label1", "label1", "label1", "label1", "label1", "label1"])})
    
    edge_relationships = ak.DataFrame({"src" : ak.array([101, 102, 104, 104, 104, 105, 105, 105, 106, 108]), 
                                       "dst" : ak.array([104, 105, 100, 105, 108, 101, 106, 109, 102, 107]), "edge_relationships" : 
        ak.array(["Y1", "Y1", "Y4", "Y2", "Y4", "Y3", "Y1", "Y1", "Y1", "Y1"])})
    
    prop_graph.add_node_labels(node_labels)
    prop_graph.add_edge_relationships(edge_relationships)
    
    ### Test subgraph isomorphism.
    subgraph = ar.PropGraph()
    
    src1= ak.array([20, 21, 21, 22])
    dst1= ak.array([21, 22, 23 ,20])
    
    subgraph.add_edges_from(src1,dst1)
    node_labels = ak.DataFrame({"vertex_ids" : ak.array([20, 21, 22, 23]), 
                                "vertex_labels" : ak.array(["label1", "label1", "label1", "label1"])})
    edge_relationships = ak.DataFrame({"src" : ak.array([20, 21, 21, 22]), 
                                       "dst" : ak.array([21, 22, 23 ,20]), 
                    "edge_relationships" : ak.array(["Y1", "Y2", "Y4", "Y3"])})
    subgraph.add_node_labels(node_labels)
    subgraph.add_edge_relationships(edge_relationships)
    
    
    ar.subgraph_isomorphism(prop_graph, subgraph, "ullmann")

    ak.shutdown()