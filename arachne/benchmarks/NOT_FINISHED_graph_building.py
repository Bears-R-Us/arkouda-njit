"""Sample Arachne Script

This script provides an example on how a graph is built in Arachne from two Arkouda arrays and then
analyzed using Arachne functions. The graphs are randomly generated by using the ak.randint function
with the range of the vertex names being picked from 0..<n and the number of edges m. No special
distribution is used to generated the graph e.g. RMAT. Further, these graphs are population with 
labels and relationships picked from x random labels and y random relationships.

The values of n and m are accepted from command line input and they denote the size of the graph. 
The values of x and y are accepted from the command line input and they denote the number of labels 
and relationships, respectively that the graph will contain. It requires Arkouda and Arachne to both
be pip installed in the environment. 

Assumes Arkouda server is running. It will shutdown the Arkouda server upon completion.

Sample usage: python3 arachne_simple_tests.py n51 5555 5000 20000 10 10

"""
import argparse
import time
import arkouda as ak
import arachne as ar
import networkx as nx

def create_parser():
    """Creates the command line parser for this script"""
    parser = argparse.ArgumentParser(
        description="Simple script showcasing all the functionality of Arachne on a random graph of\
                     size specified by the user."
    )
    parser.add_argument("hostname", help="Hostname of arkouda server")
    parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    parser.add_argument("n", "-n", type=int, default=1000, help="Number of vertices for graph")
    parser.add_argument("m", "-m", type=int, default=2000, help="Number of edges for graph")
    parser.add_argument("x", "-x", type=int, default=5, help="Number of labels for graph")
    parser.add_argument("y", "-y", type=int, default=10, help="Number of relationships for graph")

    return parser

def nx_bfs_to_ar_bfs(nx_bfs, ar_graph, array_size):
    """Helper function to convert NetworkX BFS to Arachne BFS"""
    vertices = ar_graph.nodes().to_list()
    nx_layer_dict = dict(enumerate(nx_bfs))
    nx_layers = [-1] * array_size
    for layer,vertices_at_layer in nx_layer_dict.items():
        for vertex in vertices_at_layer:
            nx_layers[vertices.index(vertex)] = layer
    return nx_layers

if __name__ == "__main__":
    # Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()

    # Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    ### Build graph from randomly generated source and destination arrays.
    # 1. Use Arkouda's randint to generate the random edge arrays.
    src = ak.randint(0, args.n, args.m)
    dst = ak.randint(0, args.n, args.m)

    # 2. Build undirected graph.
    print("### Arachne Graph Building")
    start = time.time()
    graph = ar.Graph()
    graph.add_edges_from(src, dst)
    end = time.time()
    print(f"Building undirected graph with {len(graph)} vertices and {graph.size()} edges "
          f"took {end-start} seconds")

    # 3. Build directed graph.
    start = time.time()
    di_graph = ar.DiGraph()
    di_graph.add_edges_from(src, dst)
    end = time.time()
    print(f"Building directed graph with {len(di_graph)} vertices and {di_graph.size()} "
          f"edges took {end-start} seconds")
    print()

    # 4. Build property graph.
    prop_graph = ar.PropGraph()
    start = time.time()
    prop_graph.add_edges_from(src, dst)
    end = time.time()
    build_time = end - start
    print(f"Building property graph with {len(prop_graph)} vertices and {prop_graph.size()} "
          f"edges took {round(build_time,2)} seconds.")
    
    ### Populate property graph with vertex labels.
    # 1. Generate labels.
    LBL = "label"
    labels_list = [LBL + str(x) for x in range(args.x)]
    labels = ak.array(labels_list)

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
    prop_graph.add_node_labels(label_df)
    end = time.time()
    add_labels_time = end - start
    print(f"Populating property graph with {len(random_labels)} labels took "
          f"{round(add_labels_time,2)} seconds.")
    


    ### NetworkX graphs for comparison.
    print("### NetworkX Graph Building")
    # 1. Build NetworkX undirected graph.
    ebunch = list(zip(src.to_list(),dst.to_list()))
    nx_graph = nx.Graph()
    start = time.time()
    nx_graph.add_edges_from(ebunch)
    end = time.time()
    print(f"Building undirected graph with {len(nx_graph)} vertices and {nx_graph.size()} edges "
          f"took {end-start} seconds")

    # 2. Build NetworkX directed graph.
    start = time.time()
    nx_di_graph = nx.DiGraph()
    end = time.time()
    nx_di_graph.add_edges_from(ebunch)
    print(f"Building directed graph with {len(nx_di_graph)} vertices and {nx_di_graph.size()} "
          f"edges took {end-start} seconds")
    print()

    print("Arachne Breadth-First Search")
    ### Run Arachne breadth-first search on the input graphs.
    # 1a. BFS on undirected graph.
    start = time.time()
    graph_bfs_layers = ar.bfs_layers(graph, 9)
    end = time.time()
    print(f"Running breadth-first search on undirected graph took {end-start} seconds")

    # 2a. BFS on directed graph.
    start = time.time()
    di_graph_bfs_layers = ar.bfs_layers(di_graph, 9)
    end = time.time()
    print(f"Running breadth-first search on directed graph took {end-start} seconds")
    print()

    print("NetworkX Breadth-First Search")
    ### Run NetworkX breadth-first search on the input graphs.
    # 1a. BFS on undirected graph.
    start = time.time()
    nx_graph_bfs_layers = nx.bfs_layers(nx_graph, 9)
    end = time.time()
    print(f"Running breadth-first search on undirected graph took {end-start} seconds")

    # 2a. BFS on directed graph.
    start = time.time()
    nx_di_graph_bfs_layers = nx.bfs_layers(nx_di_graph, 9)
    end = time.time()
    print(f"Running breadth-first search on directed graph took {end-start} seconds")
    print()

    ### Compare Arachne BFS to NetworkX BFS.
    list_graph_bfs_layers = graph_bfs_layers.to_list()
    list_di_graph_bfs_layers = di_graph_bfs_layers.to_list()
    list_nx_graph_bfs_layers = nx_bfs_to_ar_bfs(nx_graph_bfs_layers,
                                                graph,
                                                len(graph_bfs_layers))
    list_nx_di_graph_bfs_layers = nx_bfs_to_ar_bfs(nx_di_graph_bfs_layers,
                                                   di_graph,
                                                   len(di_graph_bfs_layers))

    if list_graph_bfs_layers == list_nx_graph_bfs_layers:
        print("Undirected graph BFS match!")
    else:
        print("Error: Undirected graph BFS do not match!")

    if list_di_graph_bfs_layers == list_nx_di_graph_bfs_layers:
        print("Directed graph BFS match!")
    else:
        print("Error: Directed graph BFS do not match!")

    ### Property graph operations.
    # 1. Query labels.

    # 2. Query relationships.

    # 3. Run one_path function that returns paths of length one (edges) that match the queries.

    ak.shutdown()
