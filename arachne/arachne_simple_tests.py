import argparse
import arkouda as ak
import arachne as ar 
import numpy as np

def create_parser():
    parser = argparse.ArgumentParser(
        description="Measure the performance of breadth-first search on a graph. Must be preprocessed!"
    )
    parser.add_argument("hostname", help="Hostname of arkouda server")
    parser.add_argument("port", type=int, help="Port of arkouda server")
    
    return parser

if __name__ == "__main__":    
    parser = create_parser()
    args = parser.parse_args()
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    # Read in edges and their features first, to build the graph from those edges.
    edges_df = ak.read_csv("/scratch/users/oaa9/testing_files/simple/property_graphs/karate_edges.csv")
    # print(f"edges_csv \n= {edges_df.__repr__()}")

    # Build the graph from the read-in csv file.
    src = ak.cast(edges_df["src"], dt=ak.int64)
    dst = ak.cast(edges_df["dst"], dt=ak.int64)
    graph = ar.PropGraph()
    graph.add_edges_from(src,dst)

    # Read in the node labels from a separate csv file.
    nodes_df = ak.read_csv("/scratch/users/oaa9/testing_files/simple/property_graphs/karate_nodes.csv")
    node_ids = ak.cast(nodes_df["node"], dt=ak.int64)
    node_labels = nodes_df["label"]
    node_label_dataframe = ak.DataFrame({"nodeIDs" : node_ids, "nodeLabels" : node_labels})

    # Read in the edge relationships from file used above.
    edge_relationships = edges_df["relationship"]
    edge_relationship_dataframe = ak.DataFrame({"src" : src, "dst" : dst, "edgeRelationships" : edge_relationships})

    # Read in the node properties from a separate csv file.
    node_prop_df = ak.read_csv("/scratch/users/oaa9/testing_files/simple/property_graphs/karate_node_properties.csv")
    node_ids = ak.cast(nodes_df["node"], dt=ak.int64)
    prop1 = node_prop_df["type"]
    prop2 = node_prop_df["age"]
    node_prop_dataframe = ak.DataFrame({"nodeIDs" : node_ids, "type" : prop1, "age" : prop2})

    # Read in the node properties from a separate csv file.
    edge_prop_df = ak.read_csv("/scratch/users/oaa9/testing_files/simple/property_graphs/karate_edge_properties.csv")
    src = ak.cast(edge_prop_df["src"], dt=ak.int64)
    dst = ak.cast(edge_prop_df["dst"], dt=ak.int64)
    prop1 = edge_prop_df["team"]
    prop2 = edge_prop_df["since"]
    edge_prop_dataframe = ak.DataFrame({"src" : src, "dst" : dst, "team" : prop1, "since" : prop2})

    # Insert attributes into a property graph using the singly linked list method.
    graph.add_node_labels(node_label_dataframe, "DipSLLaddNodeLabels")
    graph.add_edge_relationships(edge_relationship_dataframe, "DipSLLaddEdgeRelationships")
    graph.add_node_properties(node_prop_dataframe, "DipSLLaddNodeProperties")
    graph.add_edge_properties(edge_prop_dataframe, "DipSLLaddEdgeProperties")

    # Querying with DipSLLquery:
    graph.query(
        "DipSLLquery",
        nodes_to_find = ak.array([1,2]),
        edges_to_find = (ak.array([20,22]),ak.array([2,2])),
        labels_to_find = ak.array(["student"]),
        relationships_to_find = ak.array(["friends", "coworkers"])
        # node_properties_to_find = ak.array(["age"]),
        # edge_properties_to_find = ak.array(["team"])
    )

    # Insert attributes into a property graph using the two-dimensional array method.
    graph.add_node_labels(node_label_dataframe, "DipArrayaddNodeLabels")
    graph.add_edge_relationships(edge_relationship_dataframe, "DipArrayaddEdgeRelationships")

    # Querying with DipARRquery:
    graph.query(
        "DipArrayquery",
        nodes_to_find = ak.array([1,2]),
        edges_to_find = (ak.array([20,22]),ak.array([2,2])),
        labels_to_find = ak.array(["student"]),
        relationships_to_find = ak.array(["friends", "coworkers"])
        # node_properties_to_find = ak.array(["age"]),
        # edge_properties_to_find = ak.array(["team"])
    )

    # Insert attributes into a property graph using the doubly linked list method.
    graph.add_node_labels(node_label_dataframe, "DipDLLaddNodeLabels")
    graph.add_edge_relationships(edge_relationship_dataframe, "DipDLLaddEdgeRelationships")
    
    # Querying with DipDLLquery:
    graph.query(
        "DipDLLquery",
        nodes_to_find = ak.array([1,2]),
        edges_to_find = (ak.array([20,22]),ak.array([2,2])),
        labels_to_find = ak.array(["student"]),
        relationships_to_find = ak.array(["friends", "coworkers"])
        # node_properties_to_find = ak.array(["age"]),
        # edge_properties_to_find = ak.array(["team"])
    )

    ak.shutdown()