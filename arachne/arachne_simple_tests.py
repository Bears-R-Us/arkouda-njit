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
    edges_df = ak.read_csv("/rhome/oaa9/Research/arkouda_extension/testing_files/data/property_graphs/karate_edges.csv")
    print(f"edges_csv \n= {edges_df.__repr__()}")

    # Build the graph from the read-in csv file.
    src = ak.cast(edges_df["src"], dt=ak.int64)
    dst = ak.cast(edges_df["dst"], dt=ak.int64)
    graph = ar.PropGraph()
    graph.add_edges_from(src,dst)

    # Read in the node labels from a separate csv file.
    nodes_df = ak.read_csv("/rhome/oaa9/Research/arkouda_extension/testing_files/data/property_graphs/karate_nodes.csv")
    node_ids = ak.cast(nodes_df["node"], dt=ak.int64)
    node_labels = nodes_df["label"]
    node_label_dataframe = ak.DataFrame({"nodeIDs" : node_ids, "nodeLabels" : node_labels})
    graph.add_node_labels(node_label_dataframe)

    # Read in the edge relationships from file used above.
    edge_relationships = edges_df["relationship"]
    edge_relationship_dataframe = ak.DataFrame({"src" : src, "dst" : dst, "edgeRelationships" : edge_relationships})
    graph.add_edge_relationships(edge_relationship_dataframe)

    # Read in the node properties from a separate csv file.
    node_prop_df = ak.read_csv("/rhome/oaa9/Research/arkouda_extension/testing_files/data/property_graphs/karate_node_properties.csv")
    node_ids = ak.cast(nodes_df["node"], dt=ak.int64)
    prop1 = node_prop_df["type"]
    prop2 = node_prop_df["age"]
    node_prop_dataframe = ak.DataFrame({"nodeIDs" : node_ids, "type" : prop1, "age" : prop2})
    graph.add_node_properties(node_prop_dataframe)

    # Read in the node properties from a separate csv file.
    edge_prop_df = ak.read_csv("/rhome/oaa9/Research/arkouda_extension/testing_files/data/property_graphs/karate_edge_properties.csv")
    src = ak.cast(edge_prop_df["src"], dt=ak.int64)
    dst = ak.cast(edge_prop_df["dst"], dt=ak.int64)
    prop1 = edge_prop_df["team"]
    prop2 = edge_prop_df["since"]
    edge_prop_dataframe = ak.DataFrame({"src" : src, "dst" : dst, "team" : prop1, "since" : prop2})
    graph.add_edge_properties(edge_prop_dataframe)

    # Let us do some querying of data!
    graph.query(
        nodes_to_find = ak.array([1,2]),
        edges_to_find = (ak.array([20,22]),ak.array([2,2])),
        labels_to_find = ak.array(["student"]),
        relationships_to_find = ak.array(["friends", "coworkers"])
    )

    # # Build graph from an array.
    # src = ak.array([34, 23, 34, 23, 23, 89])
    # dst = ak.array([23, 34, 89, 89, 89, 89])
    # wgt = ak.array([98, 12, 13, .4, 23, 12])
    # graph = ar.PropGraph()
    # graph.add_edges_from(src, dst, wgt)

    # # Add node labels to the property graph.
    # node_ids = ak.array([23, 34, 89, 89])
    # node_labels = ak.array(["Person", "Person", "Vehicle", "Car"])
    # node_label_dataframe = ak.DataFrame({"nodeIDs" : node_ids, "nodeLabels" : node_labels})
    # graph.add_node_labels(node_label_dataframe)
    # print("Successfully added node labels.")

    # # Add the edge relationships to the property graph.
    # edge_relationships = ak.array(["lives-with", "lives-with", "drives", "drives", "owns", "drives"])
    # edge_relationship_dataframe = ak.DataFrame({"src" : src, "dst" : dst, "edgeRelationships" : edge_relationships})
    # graph.add_edge_relationships(edge_relationship_dataframe)
    # print("Successfully added edge relationships.")

    # # Add the node properties to the property graph.
    # # First, we need properties for the nodes labeled as "Person".
    # person_names = ak.array([34, 23])
    # person_property_name = ak.array(["Ann", "Dan"])
    # person_property_born = ak.array(["05-29-1990", "12-05-1975"])
    # # Second, we need properties for the nodes labeled as "Vehicle" and "Car".
    # vehicle_names = ak.array([89])
    # vehicle_property_brand = ak.array(["Tesla"])
    # vehicle_property_model = ak.array(["Model X"])
    # # Now, we send each to a dataframe and add them independently to our property graph.
    # person_node_properties = ak.DataFrame({"nodeIDs" : person_names, "name" : person_property_name, "born" : person_property_born})
    # vehicle_node_properties = ak.DataFrame({"nodeIDs" : vehicle_names, "brand" : vehicle_property_brand, "model" : vehicle_property_model})
    # graph.add_node_properties(person_node_properties)
    # print("Successfully added person node properties.")
    # graph.add_node_properties(vehicle_node_properties)
    # print("Successfully added vehicle node properties.")

    # # Add the edge properties to the property graphs.
    # # First, we will add the edge properties for the edges with relationship "drives".
    # drives_src = ak.array([34, 23, 89])
    # drives_dst = ak.array([89, 89, 89])
    # drives_property_since = ak.array(["01-10-2011", "01-10-2011", "NULL"])
    # # Second, we will add the edge properties for the edges with relationships "owns".
    # owns_src = ak.array([23])
    # owns_dst = ak.array([89])
    # owns_property_registered = ak.array(["01-10-2011"])
    # # Now, we send each to a dataframe and add them independently to our property graph.
    # drives_edge_properties = ak.DataFrame({"src" : drives_src, "dst" : drives_dst, "since" : drives_property_since})
    # owns_edge_properties = ak.DataFrame({"src" : owns_src, "dst" : owns_dst, "registered" : owns_property_registered})
    # graph.add_edge_properties(drives_edge_properties)
    # print("Successfully added drives edge properties.")
    # graph.add_edge_properties(owns_edge_properties)
    # print("Successfully added owns edge properties.")
    # print()

    # # Now, below let's make filters with Arkouda for labels, relationships, and properties.
    # # First, we make filters for all the node labels that contain the value Person.
    # indices = node_label_dataframe["nodeLabels"] == "Person"
    # node_label_filter = node_label_dataframe[indices]["nodeIDs"]
    # print("Nodes with label Person =", node_label_filter)
    # print()

    # # Second, let's make filters for all the edge relationships that contain the value drives.
    # indices = edge_relationship_dataframe["edgeRelationships"] == "drives"
    # edge_relationship_filter = edge_relationship_dataframe[indices]["src","dst"]
    # print("Edges with relationship drives =\n", edge_relationship_filter.__repr__())
    # print()

    # # Third, let's make filters for all the nodes born in December.
    # indices = person_node_properties["born"].contains("12-")
    # node_property_filter = person_node_properties[indices]["nodeIDs"]
    # print("Nodes with property born in December =", node_property_filter)
    # print()

    # # Fourth, and lastly, let's make a filter for all the edges with property since starting in 2011.
    # indices = drives_edge_properties["since"].contains("-2011")
    # edge_property_filter = drives_edge_properties[indices]["src", "dst"]
    # print("Edges with property since from 2011 =\n", edge_property_filter.__repr__())
    # print()

    # subgraph = ar.subgraph_view(graph, ar.Graph(), filter_labels=node_label_filter, filter_relationships=edge_relationship_filter, filter_node_properties=node_property_filter, filter_edge_properties=edge_property_filter)
    # print(graph.edges())
    # print(subgraph.edges())

    ak.shutdown()