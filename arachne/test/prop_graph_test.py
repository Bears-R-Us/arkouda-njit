from base_test import ArkoudaTest
import filecmp
import arkouda as ak
import arachne as ar
import scipy as sp
import scipy.io
import pathlib
import networkx as nx

class PropGraphTest(ArkoudaTest):
    def test_adding_methods(self):
        # Build graph from an array.
        src = ak.array([34, 23, 34, 23, 23, 89])
        dst = ak.array([23, 34, 89, 89, 89, 89])
        wgt = ak.array([98, 12, 13, .4, 23, 12])
        graph = ar.PropGraph()
        graph.add_edges_from(src, dst, wgt)

        # Add node labels to the property graph.
        node_ids = ak.array([23, 34, 89, 89])
        node_labels = ak.array(["Person", "Person", "Vehicle", "Car"])
        node_label_dataframe = ak.DataFrame({"nodeIDs" : node_ids, "nodeLabels" : node_labels})
        graph.add_node_labels(node_label_dataframe)
        print("Successfully added node labels.")

        # Add the edge relationships to the property graph.
        edge_relationships = ak.array(["lives-with", "lives-with", "drives", "drives", "owns", "drives"])
        edge_relationship_dataframe = ak.DataFrame({"src" : src, "dst" : dst, "edgeRelationships" : edge_relationships})
        graph.add_edge_relationships(edge_relationship_dataframe)
        print("Successfully added edge relationships.")

        # Add the node properties to the property graph.
        # First, we need properties for the nodes labeled as "Person".
        person_names = ak.array([34, 23])
        person_property_name = ak.array(["Ann", "Dan"])
        person_property_born = ak.array(["05-29-1990", "12-05-1975"])
        # Second, we need properties for the nodes labeled as "Vehicle" and "Car".
        vehicle_names = ak.array([89])
        vehicle_property_brand = ak.array(["Tesla"])
        vehicle_property_model = ak.array(["Model X"])
        # Now, we send each to a dataframe and add them independently to our property graph.
        person_node_properties = ak.DataFrame({"nodeIDs" : person_names, "name" : person_property_name, "born" : person_property_born})
        vehicle_node_properties = ak.DataFrame({"nodeIDs" : vehicle_names, "brand" : vehicle_property_brand, "model" : vehicle_property_model})
        graph.add_node_properties(person_node_properties)
        print("Successfully added person node properties.")
        graph.add_node_properties(vehicle_node_properties)
        print("Successfully added vehicle node properties.")

        # Add the edge properties to the property graphs.
        # First, we will add the edge properties for the edges with relationship "drives".
        drives_src = ak.array([34, 23, 89])
        drives_dst = ak.array([89, 89, 89])
        drives_property_since = ak.array(["01-10-2011", "01-10-2011", "NULL"])
        # Second, we will add the edge properties for the edges with relationships "owns".
        owns_src = ak.array([23])
        owns_dst = ak.array([89])
        owns_property_registered = ak.array(["01-10-2011"])
        # Now, we send each to a dataframe and add them independently to our property graph.
        drives_edge_properties = ak.DataFrame({"src" : drives_src, "dst" : drives_dst, "since" : drives_property_since})
        owns_edge_properties = ak.DataFrame({"src" : owns_src, "dst" : owns_dst, "registered" : owns_property_registered})
        graph.add_edge_properties(drives_edge_properties)
        print("Successfully added drives edge properties.")
        graph.add_edge_properties(owns_edge_properties)
        print("Successfully added owns edge properties.")
        
        curr_path = str(pathlib.Path(__file__).parent.resolve())
        curr_path = curr_path.rsplit("/", 1)[0] + "/"
        filepath = curr_path + "data/prop_graph_arrays.txt"
        graph.write_graph_arrays_to_file(filepath)

        filepath_ground_truth = curr_path + "data/prop_graph_ground_truth.txt"

        f1 = filecmp.cmp(filepath, filepath_ground_truth)
        f2 = filecmp.cmp(filepath, filepath_ground_truth)

        self.assertEqual(f1, f2)