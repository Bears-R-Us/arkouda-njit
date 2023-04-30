from base_test import ArkoudaTest
import arkouda as ak
import arachne as ar
import scipy as sp
import scipy.io
import pathlib
import networkx as nx

class ReadingTest(ArkoudaTest):
    def test_read_known_edgelist(self):
        # Parse out paths where benchmark files are to be held. 
        curr_path = str(pathlib.Path(__file__).parent.resolve())
        curr_path = curr_path.rsplit("/", 1)[0] + "/"
        filepath = curr_path + "data/karate.mtx"
        only_filepath = curr_path + "data/"
        only_filename = filepath.rsplit("/", 1)[1]
        only_extension = filepath.rsplit(".", 1)[1]

        # Parse out metadata for test files from information txt file. 
        weighted = False
        directed = False
        for line in open(only_filepath + "info.txt"):
            if line[0] == "#":
                continue
            
            text = line.split()

            if text[0] == only_filename:
                directed = bool(int(text[1]))
                weighted = bool(int(text[2]))

        # Read in the graph with Arachne. 
        G = ar.read_known_edgelist(78, 34, filepath, directed=directed, weighted=weighted, filetype=only_extension)

        # Read in graph with NetworkX.
        fh = open(filepath, "rb")
        H = nx.from_scipy_sparse_array(sp.io.mmread(fh))

        # (num_vertices, num_edges) tuples for comparison.
        ar_tuple = (len(G), G.size())
        nx_tuple = (len(H), H.size())

        return self.assertEqual(ar_tuple, nx_tuple)

    def test_read_edgelist(self):
        # Parse out paths where benchmark files are to be held. 
        curr_path = str(pathlib.Path(__file__).parent.resolve())
        curr_path = curr_path.rsplit("/", 1)[0] + "/"
        filepath = curr_path + "data/karate.mtx"
        only_filepath = curr_path + "data/"
        only_filename = filepath.rsplit("/", 1)[1]
        only_extension = filepath.rsplit(".", 1)[1]

        # Parse out metadata for test files from information txt file. 
        weighted = False
        directed = False
        for line in open(only_filepath + "info.txt"):
            if line[0] == "#":
                continue
            
            text = line.split()

            if text[0] == only_filename:
                directed = bool(int(text[1]))
                weighted = bool(int(text[2]))

        # Read in the graph with Arachne. 
        G = ar.read_edgelist(filepath, directed=directed, weighted=weighted, filetype=only_extension)

        # Read in graph with NetworkX.
        fh = open(filepath, "rb")
        H = nx.from_scipy_sparse_array(sp.io.mmread(fh))

        # (num_vertices, num_edges) tuples for comparison.
        ar_tuple = (len(G), G.size())
        nx_tuple = (len(H), H.size())

        return self.assertEqual(ar_tuple, nx_tuple)
    
    def test_subgraph_view(self):
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
        print()

        # Now, below let's make filters with Arkouda for labels, relationships, and properties.
        # First, we make filters for all the node labels that contain the value Person.
        A = ak.arange(0, len(node_label_dataframe), 1)
        indices = node_label_dataframe["nodeLabels"] == "Person"
        node_label_filter = node_label_dataframe[indices]["nodeIDs"]
        print("Nodes with label Person =", node_label_filter)
        print()

        # Second, let's make filters for all the edge relationships that contain the value drives.
        A = ak.arange(0, len(edge_relationship_dataframe), 1)
        indices = edge_relationship_dataframe["edgeRelationships"] == "drives"
        edge_relationship_filter = edge_relationship_dataframe[indices]["src","dst"]
        print("Edges with relationship drives =\n", edge_relationship_filter.__repr__())
        print()

        # Third, let's make filters for all the nodes born in December.
        A = ak.arange(0, len(person_node_properties), 1)
        indices = person_node_properties["born"].contains("12-")
        node_property_filter = person_node_properties[indices]["nodeIDs"]
        print("Nodes with property born in December =", node_property_filter)
        print()

        # Fourth, and lastly, let's make a filter for all the edges with property since starting in 2011.
        A = ak.arange(0, len(drives_edge_properties), 1)
        indices = drives_edge_properties["since"].contains("-2011")
        edge_property_filter = drives_edge_properties[indices]["src", "dst"]
        print("Edges with property since from 2011 =\n", edge_property_filter.__repr__())
        print()

        subgraph = ar.subgraph_view(graph, ar.Graph(), filter_labels=node_label_filter, filter_relationships=edge_relationship_filter, filter_node_properties=node_property_filter, filter_edge_properties=edge_property_filter)
        graph = ar.Graph()
        graph.add_edges_from(src, dst)

        edges_graph = graph.edges()
        src_graph = edges_graph[0]
        dst_graph = edges_graph[1]

        edges_subgraph = subgraph.edges()
        src_subgraph = edges_subgraph[0]
        dst_subgraph = edges_subgraph[1]

        src_test = self.assertEqual(src_graph.to_list(), src_subgraph.to_list())
        dst_test = self.assertEqual(dst_graph.to_list(), dst_subgraph.to_list())

        return self.assertEqual(src_test, dst_test)
