from base_test import ArkoudaTest
import arachne as ar
import arkouda as ak
import networkx as nx
import pandas as pd

class PropGraphTest(ArkoudaTest):
    """Test property graph functionality."""
    def build_prop_graph(self):
        """Builds undirected and weighted graphs in both Arachne and NetworkX for tests."""
        graph = ar.PropGraph()
        m, n, k = 10, 10, 2

        src_array = ak.randint(0, n, m, dtype=ak.dtype('int64'), seed=2)
        dst_array = ak.randint(0, n, m, dtype=ak.dtype('int64'), seed=4)
        int_array = ak.randint(-1, k, m, dtype=ak.dtype('int64'), seed=6)
        uint_array = ak.randint(0, k, m, dtype=ak.dtype('uint64'), seed=8)
        real_array = ak.randint(0, k, m, dtype=ak.dtype('float64'), seed=10)
        bool_array = ak.randint(0, k, m, dtype=ak.dtype('bool'), seed=12)
        strings_array = ak.random_strings_uniform(0, k, m, 
                                                  characters="abcdefghijklmonpqrstuvwxyz",
                                                  seed=14
                                                )

        test_edge_dict = {
            "src":src_array,
            "dst":dst_array,
            "data1":int_array,
            "data2":uint_array,
            "data3":real_array,
            "data4":bool_array,
            "data5":strings_array
        }
        graph.load_edge_attributes(ak.DataFrame(test_edge_dict), source_column="src",
                                   destination_column="dst", relationship_columns=["data5", "data1"]
                                )

        m = len(graph)
        int_array = ak.randint(-1, k, m, dtype=ak.dtype('int64'), seed=6)
        uint_array = ak.randint(0, k, m, dtype=ak.dtype('uint64'), seed=8)
        real_array = ak.randint(0, k, m, dtype=ak.dtype('float64'), seed=10)
        bool_array = ak.randint(0, k, m, dtype=ak.dtype('bool'), seed=12)
        strings_array = ak.random_strings_uniform(0, k, m, 
                                                  characters="abcdefghijklmonpqrstuvwxyz",
                                                  seed=14
                                                )

        test_node_dict = {
            "nodes":graph.nodes(),
            "data1":int_array,
            "data2":uint_array,
            "data3":real_array,
            "data4":bool_array,
            "data5":strings_array
        }
        graph.load_node_attributes(ak.DataFrame(test_node_dict), node_column="nodes",
                                   label_columns=["data5", "data2"]
                                )

        return graph

    def subgraph_view(self):
        """Tests subgraph_view function for property graphs."""
        graph = self.build_prop_graph()

        def node_filter(node_attributes):
            return node_attributes["data2"] == 0

        def edge_filter(edge_attributes):
            return edge_attributes["data1"] > -1

        subgraph_nodes = graph.subgraph_view(filter_node=node_filter)
        subgraph_edges = graph.subgraph_view(filter_edge=edge_filter)
        subgraph_together = graph.subgraph_view(filter_node=node_filter, filter_edge=edge_filter)

        self.assertListEqual(subgraph_nodes.nodes().to_list(), [0, 1, 3, 5, 6, 7, 8])
        self.assertListEqual(subgraph_edges.nodes().to_list(), [1, 3, 5, 6, 8])
        self.assertListEqual(subgraph_together.nodes().to_list(), [1, 6])

    def test_prop_graph_and_networkx_graph_equality(self):
        prop_graph, nx_graph = self.build_prop_graph_and_networkx()

        # 1. Check number of nodes
        self.assertEqual(len(prop_graph.nodes()), nx_graph.number_of_nodes())

        # 2. Check number of edges
        self.assertEqual(prop_graph.size(), nx_graph.number_of_edges())

        # 3. Check node equality
        prop_nodes = set(prop_graph.nodes().to_ndarray())
        nx_nodes = set(nx_graph.nodes())
        self.assertSetEqual(prop_nodes, nx_nodes)

        # 4. Check edge equality
        # Assuming prop_graph.get_edge_attributes() returns a dict like {(src, dst): attributes}
        graph_edge_information = prop_graph.get_edge_attributes().to_pandas()
        prop_edges = set()
        for index, row in graph_edge_information.iterrows():
            src = row['src']  # Adjust field names as necessary
            dst = row['dst']
            # Assuming all other columns are attributes
            attributes = row.drop(['src', 'dst'])  # Exclude src, dst from attributes
            prop_edges.add((src, dst, frozenset(attributes.items())))


        nx_edges = set()
        for row in nx.to_pandas_edgelist(nx_graph).itertuples(index=False):
            src = getattr(row, 'source')
            dst = getattr(row, 'target')
            # Dynamically build attributes dict excluding 'source' and 'target'
            attributes = {attr: value for attr, value in row._asdict().items() if attr not in ['source', 'target']}
            nx_edges.add((src, dst, frozenset(attributes.items())))

        self.assertSetEqual(prop_edges, nx_edges)
        

    def build_prop_graph_and_networkx(self):
        """Builds undirected and weighted graphs in both Arachne and NetworkX for tests."""
        graph = ar.PropGraph()
        m, n, k = 10, 10, 2

        src_array = ak.randint(0, n, m, dtype=ak.dtype('int64'), seed=2)
        dst_array = ak.randint(0, n, m, dtype=ak.dtype('int64'), seed=4)
        int_array = ak.randint(-1, k, m, dtype=ak.dtype('int64'), seed=6)
        uint_array = ak.randint(0, k, m, dtype=ak.dtype('uint64'), seed=8)
        real_array = ak.randint(0, k, m, dtype=ak.dtype('float64'), seed=10)
        bool_array = ak.randint(0, k, m, dtype=ak.dtype('bool'), seed=12)
        strings_array = ak.random_strings_uniform(0, k, m, 
                                                  characters="abcdefghijklmonpqrstuvwxyz",
                                                  seed=14
                                                )

        test_edge_dict = {
            "src":src_array,
            "dst":dst_array,
            "data1":int_array,
            "data2":uint_array,
            "data3":real_array,
            "data4":bool_array,
            "data5":strings_array
        }
        graph.load_edge_attributes(ak.DataFrame(test_edge_dict), source_column="src",
                                   destination_column="dst", relationship_columns=["data5", "data1"]
                                )

        m = len(graph)
        int_array = ak.randint(-1, k, m, dtype=ak.dtype('int64'), seed=6)
        uint_array = ak.randint(0, k, m, dtype=ak.dtype('uint64'), seed=8)
        real_array = ak.randint(0, k, m, dtype=ak.dtype('float64'), seed=10)
        bool_array = ak.randint(0, k, m, dtype=ak.dtype('bool'), seed=12)
        strings_array = ak.random_strings_uniform(0, k, m, 
                                                  characters="abcdefghijklmonpqrstuvwxyz",
                                                  seed=14
                                                )

        test_node_dict = {
            "nodes":graph.nodes(),
            "data1":int_array,
            "data2":uint_array,
            "data3":real_array,
            "data4":bool_array,
            "data5":strings_array
        }
        graph.load_node_attributes(ak.DataFrame(test_node_dict), node_column="nodes",
                                   label_columns=["data5", "data2"]
                                )

        # Building NetworkX DiGraph
        graph_edge_information = graph.get_edge_attributes()
        nx_graph=nx.from_pandas_edgelist(graph_edge_information.to_pandas(), source='src',
                                target='dst', edge_attr=True, create_using=nx.DiGraph)
        

        return graph, nx_graph

        
        
