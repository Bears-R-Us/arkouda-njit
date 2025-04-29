import pathlib
from base_test import ArkoudaTest
import arachne as ar
import networkx as nx
import scipy as sp
import arkouda as ak

class ClassTest(ArkoudaTest):
    """Tests graph class methods."""
    def build_undirected_graph(self):
        """Builds undirected and weighted graphs in both Arachne and NetworkX for tests."""
        src_list = [2,5,2,3,3,3,3,2,3,4,5,5,5,5,5,5,7,8,9,9,8,9 ,10,10,10,24,25,25]
        dst_list = [1,0,0,0,3,3,3,3,4,3,5,2,2,2,2,7,8,9,8,8,5,10,7 ,7 ,7 ,24,26,27]
        wgt_list = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1 ,1 ,1 ,1 ,1 ,10,20]
        src = ak.array(src_list)
        dst = ak.array(dst_list)
        wgt = ak.array(wgt_list)

        ar_graph = ar.Graph()
        ar_graph.add_edges_from(src,dst)
        ar_graph_weighted = ar.Graph()
        ar_graph_weighted.add_edges_from(src,dst,wgt)

        ebunch = list(zip(src_list,dst_list))
        nx_graph = nx.Graph()
        nx_graph.add_edges_from(ebunch)
        ebunchw = list(zip(src_list,dst_list,wgt_list))
        nx_graph_weighted = nx.Graph()
        nx_graph_weighted.add_weighted_edges_from(ebunchw)

        # Remove self-loops and vertices with degree 0 in NetworkX graphs
        nx_graph.remove_edges_from(nx.selfloop_edges(nx_graph))
        nodes_to_remove = [node for node, degree in nx_graph.degree() if degree == 0]
        nx_graph.remove_nodes_from(nodes_to_remove)

        nx_graph_weighted.remove_edges_from(nx.selfloop_edges(nx_graph_weighted))
        nodes_to_remove = [node for node, degree in nx_graph_weighted.degree() if degree == 0]
        nx_graph_weighted.remove_nodes_from(nodes_to_remove)

        return ar_graph, nx_graph, ar_graph_weighted, nx_graph_weighted

    def build_directed_graph(self):
        """Builds directed and weighted graphs in both Arachne and NetworkX for tests."""
        src_list = [2,5,2,3,3,3,3,2,3,4,5,5,5,5,5,5,7,8,9,9,8,9 ,10,10,10,24,25,25]
        dst_list = [1,0,0,0,3,3,3,3,4,3,5,2,2,2,2,7,8,9,8,8,5,10,7 ,7 ,7 ,24,26,27]
        wgt_list = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1 ,1 ,1 ,1 ,1 ,10,20]
        src = ak.array(src_list)
        dst = ak.array(dst_list)
        wgt = ak.array(wgt_list)

        ar_di_graph = ar.DiGraph()
        ar_di_graph.add_edges_from(src,dst)
        ar_di_graph_weighted = ar.DiGraph()
        ar_di_graph_weighted.add_edges_from(src,dst,wgt)

        ebunch = list(zip(src_list,dst_list))
        nx_di_graph = nx.DiGraph()
        nx_di_graph.add_edges_from(ebunch)
        ebunchw = list(zip(src_list,dst_list,wgt_list))
        nx_di_graph_weighted = nx.DiGraph()
        nx_di_graph_weighted.add_weighted_edges_from(ebunchw)

        # Remove self-loops and vertices with degree 0 in NetworkX graphs
        nx_di_graph.remove_edges_from(nx.selfloop_edges(nx_di_graph))
        nodes_to_remove = [node for node, degree in nx_di_graph.degree() if degree == 0]
        nx_di_graph.remove_nodes_from(nodes_to_remove)

        nx_di_graph_weighted.remove_edges_from(nx.selfloop_edges(nx_di_graph_weighted))
        nodes_to_remove = [node for node, degree in nx_di_graph_weighted.degree() if degree == 0]
        nx_di_graph_weighted.remove_nodes_from(nodes_to_remove)

        return ar_di_graph, nx_di_graph, ar_di_graph_weighted, nx_di_graph_weighted
    
    def test_density(self):
        ar_graph, nx_graph, ar_graph_weighted, nx_graph_weighted = self.build_undirected_graph()
        ar_di_graph, nx_di_graph, ar_di_graph_weighted, nx_di_graph_weighted\
            = self.build_directed_graph()
        self.assertEqual(ar_graph.density(),nx.density(nx_graph))
        self.assertEqual(ar_graph_weighted.density(),nx.density(nx_graph_weighted))
        self.assertEqual(ar_di_graph.density(),nx.density(nx_di_graph))
        self.assertEqual(ar_di_graph_weighted.density(),nx.density(nx_di_graph_weighted))

    def test_add_edges_from(self):
        """Testing adding edges to undirected and directed graphs."""
        ar_graph, nx_graph, ar_graph_weighted, nx_graph_weighted = self.build_undirected_graph()
        ar_di_graph, nx_di_graph, ar_di_graph_weighted, nx_di_graph_weighted\
            = self.build_directed_graph()

        ar_tuple_u = (len(ar_graph), ar_graph.size())
        nx_tuple_u = (len(nx_graph), nx_graph.size())

        ar_tuple_d = (len(ar_di_graph), ar_di_graph.size())
        nx_tuple_d = (len(nx_di_graph), nx_di_graph.size())

        ar_tuple_uw = (len(ar_graph_weighted), ar_graph_weighted.size())
        nx_tuple_uw = (len(nx_graph_weighted), nx_graph_weighted.size())

        ar_tuple_dw = (len(ar_di_graph_weighted), ar_di_graph_weighted.size())
        nx_tuple_dw = (len(nx_di_graph_weighted), nx_di_graph_weighted.size())

        self.assertEqual(ar_tuple_u, nx_tuple_u)
        self.assertEqual(ar_tuple_d, nx_tuple_d)
        self.assertEqual(ar_tuple_uw, nx_tuple_uw)
        self.assertEqual(ar_tuple_dw, nx_tuple_dw)

    def test_nodes_and_edges(self):
        """Testing returning all the nodes and edges for a graph."""
        ar_graph, nx_graph, ar_graph_weighted, nx_graph_weighted = self.build_undirected_graph()
        ar_di_graph, nx_di_graph, ar_di_graph_weighted, nx_di_graph_weighted\
            = self.build_directed_graph()

        ar_tuple_u = (len(ar_graph.nodes()), len(ar_graph.edges()[0]))
        nx_tuple_u = (len(nx_graph.nodes()), 
                      len(nx_graph.edges())*2-nx.number_of_selfloops(nx_graph)
                    )

        ar_tuple_d = (len(ar_di_graph.nodes()), len(ar_di_graph.edges()[0]))
        nx_tuple_d = (len(nx_di_graph.nodes()), len(nx_di_graph.edges()))

        ar_tuple_uw = (len(ar_graph_weighted.nodes()), len(ar_graph_weighted.edges()[0]))
        nx_tuple_uw = (len(nx_graph_weighted.nodes()), 
                       len(nx_graph_weighted.edges())*2-nx.number_of_selfloops(nx_graph_weighted)
                    )

        ar_tuple_dw = (len(ar_di_graph_weighted.nodes()), len(ar_di_graph_weighted.edges()[0]))
        nx_tuple_dw = (len(nx_di_graph_weighted.nodes()), len(nx_di_graph_weighted.edges()))

        self.assertEqual(ar_tuple_u, nx_tuple_u)
        self.assertEqual(ar_tuple_d, nx_tuple_d)
        self.assertEqual(ar_tuple_uw, nx_tuple_uw)
        self.assertEqual(ar_tuple_dw, nx_tuple_dw)

    def test_undirected_degree(self):
        """Testing returning the degree for all the vertices in a graph."""
        ar_graph, nx_graph, _, _ = self.build_undirected_graph()

        ar_graph_degree = ar_graph.degree()
        nx_graph_degree = nx_graph.degree()

        ar_graph_degree = ar_graph_degree.to_list()
        temp = [0] * len(ar_graph)
        vertices = ar_graph.nodes().to_list()

        for tup in nx_graph_degree:
            vertex = tup[0]
            degree = tup[1]
            temp[vertices.index(vertex)] = degree
        nx_graph_degree = temp

        self.assertListEqual(ar_graph_degree, nx_graph_degree)

    def test_directed_degree(self):
        """Testing returning the in and out degrees for all the vertices in a directed graph."""
        ar_di_graph, nx_di_graph, _, _ = self.build_directed_graph()

        ar_di_graph_in_degree = ar_di_graph.in_degree().to_list()
        ar_di_graph_out_degree = ar_di_graph.out_degree().to_list()

        nx_di_graph_in_degree = nx_di_graph.in_degree()
        nx_di_graph_out_degree = nx_di_graph.out_degree()

        vertices = ar_di_graph.nodes().to_list()

        temp = [0] * len(ar_di_graph)
        for tup in nx_di_graph_in_degree:
            vertex = tup[0]
            degree = tup[1]
            temp[vertices.index(vertex)] = degree
        nx_di_graph_in_degree = temp

        temp = [0] * len(ar_di_graph)
        for tup in nx_di_graph_out_degree:
            vertex = tup[0]
            degree = tup[1]
            temp[vertices.index(vertex)] = degree
        nx_di_graph_out_degree = temp

        self.assertListEqual(ar_di_graph_in_degree, nx_di_graph_in_degree)
        self.assertListEqual(ar_di_graph_out_degree, nx_di_graph_out_degree)

    def test_read_matrix_market_file(self):
        """Tests reading a matrix market file."""
        # Parse out paths where benchmark files are to be held.
        curr_path = str(pathlib.Path(__file__).parent.resolve())
        curr_path = curr_path.rsplit("/", 1)[0] + "/"
        filepath = curr_path + "data/karate.mtx"

        # Read in the graph with Arachne. 
        ar_graph = ar.read_matrix_market_file(filepath)

        # Read in graph with NetworkX.
        file_object = open(filepath, "rb")
        nx_graph = nx.from_scipy_sparse_array(sp.io.mmread(file_object))

        # (num_vertices, num_edges) tuples for comparison.
        ar_tuple = (len(ar_graph), ar_graph.size())
        nx_tuple = (len(nx_graph), nx_graph.size())

        self.assertEqual(ar_tuple, nx_tuple)
