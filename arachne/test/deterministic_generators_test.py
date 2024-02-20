import pathlib
from base_test import ArkoudaTest
import networkx as nx
import arachne as ar
import arkouda as ak

class DeterministicGeneratorsTest(ArkoudaTest):

    def test_complete_graph(self):
        n = 10
        #ar.Graph vs nx.Graph
        
        ar_graph = ar.complete_graph(n,ar.Graph)
        nx_graph = nx.complete_graph(n,nx.Graph)
        #Check Node count Equality
        self.assertEqual(ar_graph.n_vertices,nx_graph.number_of_nodes())
        #Check Edge count Equality
        self.assertEqual(ar_graph.size(),nx_graph.number_of_edges())
        ar_total_degree = ar_graph.degree().sum()
        nx_degree = sum(dict(nx_graph.degree()).values())
        #Check total Degree
        self.assertEqual(ar_total_degree,nx_degree)
        #Check Degree Equality per node
        ar_degrees = list(ar_graph.degree().to_ndarray())
        nx_degrees = [degree for node, degree in nx_graph.degree()]
        self.assertEqual(ar_degrees,nx_degrees)

        #ar.DiGraph vs nx.DiGraph

        ar_graph = ar.complete_graph(n,ar.DiGraph)
        nx_graph = nx.complete_graph(n,nx.DiGraph)
        #Check Node count Equality
        self.assertEqual(ar_graph.n_vertices,nx_graph.number_of_nodes())
        #Check Edge count Equality
        self.assertEqual(ar_graph.size(),nx_graph.number_of_edges())
        ar_degree = ar_graph.degree().sum()
        
        #Check total Degree
        nx_total_in_degree = sum(dict(nx_graph.in_degree()).values())
        nx_total_out_degree = sum(dict(nx_graph.out_degree()).values())
        nx_total_degree_directed = nx_total_in_degree + nx_total_out_degree
        ar_total_degree = ar_graph.in_degree().sum() + ar_graph.out_degree().sum()
        self.assertEqual(ar_total_degree, nx_total_degree_directed)
        #Check In/Out Degree per node
        nx_in_degrees = [degree for node,degree in list(nx_graph.in_degree())]
        nx_out_degrees =  [degree for node,degree in list(nx_graph.out_degree())]

        ar_in_degrees = list(ar_graph.in_degree().to_ndarray())
        ar_out_degrees = list(ar_graph.out_degree().to_ndarray())

        self.assertEqual(ar_in_degrees,nx_in_degrees)
        self.assertEqual(ar_out_degrees,nx_out_degrees)


    def test_path_graph(self):
        n = 10
        #ar.Graph vs nx.Graph
        ar_graph = ar.path_graph(n,ar.Graph)
        nx_graph = nx.path_graph(n,nx.Graph)
        #Check Node count Equality
        self.assertEqual(ar_graph.n_vertices,nx_graph.number_of_nodes())
        #Check Edge count Equality
        self.assertEqual(ar_graph.size(),nx_graph.number_of_edges())
        ar_degree = ar_graph.degree().sum()
        nx_degree = sum(dict(nx_graph.degree()).values())
        #Check total Degree
        self.assertEqual(ar_degree,nx_degree)
        #Check Degree Equality per node
        ar_degrees = list(ar_graph.degree().to_ndarray())
        nx_degrees = [degree for node, degree in nx_graph.degree()]
        self.assertEqual(ar_degrees,nx_degrees)


        #ar.DiGraph vs nx.DiGraph
        ar_graph = ar.path_graph(n,ar.DiGraph)
        nx_graph = nx.path_graph(n,nx.DiGraph)
        #Check Node count Equality
        self.assertEqual(ar_graph.n_vertices,nx_graph.number_of_nodes())
        #Check Edge count Equality
        self.assertEqual(ar_graph.size(),nx_graph.number_of_edges())
        #Check total Degree
        nx_total_in_degree = sum(dict(nx_graph.in_degree()).values())
        nx_total_out_degree = sum(dict(nx_graph.out_degree()).values())
        nx_total_degree_directed = nx_total_in_degree + nx_total_out_degree
        ar_degree = ar_graph.in_degree().sum() + ar_graph.out_degree().sum()
        self.assertEqual(ar_degree, nx_total_degree_directed)
        #Check In/Out Degree per node
        nx_in_degrees = [degree for node,degree in list(nx_graph.in_degree())]
        nx_out_degrees =  [degree for node,degree in list(nx_graph.out_degree())]

        ar_in_degrees = list(ar_graph.in_degree().to_ndarray())
        ar_out_degrees = list(ar_graph.out_degree().to_ndarray())

        self.assertEqual(ar_in_degrees,nx_in_degrees)
        self.assertEqual(ar_out_degrees,nx_out_degrees)


    def test_karate_club_graph(self):
        curr_path = str(pathlib.Path(__file__).parent.resolve())
        curr_path = curr_path.rsplit("/", 1)[0] + "/"
        filepath = curr_path + "data/karate.mtx"

        # Read in the graph with Arachne read_matrix_market_file(). 
        existing_karate_club_graph = ar.read_matrix_market_file(filepath)

        # Read in the graph with Arachne karate_club_graph()
        ar_graph= ar.karate_club_graph(ar.Graph)
        
        #Check Degree Equality per node
        ar_degrees = list(ar_graph.degree().to_ndarray())
        
        existing_karate_club_graph_degrees = list(existing_karate_club_graph.degree().to_ndarray())
        self.assertEqual(ar_degrees,existing_karate_club_graph_degrees)

        #DiGraph
        """
        #TODO
        existing_karate_club_graph = ar.read_matrix_market_file(filepath,directed = True)
        ar_graph= ar.karate_club_graph(ar.DiGraph)
        ar_in_degrees = list(ar_graph.in_degree().to_ndarray())
        ar_out_degrees = list(ar_graph.out_degree().to_ndarray())
        existing_karate_club_graph_in_degrees = list(existing_karate_club_graph.in_degree().to_ndarray())
        existing_karate_club_graph_out_degrees = list(existing_karate_club_graph.out_degree().to_ndarray())
        self.assertEqual(ar_in_degrees,existing_karate_club_graph_in_degrees)
        self.assertEqual(ar_out_degrees,existing_karate_club_graph_out_degrees)
        """


    
