from base_test import ArkoudaTest
import algorithm_test
import arkouda as ak
import arachne as ar
import networkx as nx

class ClassTest(ArkoudaTest):
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

        return ar_di_graph, nx_di_graph, ar_di_graph_weighted, nx_di_graph_weighted

    def test_add_edges_from(self):
        """Testing adding edges to undirected and directed graphs."""
        ar_graph, nx_graph, ar_graph_weighted, nx_graph_weighted = self.build_undirected_graph()
        ar_di_graph, nx_di_graph, ar_di_graph_weighted, nx_di_graph_weighted = self.build_directed_graph()

        ar_tuple_u = (len(ar_graph), ar_graph.size())
        nx_tuple_u = (len(nx_graph), nx_graph.size())

        ar_tuple_d = (len(ar_di_graph), ar_di_graph.size())
        nx_tuple_d = (len(nx_di_graph), nx_di_graph.size())

        ar_tuple_uw = (len(ar_graph_weighted), ar_graph_weighted.size())
        nx_tuple_uw = (len(nx_graph_weighted), nx_graph_weighted.size())

        ar_tuple_dw = (len(ar_di_graph_weighted), ar_di_graph_weighted.size())
        nx_tuple_dw = (len(nx_di_graph_weighted), nx_di_graph_weighted.size())

        undirected_test = self.assertEqual(ar_tuple_u, nx_tuple_u)
        directed_test = self.assertEqual(ar_tuple_d, nx_tuple_d)
        undirected_weighted_test = self.assertEqual(ar_tuple_uw, nx_tuple_uw)
        directed_weighted_test = self.assertEqual(ar_tuple_dw, nx_tuple_dw)

        check_undirected = self.assertEqual(undirected_test, undirected_weighted_test)
        check_directed = self.assertEqual(directed_test, directed_weighted_test)

        return self.assertEqual(check_undirected, check_directed)

    def test_nodes_and_edges(self):
        """Testing returning all the nodes and edges for a graph."""
        ar_graph, nx_graph, ar_graph_weighted, nx_graph_weighted = self.build_undirected_graph()
        ar_di_graph, nx_di_graph, ar_di_graph_weighted, nx_di_graph_weighted = self.build_directed_graph()

        ar_tuple_u = (len(ar_graph.nodes()), len(ar_graph.edges()[0]))
        nx_tuple_u = (len(nx_graph.nodes()), len(nx_graph.edges())*2-nx.number_of_selfloops(nx_graph))

        ar_tuple_d = (len(ar_di_graph.nodes()), len(ar_di_graph.edges()[0]))
        nx_tuple_d = (len(nx_di_graph.nodes()), len(nx_di_graph.edges()))

        ar_tuple_uw = (len(ar_graph_weighted.nodes()), len(ar_graph_weighted.edges()[0]))
        nx_tuple_uw = (len(nx_graph_weighted.nodes()), len(nx_graph_weighted.edges())*2-nx.number_of_selfloops(nx_graph_weighted))

        ar_tuple_dw = (len(ar_di_graph_weighted.nodes()), len(ar_di_graph_weighted.edges()[0]))
        nx_tuple_dw = (len(nx_di_graph_weighted.nodes()), len(nx_di_graph_weighted.edges()))

        print("Nodes and Edges:")
        print(ar_tuple_u)
        print(nx_tuple_u)
        print()
        print(ar_tuple_d)
        print(nx_tuple_d)
        print()
        print(ar_tuple_uw)
        print(nx_tuple_uw)
        print()
        print(ar_tuple_dw)
        print(nx_tuple_dw)

        undirected_test = self.assertEqual(ar_tuple_u, nx_tuple_u)
        directed_test = self.assertEqual(ar_tuple_d, nx_tuple_d)
        undirected_weighted_test = self.assertEqual(ar_tuple_uw, nx_tuple_uw)
        directed_weighted_test = self.assertEqual(ar_tuple_dw, nx_tuple_dw)

        check_undirected = self.assertEqual(undirected_test, undirected_weighted_test)
        check_directed = self.assertEqual(directed_test, directed_weighted_test)

        return self.assertEqual(check_undirected, check_directed)




