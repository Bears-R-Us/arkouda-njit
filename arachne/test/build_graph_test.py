from base_test import ArkoudaTest
import arkouda as ak
import arachne as ar
import networkx as nx

class ClassTest(ArkoudaTest):
    src = [2,5,2,3,3,3,2,3,5,5,5,7,8,8,9 ,10,10,24,25,25]
    dst = [1,0,0,0,3,3,3,4,5,2,7,8,9,5,10,7 ,7 ,24,26,27]
    wgt = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1 ,1 ,1 ,10,20,20]

    def test_add_edges_from(self):
        """Testing adding edges to undirected and directed graphs."""
        Gu = ar.Graph()
        Hu = nx.Graph()

        Gd = ar.DiGraph()
        Hd = nx.DiGraph()

        Guw = ar.Graph()
        Huw = nx.Graph()

        Gdw = ar.DiGraph()
        Hdw = nx.DiGraph()

        akarray_src = ak.array(src)
        akarray_dst = ak.array(dst)
        akarray_wgt = ak.array(wgt)

        ebunch = list(zip(src, dst))
        ebunchw = list(zip(src, dst, wgt))

        Gu.add_edges_from(akarray_src, akarray_dst)
        Hu.add_edges_from(ebunch)
        ar_tuple_u = (len(Gu), Gu.size())
        nx_tuple_u = (len(Hu), Hu.size())
        
        Gd.add_edges_from(akarray_src, akarray_dst)
        Hd.add_edges_from(ebunch)
        ar_tuple_d = (len(Gd), Gd.size())
        nx_tuple_d = (len(Hd), Hd.size())
        
        Guw.add_edges_from(akarray_src, akarray_dst, akarray_wgt)
        Huw.add_weighted_edges_from(ebunchw)
        ar_tuple_uw = (len(Guw), Guw.size())
        nx_tuple_uw = (len(Huw), Huw.size())
        
        Gdw.add_edges_from(akarray_src, akarray_dst, akarray_wgt)
        Hdw.add_weighted_edges_from(ebunchw)
        ar_tuple_dw = (len(Gdw), Gdw.size())
        nx_tuple_dw = (len(Hdw), Hdw.size())

        undirected_test = self.assertEqual(ar_tuple_u, nx_tuple_u)
        directed_test = self.assertEqual(ar_tuple_d, nx_tuple_d)
        undirected_weighted_test = self.assertEqual(ar_tuple_uw, nx_tuple_uw)
        directed_weighted_test = self.assertEqual(ar_tuple_dw, nx_tuple_dw)

        check_undirected = self.assertEqual(undirected_test, undirected_weighted_test)
        check_directed = self.assertEqual(directed_test, directed_weighted_test)

        return self.assertEqual(check_undirected, check_directed)

    def test_nodes_and_edges(self):
        Gu = ar.Graph()
        Hu = nx.Graph()

        Gd = ar.DiGraph()
        Hd = nx.DiGraph()

        Guw = ar.Graph()
        Huw = nx.Graph()

        Gdw = ar.DiGraph()
        Hdw = nx.DiGraph()

        akarray_src = ak.array(src)
        akarray_dst = ak.array(dst)
        akarray_wgt = ak.array(wgt)

        ebunch = list(zip(src, dst))
        ebunchw = list(zip(src, dst, wgt))

        Gu.add_edges_from(akarray_src, akarray_dst)
        Hu.add_edges_from(ebunch)
        ar_tuple_u = (len(Gu.nodes()), len(Gu.edges()[0]))
        nx_tuple_u = (len(Hu.nodes()), len(Hu.edges()))
        
        Gd.add_edges_from(akarray_src, akarray_dst)
        Hd.add_edges_from(ebunch)
        ar_tuple_d = (len(Gd.nodes()), len(Gd.edges()[0]))
        nx_tuple_d = (len(Hd.nodes()), len(Hd.edges()))
        
        Guw.add_edges_from(akarray_src, akarray_dst, akarray_wgt)
        Huw.add_weighted_edges_from(ebunchw)
        ar_tuple_uw = (len(Guw.nodes()), len(Guw.edges()[0]))
        nx_tuple_uw = (len(Huw.nodes()), len(Huw.edges()))
        
        Gdw.add_edges_from(akarray_src, akarray_dst, akarray_wgt)
        Hdw.add_weighted_edges_from(ebunchw)
        ar_tuple_dw = (len(Gdw.nodes()), len(Gdw.edges()[0]))
        nx_tuple_dw = (len(Hdw.nodes()), len(Hdw.edges()))

        undirected_test = self.assertEqual(ar_tuple_u, nx_tuple_u)
        directed_test = self.assertEqual(ar_tuple_d, nx_tuple_d)
        undirected_weighted_test = self.assertEqual(ar_tuple_uw, nx_tuple_uw)
        directed_weighted_test = self.assertEqual(ar_tuple_dw, nx_tuple_dw)

        check_undirected = self.assertEqual(undirected_test, undirected_weighted_test)
        check_directed = self.assertEqual(directed_test, directed_weighted_test)

        return self.assertEqual(check_undirected, check_directed)




