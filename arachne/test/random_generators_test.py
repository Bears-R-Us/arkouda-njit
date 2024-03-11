import pathlib
from base_test import ArkoudaTest
import networkx as nx
import arachne as ar
import arkouda as ak

class RandomGeneratorsTest(ArkoudaTest):

    def test_random_tree(self):
        #ar.Graph vs networkx Graph
        n = 2
        ar_graph = ar.random_tree(n,ar.Graph)
        nx_graph = nx.random_tree(n)
        src, dst = ar_graph.edges()
        src = src.to_ndarray()
        dst = dst.to_ndarray()
        ar_edge_set = [(src_item, dst_item) for src_item, dst_item in zip(src, dst)]

        nx_edge_set = list(nx_graph.edges())
        #Check expected edge set for graph with two nodes to see if both are valid
        self.assertEqual(self.isExpectedEdgeSet(ar_edge_set), self.isExpectedEdgeSet(nx_edge_set))
        #ar.DiGraph vs networkx DiGraph
        ar_graph = ar.random_tree(n,ar.DiGraph)
        nx_graph = nx.random_tree(n)
        nx_graph = nx.DiGraph(nx_graph)
       
        src, dst = ar_graph.edges()
        src = src.to_ndarray()
        dst = dst.to_ndarray()
        ar_edge_set = [(src_item, dst_item) for src_item, dst_item in zip(src, dst)]
        nx_edge_set = list(nx_graph.edges())
        #Check expected edge set for graph with two nodes to see if both are valid
        self.assertEqual(self.isExpectedEdgeSet(ar_edge_set), self.isExpectedEdgeSet(nx_edge_set))

       
    def test_gnp(self):
        #ar.Graph vs networkx Graph
        n = 2   
        ar_graph = ar.gnp(n,.5,ar.Graph)
        nx_graph = nx.gnp_random_graph(n,.5)

        if ar_graph.size()  == 0:
            ar_edge_set = [] 
        else:
            src, dst = ar_graph.edges()
            src = src.to_ndarray()
            dst = dst.to_ndarray()
            ar_edge_set = [(src_item, dst_item) for src_item, dst_item in zip(src, dst)]

        nx_edge_set = list(nx_graph.edges())
        #Check expected edge set for graph with two nodes to see if both are valid
        self.assertEqual(self.isExpectedEdgeSet(ar_edge_set), self.isExpectedEdgeSet(nx_edge_set))

        #ar.DiGraph vs networkx DiGraph
        ar_graph = ar.gnp(n,.5,ar.DiGraph)
        nx_graph = nx.gnp_random_graph(n,.5)
        nx_graph = nx.DiGraph(nx_graph)
        if ar_graph.size() == 0:
            ar_edge_set = [] 
        else:
            src, dst = ar_graph.edges()
            src = src.to_ndarray()
            dst = dst.to_ndarray()
            ar_edge_set = [(src_item, dst_item) for src_item, dst_item in zip(src, dst)]

        nx_edge_set = list(nx_graph.edges())
        #Check expected edge set for graph with two nodes to see if both are valid
        self.assertEqual(self.isExpectedEdgeSet(ar_edge_set), self.isExpectedEdgeSet(nx_edge_set))

    
    def test_rmat(self):
        #ar.Graph vs expected edge set
        n = 1
        edge_factor = 1
        ar_graph = ar.rmat(n,ar.Graph,edge_factor)
        
        if ar_graph.size()  == 0:
            ar_edge_set = [] 
        else:
            src, dst = ar_graph.edges()
            src = src.to_ndarray()
            dst = dst.to_ndarray()
            ar_edge_set = [(src_item, dst_item) for src_item, dst_item in zip(src, dst)]

        self.assertEqual(self.isExpectedEdgeSet(ar_edge_set), True)

        #ar.DiGraph vs expected edge set
        ar_graph = ar.rmat(n,ar.DiGraph,edge_factor)
        if ar_graph.size() == 0:
            ar_edge_set = [] 
        else:
            src, dst = ar_graph.edges()
            src = src.to_ndarray()
            dst = dst.to_ndarray()
            ar_edge_set = [(src_item, dst_item) for src_item, dst_item in zip(src, dst)]

        self.assertEqual(self.isExpectedEdgeSet(ar_edge_set), True)

    def test_watts_strogatz_graph(self):
        #ar.Graph vs networkx Graph
        n = 2   
        k = 2
        p = .5
        ar_graph = ar.watts_strogatz_graph(n,k,p,ar.Graph)
        nx_graph = nx.watts_strogatz_graph(n,k,p)
       
        if ar_graph.size()  == 0:
            ar_edge_set = [] 
        else:
            src, dst = ar_graph.edges()
            src = src.to_ndarray()
            dst = dst.to_ndarray()
            ar_edge_set = [(src_item, dst_item) for src_item, dst_item in zip(src, dst)]

        nx_edge_set = list(nx_graph.edges())
        #Check expected edge set for graph with two nodes to see if both are valid
        self.assertEqual(self.isExpectedEdgeSet(ar_edge_set), self.isExpectedEdgeSet(nx_edge_set))
        #ar.DiGraph vs networkx DiGraph
        ar_graph = ar.watts_strogatz_graph(n,k,p,ar.DiGraph)
        nx_graph = nx.watts_strogatz_graph(n,k,p)
        nx_graph = nx.DiGraph(nx_graph)
        if ar_graph.size() == 0:
            ar_edge_set = [] 
        else:
            src, dst = ar_graph.edges()
            src = src.to_ndarray()
            dst = dst.to_ndarray()
            ar_edge_set = [(src_item, dst_item) for src_item, dst_item in zip(src, dst)]

        nx_edge_set = list(nx_graph.edges())
        #Check expected edge set for graph with two nodes to see if both are valid
        self.assertEqual(self.isExpectedEdgeSet(ar_edge_set), self.isExpectedEdgeSet(nx_edge_set))
        
        

    def isExpectedEdgeSet(self,edge_set_to_compare):
        expected_edge_sets = [
        [],  # No edges.
        [(0, 1)],  # 0 → 1
        [(1, 0)],  # 1 → 0
        [(0, 1), (1, 0)],  # 0 ↔ 1 (Bidirectional edge between 0 and 1)
        [(0, 0)],  # 0 → 0 (Self-loop at 0)
        [(1, 1)],  # 1 → 1 (Self-loop at 1)
        [(0, 0), (0, 1)],  # 0 → 0, 0 → 1
        [(0, 0), (1, 0)],  # 0 → 0, 1 → 0
        [(0, 0), (0, 1), (1, 0)],  # 0 → 0, 0 ↔ 1
        [(1, 1), (0, 1)],  # 1 → 1, 0 → 1
        [(1, 1), (1, 0)],  # 1 → 1, 1 → 0
        [(1, 1), (0, 1), (1, 0)],  # 1 → 1, 0 ↔ 1
        [(0, 0), (1, 1)],  # 0 → 0, 1 → 1
        [(0, 0), (1, 1), (0, 1)],  # 0 → 0, 1 → 1, 0 → 1
        [(0, 0), (1, 1), (1, 0)],  # 0 → 0, 1 → 1, 1 → 0
        [(0, 0), (1, 1), (0, 1), (1, 0)],  # 0 → 0, 1 → 1, 0 ↔ 1
        ]
        expected_edge_sets = [sorted(edge_set) for edge_set in expected_edge_sets]
        for edge_set in expected_edge_sets:
            if edge_set == sorted(edge_set_to_compare):
                return True
        return False
        
    


        

