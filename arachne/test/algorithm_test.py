from base_test import ArkoudaTest
import networkx as nx
import arachne as ar
import arkouda as ak

class AlgorithmTest(ArkoudaTest):
    """Test graph algorithm methods."""
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

    def test_undirected_bfs_layers(self):
        """Tests Arachne bfs_layers() and compares against NetworkX."""
        # Read in graphs with Arachne and NetworkX.
        ar_graph, nx_graph,_,_ = self.build_undirected_graph()

        # Extract vertices to launch breadth-first search from each.
        vertices = ar_graph.nodes().to_list()

        ar_all_layers = []
        nx_all_layers = []
        for root in vertices:
            # Compute breadth-first search with Arachne.
            ar_layers = ar.bfs_layers(ar_graph, root).to_list()

            # Compute breadth-first search with NetworkX.
            nx_layer_dict = dict(enumerate(nx.bfs_layers(nx_graph, root)))
            nx_layers = [-1] * len(ar_layers)
            for layer,vertices_at_layer in nx_layer_dict.items():
                for vertex in vertices_at_layer:
                    nx_layers[vertices.index(vertex)] = layer

            # Add both to corresponding layers tracker.
            ar_all_layers.append(ar_layers)
            nx_all_layers.append(nx_layers)

        self.assertEqual(ar_all_layers, nx_all_layers)

    def test_directed_bfs_layers(self):
        """Tests Arachne bfs_layers() and compares against NetworkX."""
        # Read in graphs with Arachne and NetworkX.
        ar_graph, nx_graph,_,_ = self.build_directed_graph()

        # Extract vertices to launch breadth-first search from each.
        vertices = ar_graph.nodes().to_list()

        ar_all_layers = []
        nx_all_layers = []
        for root in vertices:
            # Compute breadth-first search with Arachne.
            ar_layers = ar.bfs_layers(ar_graph, root).to_list()

            # Compute breadth-first search with NetworkX.
            nx_layer_dict = dict(enumerate(nx.bfs_layers(nx_graph, root)))
            nx_layers = [-1] * len(ar_layers)
            for layer,vertices_at_layer in nx_layer_dict.items():
                for vertex in vertices_at_layer:
                    nx_layers[vertices.index(vertex)] = layer

            # Add both to corresponding layers tracker.
            ar_all_layers.append(ar_layers)
            nx_all_layers.append(nx_layers)

        self.assertEqual(ar_all_layers, nx_all_layers)

    def test_square_count(self):
        """Tests Arachne squares() and compares it against base case."""
        # Read in graph with Arachne.
        ar_graph,_,_,_ = self.build_undirected_graph()

        # Get the square count.
        sc = ar.squares(ar_graph)

        self.assertEqual(2, sc)

    def test_triangles(self):
        """Tests Arachne triangles() and compares it against NetworkX."""
        # Read in the graph with Arachne and NetworkX.
        ar_graph, nx_graph,_,_ = self.build_undirected_graph()
        nodes = [0,2,3,4]

        # Get triangle counts with Arachne.
        ar_tri_full = ar.triangles(ar_graph)
        ar_tri_partial = ar.triangles(ar_graph, ak.array(nodes))

        # Get triangle counts with NetworkX.
        nx_tri_full = nx.triangles(nx_graph)
        nx_tri_partial = nx.triangles(nx_graph, nodes)

        ret = [nx_tri_partial[v] for v in nodes]
        self.assertEqual(ret, ar_tri_partial.to_list())
        self.assertEqual(sum(nx_tri_full.values())/3, ar_tri_full/3)

    def test_triangle_centrality(self):
        """Tests Arachne triangles() and compares it against NetworkX."""
        # Read in the graph with Arachne.
        src = [0, 1, 2, 3, 4, 4, 5, 6, 7, 8, 0]
        dst = [1, 2, 0, 0, 3, 0, 6, 7, 5, 9, 0]
        graph = ar.Graph()
        graph.add_edges_from(ak.array(src), ak.array(dst))

        # Get triangle centralities with Arachne.
        triangle_centralities = ar.triangle_centrality(graph)
        triangle_centralities = triangle_centralities * 10
        triangle_centralities = ak.cast(triangle_centralities, ak.int64)

        # Actual results.
        results = [6, 4, 4, 4, 4, 3, 3, 3, 0, 0]

        self.assertListEqual(results, triangle_centralities.to_list())
