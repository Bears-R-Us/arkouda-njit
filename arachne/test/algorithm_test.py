from base_test import ArkoudaTest
import arkouda as ak
import arachne as ar
import networkx as nx

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

        return self.assertEqual(ar_all_layers, nx_all_layers)
    
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

        return self.assertEqual(ar_all_layers, nx_all_layers)
    
    def test_square_count(self):
        """Tests Arachne squares() and compares it against base case."""
        # Read in graph with Arachne.
        ar_graph,_,_,_ = self.build_undirected_graph()

        # Get the square count.
        sc = ar.squares(ar_graph)

        return self.assertEqual(2, sc)

    # FUNCTIONS BELOW ARE CURRENTLY NOT WORKING AND HAVE TO BE FIXED.
    # def test_triangles(self):
    #     # Process graph with Arachne.
    #     filepath,directed,weighted,only_extension = self.get_graph_file_and_attributes()
    #     ar_graph = ar.read_edgelist(filepath, directed=directed, weighted=weighted, filetype=only_extension)
    #     ar_tri_full = ar.triangles(ar_graph)
    #     ar_tri_partial = ar.triangles(ar_graph, ak.array([x for x in range(34)]))

    #     # Process graph with NetworkX.
    #     nx_file = open(filepath, "rb")
    #     nx_graph = nx.from_scipy_sparse_array(sp.io.mmread(nx_file))
    #     nx_tri_full = nx.triangles(nx_graph)
    #     nx_tri_partial = nx.triangles(nx_graph, (x for x in range(34)))

    #     ret = [x for x in range(34)]
    #     for i in range(34):
    #         ret[i] = nx_tri_partial[i]
        
    #     partial = self.assertEqual(ret, ar_tri_partial.to_list())
    #     complete = self.assertEqual(sum(nx_tri_full.values())/3, ar_tri_full[0])
    #     return self.assertEqual(partial, complete)
    # def test_connected_components(self):
    #     # Process graph with Arachne.
    #     filepath,directed,weighted,only_extension = self.get_graph_file_and_attributes()
    #     ar_graph = ar.read_edgelist(filepath, directed=directed, weighted=weighted, filetype=only_extension)
    #     ar_cc = ar.connected_components(ar_graph)

    #     # Process graph with NetworkX.
    #     nx_file = open(filepath, "rb")
    #     nx_graph = nx.from_scipy_sparse_array(sp.io.mmread(nx_file))
    #     nx_cc = nx.connected_components(nx_graph)

    #     return self.assertEqual(len(list(nx_cc)), len(ak.unique(ar_cc)))

    # def test_k_truss(self):
    #     # Process graph with Arachne.
    #     filepath,directed,weighted,only_extension = self.get_graph_file_and_attributes()
    #     ar_graph = ar.read_edgelist(filepath, directed=directed, weighted=weighted, filetype=only_extension)
    #     ar_truss = ar.k_truss(ar_graph, 4)
    #     ar_max_k = ar.k_truss(ar_graph, -1)

    #     # Process graph with NetworkX.
    #     nx_file = open(filepath, "rb")
    #     nx_graph = nx.from_scipy_sparse_array(sp.io.mmread(nx_file))
    #     nx_truss = nx.k_truss(nx_graph, 4)

    #     max_k = 5
        
    #     num_e_ar = ak.value_counts(ar_truss)[1][0]
    #     num_e_nx = nx_truss.size()
        
    #     max_test = self.assertEqual(ar_max_k[0], max_k)
    #     truss_test = self.assertEqual(num_e_ar, num_e_nx)

    #     # NOTE: truss decomposition NOT pytested, it uses code for both k_truss and max_truss.
    #     return self.assertEqual(max_test,truss_test)
    
    # def test_triangle_centrality(self):
    #     # Process graph with Arachne.
    #     graph = ar.Graph()
    #     src = ak.array([1, 1, 3, 3, 4, 4, 4, 5, 2, 2, 5, 5, 6])
    #     dst = ak.array([3, 4, 4, 7, 7, 5, 8, 8, 5, 6, 6, 9, 9])
    #     graph.add_edges_from(src, dst)

    #     ar_tri_ctr = ar.triangle_centrality(graph).to_list()
    #     ar_tri_ctr_true = [0.4, 0.4, 0.4666666666666667, 0.7333333333333333, 0.7333333333333333, 0.4666666666666667, 0.4, 0.4666666666666667, 0.4]
    #     print(ar_tri_ctr)

    #     return self.assertEqual(ar_tri_ctr, ar_tri_ctr_true)



