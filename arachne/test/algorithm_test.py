from base_test import ArkoudaTest
import arkouda as ak
import arachne as ar
import scipy as sp
import scipy.io
import pathlib
import networkx as nx

class AlgorithmTest(ArkoudaTest):
    def get_graph_file_and_attributes(self):
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

        return (filepath, directed, weighted, only_extension)
    
    def test_bfs_layers(self):
        # Process graph with Arachne.
        filepath,directed,weighted,only_extension = self.get_graph_file_and_attributes()
        ar_graph = ar.read_edgelist(filepath, directed=directed, weighted=weighted, filetype=only_extension)
        ar_layers = ar.bfs_layers(ar_graph, 0).to_ndarray()

        # Turn Arachne results to a dictionary to compare against NetworkX.
        ar_layer_dict = {}
        for (i,depth) in enumerate(ar_layers):
            if depth not in ar_layer_dict:
                ar_layer_dict[depth] = [i]
            else:
                ar_layer_dict[depth].append(i)

        # Process graph with NetworkX.
        nx_file = open(filepath, "rb")
        nx_graph = nx.from_scipy_sparse_array(sp.io.mmread(nx_file))
        nx_layer_dict = dict(enumerate(nx.bfs_layers(nx_graph, 0)))

        # Modify outputs to ensure equality.
        for (nx_layer, ar_layer) in zip(ar_layer_dict.items(), nx_layer_dict.items()):
            nx_layer[1].sort()
            ar_layer[1].sort()

        return self.assertEqual(ar_layer_dict, nx_layer_dict)

    def test_connected_components(self):
        # Process graph with Arachne.
        filepath,directed,weighted,only_extension = self.get_graph_file_and_attributes()
        ar_graph = ar.read_edgelist(filepath, directed=directed, weighted=weighted, filetype=only_extension)
        ar_cc = ar.connected_components(ar_graph)

        # Process graph with NetworkX.
        nx_file = open(filepath, "rb")
        nx_graph = nx.from_scipy_sparse_array(sp.io.mmread(nx_file))
        nx_cc = nx.connected_components(nx_graph)

        return self.assertEqual(len(list(nx_cc)), len(ak.unique(ar_cc)))

    def test_triangles(self):
        # Process graph with Arachne.
        filepath,directed,weighted,only_extension = self.get_graph_file_and_attributes()
        ar_graph = ar.read_edgelist(filepath, directed=directed, weighted=weighted, filetype=only_extension)
        ar_tri_full = ar.triangles(ar_graph)
        ar_tri_partial = ar.triangles(ar_graph, ak.array([x for x in range(34)]))

        # Process graph with NetworkX.
        nx_file = open(filepath, "rb")
        nx_graph = nx.from_scipy_sparse_array(sp.io.mmread(nx_file))
        nx_tri_full = nx.triangles(nx_graph)
        nx_tri_partial = nx.triangles(nx_graph, tuple(x for x in range(34)))
        
        complete = self.assertEqual(sum(nx_tri_full.values())/3, ar_tri_full[0])

        # TODO: Partial triangle counting returns error. Has to be fixed.
        # partial = self.assertEqual(sum(nx_tri_partial.values())/3, ak.sum(ar_tri_partial))

        return complete

    def test_k_truss(self):
        # Process graph with Arachne.
        filepath,directed,weighted,only_extension = self.get_graph_file_and_attributes()
        ar_graph = ar.read_edgelist(filepath, directed=directed, weighted=weighted, filetype=only_extension)
        ar_truss = ar.k_truss(ar_graph, 4)
        ar_max_k = ar.k_truss(ar_graph, -1)

        # Process graph with NetworkX.
        nx_file = open(filepath, "rb")
        nx_graph = nx.from_scipy_sparse_array(sp.io.mmread(nx_file))
        nx_truss = nx.k_truss(nx_graph, 4)

        max_k = 5
        
        num_e_ar = ak.value_counts(ar_truss)[1][0]
        num_e_nx = nx_truss.size()
        
        max_test = self.assertEqual(ar_max_k[0], max_k)
        truss_test = self.assertEqual(num_e_ar, num_e_nx)

        # NOTE: truss decomposition NOT pytested, it uses code for both k_truss and max_truss.
        return self.assertEqual(max_test,truss_test)
    
    def test_triangle_centrality(self):
        # Process graph with Arachne.
        graph = ar.Graph()
        src = ak.array([1, 1, 3, 3, 4, 4, 4, 5, 2, 2, 5, 5, 6])
        dst = ak.array([3, 4, 4, 7, 7, 5, 8, 8, 5, 6, 6, 9, 9])
        graph.add_edges_from(src, dst)

        ar_tri_ctr = ar.triangle_centrality(graph).to_list()
        ar_tri_ctr_true = [0.4, 0.4, 0.4666666666666667, 0.7333333333333333, 0.7333333333333333, 0.4666666666666667, 0.4, 0.4666666666666667, 0.4]
        print(ar_tri_ctr)

        return self.assertEqual(ar_tri_ctr, ar_tri_ctr_true)



