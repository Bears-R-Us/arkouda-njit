from base_test import ArkoudaTest
import arkouda as ak
import arachne as ar
import scipy as sp
import scipy.io
import pathlib
import networkx as nx

class BreadthFirstSearchTest(ArkoudaTest):
    def test_bfs_layers(self):  
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

        # Run bfs_layers with Arachne. 
        ar_layers = ar.bfs_layers(G, 0).to_ndarray()

        # Turn Arachne results to a dictionary to compare against NetworkX.
        ar_layer_dict = {}
        for (i,x) in enumerate(ar_layers):
            if x not in ar_layer_dict:
                ar_layer_dict[x] = [i]
            else:
                ar_layer_dict[x].append(i)

        # Read in graph and generate dictionary object with NetworkX.
        fh = open(filepath, "rb")
        H = nx.from_scipy_sparse_array(sp.io.mmread(fh))
        nx_layer_dict = dict(enumerate(nx.bfs_layers(H, 0)))

        # Sort to make the lists the same for equal comparison. 
        for key in ar_layer_dict:
            ar_layer_dict[key].sort()
            nx_layer_dict[key].sort()

        return self.assertEqual(ar_layer_dict, nx_layer_dict)