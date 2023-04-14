from base_test import ArkoudaTest
import arkouda as ak
import arachne as ar
import scipy as sp
import scipy.io
import pathlib
import networkx as nx

class ReadingTest(ArkoudaTest):
    def test_read_known_edgelist(self):
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
        G = ar.read_known_edgelist(78, 34, filepath, directed=directed, weighted=weighted, filetype=only_extension)

        # Read in graph with NetworkX.
        fh = open(filepath, "rb")
        H = nx.from_scipy_sparse_array(sp.io.mmread(fh))

        # (num_vertices, num_edges) tuples for comparison.
        ar_tuple = (len(G), G.size())
        nx_tuple = (len(H), H.size())

        return self.assertEqual(ar_tuple, nx_tuple)

    def test_read_edgelist(self):
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

        # Read in graph with NetworkX.
        fh = open(filepath, "rb")
        H = nx.from_scipy_sparse_array(sp.io.mmread(fh))

        # (num_vertices, num_edges) tuples for comparison.
        ar_tuple = (len(G), G.size())
        nx_tuple = (len(H), H.size())

        return self.assertEqual(ar_tuple, nx_tuple)