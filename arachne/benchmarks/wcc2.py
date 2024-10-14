import arkouda as ak
import arachne as ar
import scipy as sp
import networkx as nx
import matplotlib.pyplot as plt
import os
import pandas as pd

# Connect to Arkouda server
ak.connect("n119", 5555)

# Create an Arachne graph from a test network file.
ar_network_graph = ar.read_tsv_file(os.path.abspath("/scratch/users/md724/DataSets/UIUC/wiki_topcats/wiki_topcats_cleaned.tsv"))

# Execute wcc with the absolute path to the generate and the create network file.
filePath = os.path.abspath("/scratch/users/md724/DataSets/UIUC/wiki_topcats/S2_wiki_topcats_leiden.0.001_i2_clustering.tsv")
outputPath = os.path.abspath("/scratch/users/md724/DataSets/wcc/WCC_Output")
clusters = ar.well_connected_components(ar_network_graph, filePath, outputPath, "debug")
print("Number of clusters processed = ", clusters.size)

print("clusters = ", clusters)
print("clusters.size = ", clusters.size)
ak.shutdown()


