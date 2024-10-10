import arkouda as ak
import arachne as ar
import scipy as sp
import networkx as nx
import matplotlib.pyplot as plt
import os
import pandas as pd

# Connect to Arkouda server
ak.connect("n118", 5555)


#cluster_dict = {}
print("reading the network file...")
# Create an Arachne graph from a file.
ar_network_graph = ar.read_tsv_file(os.path.abspath("/scratch/users/md724/DataSets/UIUC/oc_integer/oc_integer_cleaned_el.tsv"))
print("Graph generated!")

# Execute wcc with the absolute path to the generate and the create network file.
filePath = os.path.abspath("/scratch/users/md724/DataSets/UIUC/oc_integer/S2_oc_leiden.0.001_i2_clustering.tsv")
clusters = ar.well_connected_components(ar_network_graph, filePath, "/scratch/users/md724/DataSets/UIUC/wccOutPut")
print("Number of clusters processed = ", clusters.size)


ak.shutdown()
