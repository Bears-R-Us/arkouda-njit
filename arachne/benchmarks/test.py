import argparse
import time
import arachne as ar
import arkouda as ak
import numpy as np
import networkx as nx
import random


#### Connect to the Arkouda server.
ak.verbose = False
ak.connect("n116", "5555")

G = ar.PropGraph()
src = [1, 2, 3, 11, 21, 31]
dst = [2, 3, 1, 21, 31, 11]
src_column = [1, 2, 3, 5, 5, 5]
dst_column = [2, 3, 1, 5, 5, 5]
edge_dict = {
    "src": src,
    # "src_type": src_type,
    "src_column": src_column,
    "dst": dst,
    # "dst_type": dst_type,
    "dst_column": dst_column,
}
edge_df = ak.DataFrame(edge_dict)
G.load_edge_attributes(edge_df, source_column="src", destination_column="dst", relationship_columns=["src_column", "dst_column"])

subgraph = ar.PropGraph()
src = [1, 2, 3]
dst = [2, 3, 1]
src_column = [1, 2, 3]
dst_column = [2, 3, 1]
edge_dict = {
    "src": src,
    "src_column": src_column,
    "dst": dst,
    "dst_column": dst_column,
}
edge_df = ak.DataFrame(edge_dict)
subgraph.load_edge_attributes(edge_df, source_column="src", destination_column="dst", relationship_columns=["src_column", "dst_column"])

isos = ar.subgraph_isomorphism(G, subgraph)
print(len(isos), len(ak.unique(isos)), isos)
