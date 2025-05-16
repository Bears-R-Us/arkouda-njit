import arkouda as ak
import arachne as ar
import os

# NOTE: Make sure to change the server name to whatever is applicable in your environment. 
# If running locally, then use only ak.connect().
ak.connect("n0011", 5555)

# Create an Arachne graph from a test network file.
ar_network_graph = ar.read_tsv_file(os.path.abspath("../data/wcc/test_network.tsv"))

# Execute wcc with the absolute path to the generate and the create network file.
file_path = os.path.abspath("../data/wcc/test_clustering.tsv")
output_path = os.path.abspath("../output/")
output_filename = "test_network_wcc_output_post.tsv"

num_clusters = ar.well_connected_components(ar_network_graph, file_path, output_path, 
                                            output_filename=output_filename,
                                            connectedness_criterion = "log10",
                                            pre_filter_min_size=1, post_filter_min_size=1)
print(f"WCC found {num_clusters} clusters to be well-connected.")
