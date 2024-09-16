"""Simple correctness check for subgraph isomorphism."""
import argparse
import time

import networkx as nx
import arachne as ar
import arkouda as ak

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument('--print_isos', action='store_true', help="Print isos?")

    return script_parser

if __name__ == "__main__":
    #### Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()

    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    #### Run Arachne subgraph isomorphism.
    # 1. Create vertices, edges, and attributes for main property graph.
    src_prop_graph = ak.array([0, 0, 0, 0, 1, 1, 1, 1,  1, 2, 2, 2,  3,  3,  3, 12, 14, 14, 14, 19, 17, 17, 18])
    dst_prop_graph = ak.array([4, 5, 6, 7, 0, 8, 9, 10, 3, 0, 1, 3, 11, 12, 14, 13, 15, 17, 19, 17, 16, 18, 19])
    
   
    labels1_prop_graph = ak.array(["lbl1"] * 20)
    labels2_prop_graph = ak.array(["lbl2"] * 20)
    rels1_prop_graph = ak.array(["rel1"] * src_prop_graph.size)
    rels2_prop_graph =  ak.array(["rel2"] * src_prop_graph.size)

    # 2. Transer data above into main property graph.
    prop_graph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_prop_graph, "dst":dst_prop_graph,
                            "rels1":rels1_prop_graph, "rels2":rels2_prop_graph})
    node_df_h = ak.DataFrame({"nodes": ak.arange(0,20), "lbls1":labels1_prop_graph,
                              "lbls2":labels2_prop_graph})
    prop_graph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1","rels2"])
    prop_graph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])

    # 3. Create vertices, edges, and attributes for subgraph.
    src_subgraph = ak.array([0, 0, 1, 2])
    dst_subgraph = ak.array([1, 3, 2, 0])
    labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
    labels2_subgraph = ak.array(["lbl2", "lbl2", "lbl2", "lbl2"])
    rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])
    rels2_subgraph = ak.array(["rel2", "rel2", "rel2", "rel2"])

    # 4. Transer data above into subgraph.
    subgraph = ar.PropGraph()
    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph,
                            "rels1":rels1_subgraph, "rels2":rels2_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.arange(0,4), "lbls1":labels1_subgraph,
                              "lbls2":labels2_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels1","rels2"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])

    # 5. Run the subgraph isomorphism.
    print("Arachne running ...")
    start_time = time.time()
    isos = ar.well_connected_components(prop_graph)
    print("isos = ",isos)
    elapsed_time = time.time() - start_time
    print(f"Arachne execution time: {elapsed_time} seconds")
    print(f"Arachne found: {len(isos)/4} isos")


    ak.shutdown()
