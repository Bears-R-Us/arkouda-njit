import arkouda as ak
import arachne as ar
import pandas as pd
import time as time
import networkx as nx
import random
import argparse
from dotmotif import Motif, GrandIsoExecutor 

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    #script_parser.add_argument("m", type=int, default=2000, help="Number of edges for graph")
    script_parser.add_argument("x", type=int, default=5, help="Number of labels for graph")
    script_parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")
    #script_parser.add_argument("s", type=int, default=2, help="Random seed for reproducibility")
    script_parser.add_argument('--print_isos', action='store_true', help="Print isos?")

    return script_parser

if __name__ == "__main__":
    #### Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()
    #check
    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    ### Get Arkouda server configuration information.
    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")



    # Define the file path to your graph dataset
    file_path = '/scratch/users/md724/DataSets/web-BerkStan/web-BerkStan.txt'


    # Load the dataset into a DataFrame, skipping the initial comments
    df = pd.read_csv(file_path, delim_whitespace=True, comment='#', header=None, names=['FromNodeId', 'ToNodeId'])

    df.rename(columns={'FromNodeId': 'src', 'ToNodeId': 'dst'}, inplace=True)

    df['type'] = 'T1'

    # Display the first few rows of the DataFrame to verify it loaded correctly
    print(df.head())
    # Concatenate 'src' and 'dst' columns and find unique elements for nodes
    unique_nodes = pd.concat([df['src'], df['dst']]).unique()

    # Number of unique nodes
    num_unique_nodes = len(unique_nodes)

    # Number of edges is the length of the DataFrame
    num_edges = len(df)
    d = num_edges/(num_unique_nodes*(num_unique_nodes -1))
    print(f"Graph Density: {d}")

    print(f"Number of unique nodes: {num_unique_nodes}")
    print(f"Number of edges: {num_edges}")

    unique_nodes = pd.concat([df['src'], df['dst']]).unique()

    # Number of unique nodes
    num_unique_nodes = len(unique_nodes)

    # Number of edges is the length of the DataFrame
    num_edges = len(df)
    d = num_edges/(num_unique_nodes*(num_unique_nodes -1))
    print(f"Graph Density: {d}")

    print(f"Number of unique nodes: {num_unique_nodes}")
    print(f"Number of edges: {num_edges}")


    ak_df= ak.DataFrame(df)
 
    ar_df = ar.PropGraph()
    ar_df.load_edge_attributes(ak_df, source_column="src", destination_column="dst", relationship_columns=["type"])

    all_nodes = ak.concatenate([ak_df['src'],ak_df['dst']])
    unique_nodes = ak.unique(all_nodes)
    #unique_nodes.size
    lbls = ak.array(["1"]*unique_nodes.size)
    df_node_df = ak.DataFrame({"nodes": unique_nodes, "lbls":lbls})

    ar_df.load_node_attributes(df_node_df,node_column="nodes", label_columns=["lbls"])
                                    

    print("Data loaded now we are loading the subraph....")

    subgraph = ar.PropGraph()
    motif = Motif("""
    A -> B 
    C -> B
    """)
    src_subgraph = ak.array([0, 2])
    dst_subgraph = ak.array([1, 1])
    lbls_subgraph = ak.array(["1"]*3)
    rels_subgraph = ak.array(["T1"]*len(src_subgraph))

    edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph, "rels":rels_subgraph})
    node_df_h = ak.DataFrame({"nodes": ak.arange(0,3), "lbls":lbls_subgraph})
    subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                    relationship_columns=["rels"])
    subgraph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls"])


    #prop_graph= ar_celegans
    prop_graph= ar_df
    # Grab vertex and edge data from the Arachne dataframes.
    graph_node_information = prop_graph.get_node_attributes()
    graph_edge_information = prop_graph.get_edge_attributes()
    subgraph_node_information = subgraph.get_node_attributes()
    subgraph_edge_information = subgraph.get_edge_attributes()




    # Convert Arkouda dataframes to Pandas dataframes to NetworkX graph attributes.
    G = nx.from_pandas_edgelist(graph_edge_information.to_pandas(), source='src',
                                target='dst', edge_attr=True, create_using=nx.DiGraph)
    H = nx.from_pandas_edgelist(subgraph_edge_information.to_pandas(), source='src',
                                    target='dst', edge_attr=True, create_using=nx.DiGraph)

    # Convert graph node attributes to Pandas dfs, remove nodes, and convert rows to dicts.
    graph_node_attributes = graph_node_information.to_pandas()
    graph_nodes_from_df = list(graph_node_attributes.pop("nodes"))
    graph_node_attributes = graph_node_attributes.to_dict('index')
    graph_node_attributes_final = {}

    # Convert subgraph node attributes to Pandas dfs remove nodes, and convert rows to dicts.
    subgraph_node_attributes = subgraph_node_information.to_pandas()
    subgraph_nodes_from_df = list(subgraph_node_attributes.pop("nodes"))
    subgraph_node_attributes = subgraph_node_attributes.to_dict('index')
    subgraph_node_attributes_final = {}


        # Convert Pandas index to original node index.
    for key in graph_node_attributes:
        graph_node_attributes_final[graph_nodes_from_df[key]] = graph_node_attributes[key]

    for key in subgraph_node_attributes:
            subgraph_node_attributes_final[subgraph_nodes_from_df[key]] = subgraph_node_attributes[key]



        # Set the node attributes for G and H from dicts.
    nx.set_node_attributes(G, graph_node_attributes_final)
    nx.set_node_attributes(H, subgraph_node_attributes_final)



    print(" Arachne....")
    start = time.time()
    #isos = ar.subgraph_isomorphism(ar_celegans, subgraph)
    isos = ar.subgraph_isomorphism(prop_graph, subgraph)
    end = time.time()
    print(f"Finding {len(isos)/3} monomorphisms took {end-start} secs")
    print("************************************************************")
    print(" NetworkX... ")

        # Find subgraph isomorphisms of H in G.
    start_time = time.time()
    GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)
    subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())
    elapsed_time = time.time() - start_time
    print(f"NetworkX execution time: {elapsed_time} seconds")
    print(f"NetworkX found: {len(subgraph_isomorphisms)} isos")
    print("************************************************************")
    
    print(" DotMotif....")
    E = GrandIsoExecutor(graph=G)

    # Create the search engine.

    start = time.time()

    results = E.find(motif)
    elapsed_time = time.time() - start_time
    print(f"DotMotif execution time: {elapsed_time} seconds")
    print(f"Dotmotif found: {len(subgraph_isomorphisms)} isos")
    print(len(results))

    ak.shutdown()
