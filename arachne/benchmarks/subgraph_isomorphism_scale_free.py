import argparse
import time
import arachne as ar
import arkouda as ak
import numpy as np

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Benchmark for subgraph isomorphism."
    )
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("n", type=int, default=1000, help="Number of vertices for graph")
    script_parser.add_argument("m", type=int, default=2000, help="Number of edges for graph")
    script_parser.add_argument("x", type=int, default=5, help="Number of labels for graph")
    script_parser.add_argument("y", type=int, default=10, help="Number of relationships for graph")
    script_parser.add_argument("s", type=int, default=2, help="Random seed for reproducibility")

    return script_parser

def add_edges_pref_attach(src, dst, m, current_node, node_degrees):
    """Add edges to new node using preferential attachment."""
    total_degree = np.sum(node_degrees)
    if total_degree > 0:
        probs = node_degrees / total_degree
        target_nodes = np.random.choice(a=current_node, size=m, replace=False, p=probs)
        for target_node in target_nodes:
            src.append(current_node)
            dst.append(target_node)
            node_degrees[target_node] += 1
    return src, dst, node_degrees

if __name__ == "__main__":
    #### Command line parser and extraction.
    parser = create_parser()
    args = parser.parse_args()

    #### Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)


    ### Get Arkouda server configuration information.
    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")

    ### Generate a scale-free network
    m = 2  # Number of edges to attach from new node to existing nodes
    m0 = max(5, m)  # Initial number of interconnected nodes

    src = []
    dst = []
    node_degrees = np.zeros(args.n)

    # Create initial interconnected network
    for i in range(m0):
        for j in range(i+1, m0):
            src.append(i)
            dst.append(j)
            node_degrees[i] += 1
            node_degrees[j] += 1

    # Add new nodes with preferential attachment
    for current_node in range(m0, args.n):
        src, dst, node_degrees = add_edges_pref_attach(src, dst, m, current_node, node_degrees)

    src_ak = ak.array(src)
    dst_ak = ak.array(dst)

    # ... [Continue with the rest of your original code for graph construction]
