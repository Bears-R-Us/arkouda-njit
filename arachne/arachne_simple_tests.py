import argparse
import arkouda as ak
import arachne as ar 
import numpy as np

def create_parser():
    parser = argparse.ArgumentParser(
        description="Measure the performance of breadth-first search on a graph. Must be preprocessed!"
    )
    parser.add_argument("hostname", help="Hostname of arkouda server")
    parser.add_argument("port", type=int, help="Port of arkouda server")
    
    return parser

if __name__ == "__main__":    
    parser = create_parser()
    args = parser.parse_args()
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    # Build graph from an array.
    src = ak.array([34, 23, 34, 23, 23, 89, 56, 78, 42, 56, 45, 12, 34, 54, 34, 45, 67, 86, 74, 65])
    dst = ak.array([23, 34, 89, 89, 89, 89, 78, 23, 34, 23, 23, 34, 17, 13, 11, 45, 89, 89, 34, 89])
    graph = ar.Graph()
    print(f"src = {src}")
    print(f"dst = {dst}\n")
    graph.add_edges_from(src,dst)

    ak.shutdown()