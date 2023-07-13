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

    # First step of vertex remapping is to extract the unique keys of an array using GroupBy. 
    # The GroupBy takes a concatenation of both our src and dst arrays and returns the unique keys 
    # (vertex names) in sorted order and how many times each key appears.
    gb_vertices = ak.GroupBy(ak.concatenate([src,dst]))
    print(f"gb_vertices permutation = {gb_vertices.permutation}")
    print(f"gb_vertices unique keys = {gb_vertices.unique_keys} with size {gb_vertices.unique_keys.size}")
    print(f"hb_vertices num groups  = {gb_vertices.ngroups}\n")

    # Second step of vertex remapping, we use broadcast to generate the zero-up mapping of the 
    # vertices.
    new_vertex_range = ak.arange(gb_vertices.unique_keys.size)
    gb_vertices_remapped = gb_vertices.broadcast(new_vertex_range)
    print(f"new_vertex_range     = {new_vertex_range}")
    print(f"gb_vertices_remapped = {gb_vertices_remapped}\n")

    # Extract out the new edge arrays after they have been remapped. 
    src_remapped = gb_vertices_remapped[0:src.size]
    dst_remapped = gb_vertices_remapped[src.size:]
    print(f"src_remapped = {src_remapped}")
    print(f"dst_remapped = {dst_remapped}\n")

    # To see the values that mapped to each other, we can look at the output of arange and of unique
    # keys from the GroupBy.
    map_df = ak.DataFrame({"internal" : new_vertex_range, "external" : gb_vertices.unique_keys})
    print(f"*****MAPPING FROM OLD VERTEX NAME TO NEW VERTEX NAME*****")
    print(f"{map_df.__repr__}\n")

    # To double check we can do some indexing into gb_vertices unique keys. 
    print(f"Indexing with 7 should give us 45: {gb_vertices.unique_keys[7]}")
    print(f"Indexing with 8 should give us 54: {gb_vertices.unique_keys[8]}")
    print(f"Indexing with 3 should give us 17: {gb_vertices.unique_keys[3]}\n")

    # Next, we can symmetrize our graph. This means keeping two copies of every edge for when the
    # graph is undirected. We do this by concatenating our remapped arrays to each other. 
    src_sym = ak.concatenate([src_remapped,dst_remapped])
    dst_sym = ak.concatenate([dst_remapped,src_remapped])
    print(f"*****EDGE LIST AFTER SYMMETRYZING*****")
    edges_df = ak.DataFrame({"src" : src_sym, "dst" : dst_sym})
    print(f"{edges_df.__repr__}\n")

    # Now it is time for another GroupBy to sort the edge arrays together. It considers the keys to
    # to be both edge values at an index i together. This will also handle removing duplicated 
    # edges.
    gb_edges = ak.GroupBy([src_sym,dst_sym])
    print(f"size before GroupBy is {src_sym.size} and after GroupBy it is {gb_edges.unique_keys[0].size}")
    edges_df = ak.DataFrame({"src" : gb_edges.unique_keys[0], "dst" : gb_edges.unique_keys[1]})
    print(f"*****EDGE LIST AFTER DEDUPPING*****")
    print(f"{edges_df.__repr__}\n")
    src_sym_dedupped = gb_edges.unique_keys[0]
    dst_sym_dedupped = gb_edges.unique_keys[1]

    # Now, let us get rid of self loops by creating a mask on the indices that are equal to each
    # other. 
    loop_mask = src_sym_dedupped == dst_sym_dedupped
    src_sym_dedupped_delooped = src_sym_dedupped[~loop_mask]
    dst_sym_dedupped_delooped = dst_sym_dedupped[~loop_mask]
    print(f"size before delooping is {src_sym_dedupped.size} and after GroupBy it is {src_sym_dedupped_delooped}")
    print(f"*****EDGE LIST AFTER DELOOPING*****")
    edges_df = ak.DataFrame({"src" : src_sym_dedupped_delooped, "dst" : dst_sym_dedupped_delooped})
    print(f"{edges_df.__repr__}\n")

    ak.shutdown()