"""Contains the graph class defintion for `DiGraph`."""

from __future__ import annotations
from typing import Union
import arachne as ar
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray

__all__ = ["DiGraph"]

class DiGraph(ar.Graph):
    """Base class for directed graphs. Inherits from `Graph`. This is the double index graph data 
    structure based graph representation. The graph data resides on the arkouda server.

    DiGraphs hold directed edges. Multiple edges are not allowed. Self loops are allowed. Nodes 
    currently are only allowed to be unsigned integers. No attributes are allowed on nodes or 
    vertices. For this functionality please refer to `PropGraph`.

    Edges are represented as directed links between nodes.

    Attributes
    ----------
    directed : int
        The graph is directed (1) or undirected (0). Defaulted to 1.

    See Also
    --------
    Graph, PropGraph
    """

    def __init__(self) -> None:
        """Initializes an empty `DiGraph` instance."""
        super().__init__()
        self.directed = 1

    def out_degree(self) -> pdarray:
        """Returns the out degree view for the whole graph as a pdarray.

        Returns
        -------
        out_degree: pdarray
            The array containing the out_degrees for each node.
        """
        src = self._internal_edges()[0]

        out_degree_keys,out_degree_count = ak.GroupBy(src, assume_sorted=True).count()
        out_degree = ak.full(self.n_vertices, 0, dtype=ak.int64)
        out_degree[out_degree_keys] = out_degree_count

        return out_degree

    def in_degree(self) -> pdarray:
        """Returns the out degree view for the whole graph as a pdarray.

        Returns
        -------
        in_degree: pdarray
            The array containing the in_degrees for each node.
        """
        dst = self._internal_edges()[1]

        in_degree_keys,in_degree_count = ak.GroupBy(dst).count()
        in_degree = ak.full(self.n_vertices, 0, dtype=ak.int64)
        in_degree[in_degree_keys] = in_degree_count

        return in_degree

    def add_edges_from(self,
                       input_src:pdarray,
                       input_dst:pdarray,
                       input_weight:Union[None,pdarray] = None,
                       no_self_loops:bool = False,
                       generate_reversed_arrays:bool = False) -> None:
        """
        Populates the graph with edges and vertices from the given input Arkouda arrays. Lets
        weights also be declared.
        
        Parameters
        ----------
        input_src : pdarray
            Source vertices of the graph to be inputted.
        input_dst : pdarray
            Destination vertices of the graph to be inputted.
        input_wgt : pdarray
            Edge weights. 
        no_self_loops : bool
            Ignore self-loops during graph building.
        generate_reversed_arrays : bool
            Some algorithms such as k-truss and connected components are optimized for the reversed
            DI data structure that requires a modified view of the edge list. NOTE: Set to on by 
            default, must be manually turned off.

        Returns
        -------
        None
        """
        cmd = "insertComponents"

        ### Edge dedupping and delooping.
        # 1. Initialize the edge arrays.
        src = input_src
        dst = input_dst

        # 1a. Initialize the weights array, if applicable.
        wgt = ak.array([1.0])
        if isinstance(input_weight,pdarray):
            wgt = input_weight
            self.weighted = 1

        # 2. Sort the edges and remove duplicates.
        gb_edges = ak.GroupBy([src,dst])
        src = gb_edges.unique_keys[0]
        dst = gb_edges.unique_keys[1]
        if self.weighted == 1:
            wgt = gb_edges.aggregate(wgt, "sum")[1]

        # 3. Calculate the number of edges for the graph.
        self_loops = src == dst
        num_edges = 0
        if no_self_loops:
            src = src[~self_loops]
            dst = dst[~self_loops]

        num_edges = src.size

        ### Vertex remapping.
        # 1. Extract the unique vertex names of the graph.
        all_vertices = ak.concatenate([src,dst])
        gb_vertices = ak.GroupBy(all_vertices)
        vmap = gb_vertices.unique_keys

        # 2. Create evenly spaced array within the range of the size of unique keys and broadcast
        #    the values of the new range to the original vertices.
        new_vertex_range = ak.arange(gb_vertices.unique_keys.size)
        all_vertices = gb_vertices.broadcast(new_vertex_range)
        src = all_vertices[0:src.size]
        dst = all_vertices[src.size:]

        ### Create vertex index arrays.
        # 1. Build the out-neighbors of the adjacency lists for each vertex.
        gb_src = ak.GroupBy(src, assume_sorted = True)
        gb_src_indices, gb_src_neighbors = gb_src.count()
        neis = ak.full(gb_vertices.unique_keys.size, 0, dtype=ak.int64)
        neis[gb_src_indices] = gb_src_neighbors

        # 2. Run a prefix (cumulative) sum on neis to get the starting indices for each vertex.
        segs = ak.cumsum(neis)
        first_seg = ak.array([0])
        segs = ak.concatenate([first_seg, segs])

        # 3. Extract the number of vertices, edges, and weighted flag from the graph.
        self.n_vertices = int(vmap.size)
        self.n_edges = num_edges

        ### Create the reversed arrays for in-neighbor calculations.
        # 1. Reverse the edges and sort them.
        gb_edges_reversed = ak.GroupBy([dst, src])
        src_reversed = gb_edges_reversed.unique_keys[0]
        dst_reversed = gb_edges_reversed.unique_keys[1]

        # 2. Build the in-neighbors of the adjacency lists for each vertex.
        gb_src_reversed = ak.GroupBy(src_reversed, assume_sorted = True)
        gb_src_indices_reversed, gb_src_neighbors_reversed = gb_src_reversed.count()
        neis_reversed = ak.full(gb_vertices.unique_keys.size, 0, dtype=ak.int64)
        neis_reversed[gb_src_indices_reversed] = gb_src_neighbors_reversed

        # 3. Run a prefix (cumulative) sum on neis to get the starting indices for each vertex.
        segs_reversed = ak.cumsum(neis_reversed)
        first_seg_reversed = ak.array([0])
        segs_reversed = ak.concatenate([first_seg_reversed, segs_reversed])

        ### Store everything in a graph object in the Chapel server.
        # 1. Store data into an Graph object in the Chapel server.
        args = { "SRC_SDI" : src,
                 "DST_SDI" : dst,
                 "SEGMENTS_SDI" : segs,
                 "SRS_R_SDI" : src_reversed,
                 "DST_R_SDI" : dst_reversed,
                 "SEGMENTS_R_SDI" : segs_reversed,
                 "EDGE_WEIGHTS_SDI" : wgt,
                 "VERTEX_MAP_SDI" : vmap,
                 "Directed": bool(self.directed),
                 "Weighted" : bool(self.weighted),
                 "NumVertices" : self.n_vertices,
                 "NumEdges" : self.n_edges }

        if generate_reversed_arrays:
            raise NotImplementedError("reversed DI not implemented directed graphs, just use SDI")

        rep_msg = generic_msg(cmd=cmd, args=args)
        oriname = rep_msg
        self.name = oriname.strip()
    