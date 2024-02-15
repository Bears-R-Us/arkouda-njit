"""Contains the graph class defintion for `Graph`."""

from __future__ import annotations
from typing import cast, Tuple, Union
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray

__all__ = ["Graph"]

class Graph:
    """Base class for undirected graphs in Arachne. This is the double index graph data structure 
    based graph representation. The graph data resides on the arkouda server.

    Graphs hold undirected edges. Multiple edges are not allowed. Self loops are allowed. Nodes 
    currently are only allowed to be integers. No attributes are allowed on nodes or vertices. 
    For this functionality please refer to `PropGraph`.

    Edges are represented as links between nodes.

    Attributes
    ----------
    n_vertices : int
        The number of vertices in the graph.
    n_edges : int
        The number of edges in the graph.
    directed : int
        The graph is directed (1) or undirected (0). Defaulted to 0.
    weighted : int
        The graph is weighted (1) or unweighted (0).
    name : string
        The name of the graph in the backend Chapel server.

    See Also
    --------
    DiGraph, PropGraph
    """

    def __init__(self) -> None:
        """Initializes an empty `Graph` instance."""
        self.n_vertices = 0
        self.n_edges = 0
        self.directed = 0
        self.weighted = None
        self.name = None

    def __len__(self) -> int:
        """Returns the number of vertices in the graph. Use: 'len(G)'.

        Returns
        -------
        n_vertices: int.
            The number of vertices in the graph.
        """
        return self.n_vertices

    def size(self) -> int:
        """Returns the number of edges in the graph. Use: 'G.size()'.

        Returns
        -------
        n_edges: int.
            The number of edges in the graph.
        """
        return self.n_edges

    def nodes(self) -> pdarray:
        """Returns the nodes of the graph as a pdarray. Use: 'G.nodes()'.

        Returns
        -------
        nodes: pdarray.
            The array containing the vertex information of a graph.
        """
        cmd = "nodes"
        args = {"GraphName" : self.name}
        repMsg = generic_msg(cmd=cmd, args=args)
        returned_vals = (cast(str, repMsg).split('+'))

        return create_pdarray(returned_vals[0])

    def edges(self) -> Tuple[pdarray, pdarray]:
        """Returns a tuple of pdarrays src and dst Use: 'G.edges()'.

        Returns
        -------
        (src, dst): tuple.
            The arrays containing the edge information of a graph.
        """
        cmd = "edges"
        args = {"GraphName" : self.name}
        rep_msg = generic_msg(cmd=cmd, args=args)
        returned_vals = (cast(str, rep_msg).split('+'))
        nodes = self.nodes()

        src = create_pdarray(returned_vals[0])
        dst = create_pdarray(returned_vals[1])

        src = nodes[src]
        dst = nodes[dst]

        return (src,dst)

    def _internal_edges(self) -> Tuple[pdarray, pdarray]:
        """Returns a tuple of pdarrays src and dst with internal vertex names.

        Returns
        -------
        (src, dst): tuple.
            The arrays containing the edge information of a graph.
        """
        cmd = "edges"
        args = {"GraphName" : self.name}
        rep_msg = generic_msg(cmd=cmd, args=args)
        returned_vals = (cast(str, rep_msg).split('+'))

        src = create_pdarray(returned_vals[0])
        dst = create_pdarray(returned_vals[1])

        return (src,dst)

    def degree(self) -> pdarray:
        """Returns the degree view for the whole graph as a pdarray. NOTE: self-loops count twice in 
        the degree count due to the sum of degree theorem.

        Returns
        -------
        degree: pdarray
            The array containing the degree for each node.
        """
        (src,dst) = self._internal_edges()
        degree = ak.GroupBy(src, assume_sorted=True).count()[1]
        self_loops = src == dst
        degree[src[self_loops]] += 1

        return degree

    def add_edges_from(self,
                       input_src:pdarray,
                       input_dst:pdarray,
                       input_weight:Union[None,pdarray] = None,
                       remove_self_loops:bool = False,
                       assume_sorted:bool = False,
                       generate_reversed_arrays:bool = True) -> None:
        """
        Populates the graph with edges and vertices from the given input Arkouda arrays. Lets
        weights also be declared.
        
        Parameters
        ----------
        input_src : pdarray
            Source vertices of the graph to be inputted.
        input_dst : pdarray
            Destination vertices of the graph to be inputted.
        remove_self_loops : bool
            Remove self loops during graph building.
        assume_sorted : bool
            If the edges are already sorted, skips some operations. 
        generate_reversed_arrays : bool
            Some algorithms such as k-truss and connected components are optimized for the reversed
            DI data structure that requires a modified view of the edge list. NOTE: Set to on by 
            default, must be manually turned off.

        Returns
        -------
        None
        """
        cmd = "addEdgesFrom"

        ### Edge dedupping and delooping.
        # 1. Symmetrize the graph by concatenating the src to dst arrays and vice versa.
        src = ak.concatenate([input_src, input_dst])
        dst = ak.concatenate([input_dst, input_src])
        num_original_edges = src.size

        # 1a. Initialize and symmetrize the weights of each edge, if applicable.
        wgt = ak.array([1.0])
        if isinstance(input_weight, pdarray):
            wgt = ak.concatenate([input_weight, input_weight])
            self.weighted = 1

        # 2. Sort the edges and remove duplicates.
        gb_edges = ak.GroupBy([src, dst])
        src = gb_edges.unique_keys[0]
        dst = gb_edges.unique_keys[1]
        if bool(self.weighted):
            wgt = gb_edges.aggregate(wgt, "sum")[1]

        # 3. Calculate the number of edges that were removed. Due to symmetrization there will be
        #    an extra copy of self-loops. If the total number of edges removed is z after
        #    symmetrization then x of these are an extra copy of the self-loop. If there are copies
        #    of an edge either as u~v or v~u then there will be an extra copy yielded after
        #    symmetrizing. We will refer to the number of dedupped edges as y. They yield a total of
        #    2y to the total number of edges removed, z. Therefore, we are solving the basic
        #    algebraic problem of 2y + x = z where x and z are known for the graph after performing
        #    the dedupping in the step above.
        self_loops = src == dst
        self_loops = ak.value_counts(self_loops)[1]
        self_loops = 0 if self_loops.size == 1 else self_loops[1]

        num_edges_after_dedup = src.size
        num_removed_edges = num_original_edges - num_edges_after_dedup # This is our z.
        num_dupped_edges = (num_removed_edges - self_loops) / 2 # This is solving for y.
        num_edges = input_src.size - num_dupped_edges

        ### Vertex remapping.
        # 1. Extract the unique vertex names of the graph.
        gb_src_vertices = ak.GroupBy(src)
        gb_dst_vertices = ak.GroupBy(dst)
        vmap = gb_src_vertices.unique_keys

        # 2. Create evenly spaced array within the range of the size of unique keys and broadcast
        #    the values of the new range to the original vertices.
        new_vertex_range = ak.arange(gb_src_vertices.unique_keys.size)
        src = gb_src_vertices.broadcast(new_vertex_range)
        dst = gb_dst_vertices.broadcast(new_vertex_range)

        ### Create vertex index arrays.
        # 1. Build the neighbors of the adjacency lists for each vertex.
        gb_vertices = ak.GroupBy(src, assume_sorted=True)
        gb_src_neighbors = gb_vertices.count()[1]

        # 2. Run a prefix (cumulative) sum on neis to get the starting indices for each vertex.
        segs = ak.cumsum(gb_src_neighbors)
        first_seg = ak.array([0])
        segs = ak.concatenate([first_seg, segs])

        # 3. Extract the number of vertices, edges, and weighted flag from the graph.
        self.n_vertices = int(vmap.size)
        self.n_edges = int(num_edges)

        ### Store everything in a graph object in the Chapel server.
        # 1. Store data into an Graph object in the Chapel server.
        args = { "AkArraySrc" : src,
                 "AkArrayDst" : dst,
                 "AkArraySeg" : segs,
                 "AkArrayWeight" : wgt,
                 "AkArrayVmap" : vmap,
                 "Directed": bool(self.directed),
                 "Weighted" : bool(self.weighted),
                 "NumVertices" : self.n_vertices,
                 "NumEdges" : self.n_edges }

        rep_msg = generic_msg(cmd=cmd, args=args)
        oriname = rep_msg
        self.name = oriname.strip()

    def _generate_reversed_di(self, akarray_src:pdarray, akarray_dst:pdarray) -> None:
        """
        Populates the graph object with edges as defined by the akarrays. Uses an Arkouda-based
        reading version, is here to provide compatibility with the original algorithmic 
        implementations for triangle counting, triangle centrality, k-truss, and connected
        components.

        Returns
        -------
        None
        """
        cmd = "addEdgesFromCompat"
        src, dst = akarray_src, akarray_dst
        srcR, dstR = akarray_dst, akarray_src

        ### Remove self-loops from both the regular arrays and the reversed arrays.
        self_loops = src == dst
        src = src[~self_loops]
        dst = dst[~self_loops]
        srcR = srcR[~self_loops]
        dstR = dstR[~self_loops]

        ### Remove dupllicated edges from the graph.
        # 1. First, for the regular edges.
        regular_edges_gb = ak.GroupBy([src, dst])
        src = regular_edges_gb.unique_keys[0]
        dst = regular_edges_gb.unique_keys[1]

        # 2. Secondly, for the reversed edges.
        reversed_edges_gb = ak.GroupBy([srcR, dstR])
        srcR = reversed_edges_gb.unique_keys[0]
        dstR = reversed_edges_gb.unique_keys[1]

        ### Remap the vertex names to a one-up mapping.
        # 1. Get the vertex mapping.
        vertices_gb = ak.GroupBy(ak.concatenate([src,dst]))
        vertices = vertices_gb.unique_keys

        # 2. Concatenate all the arrays and broadcast new values to them.
        new_vertex_range = ak.arange(vertices.size)
        all_vertices = ak.concatenate([src,dst,srcR,dstR])
        all_vertices_gb = ak.GroupBy(all_vertices)
        vmap = all_vertices_gb.unique_keys
        all_vertices = all_vertices_gb.broadcast(new_vertex_range)

        # 3. Extract the high ranges for each array in the big concatenated GroupBy.
        src_high = src.size
        dst_high = src_high + src.size
        srcR_high = dst_high + src.size
        dstR_high = srcR_high + src.size

        # 4. Extract the actual arrays with slicing.
        src = all_vertices[0:src_high]
        dst = all_vertices[src_high:dst_high]
        srcR = all_vertices[dst_high:srcR_high]
        dstR = all_vertices[srcR_high:dstR_high]

        ### Create vertex index arrays.
        # 1. Create full arrays of the size of the vertex set.
        nei = ak.full(vmap.size, 0, int)
        neiR = ak.full(vmap.size, 0, int)
        start_i = ak.full(vmap.size, -1, int)
        start_iR = ak.full(vmap.size, -1, int)

        # 2. Extract the neighbor count by doing a count on the number of times each vertex appears
        #    in src.
        gb_src = ak.GroupBy(src)
        gb_src_indices, gb_src_neighbors = gb_src.count()
        nei[gb_src_indices] = gb_src_neighbors

        # 2a. Same as 2 but for srcR.
        gb_srcR = ak.GroupBy(srcR)
        gb_srcR_indices, gb_srcR_neighbors = gb_srcR.count()
        neiR[gb_srcR_indices] = gb_srcR_neighbors

        # 3. Find where each vertex starts inside of src and srcR.
        start_i = ak.find(new_vertex_range, src)
        start_iR = ak.find(new_vertex_range, srcR)

        # 4. Extract vertex and edge number information.
        self.n_vertices = int(vmap.size)
        self.n_edges = int(src.size)
        self.weighted = 0

        ### Store everything in a graph object in the Chapel server.
        args = { "AkArraySrc" : src,
                 "AkArrayDst" : dst,
                 "AkArraySrcR" : srcR,
                 "AkArrayDstR" : dstR,
                 "AkArrayNei" : nei,
                 "AkArrayNeiR" : neiR,
                 "AkArrayStartIdx" : start_i,
                 "AkArrayStartIdxR" : start_iR,
                 "AkArrayVmap" : vmap,
                 "Directed": bool(self.directed),
                 "Weighted" : bool(self.weighted),
                 "NumVertices" : self.n_vertices,
                 "NumEdges" : self.n_edges }

        rep_msg = generic_msg(cmd=cmd, args=args)
        oriname = rep_msg
        self.name = oriname.strip()