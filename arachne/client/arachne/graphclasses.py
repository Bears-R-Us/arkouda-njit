"""Contains the three graph classes that users can build: `Graph` (for undirected graphs), `DiGraph` 
(for directed graphs), and `PropGraph` (for property graphs that are inherently directed). `Graph` 
and `DiGraph` support weights on edges, but `PropGraph` does not since it supports types and 
properties on vertices and edges.
"""

from __future__ import annotations
from typing import cast, Tuple, Union
import time
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray
from arkouda.logger import getArkoudaLogger
from arkouda.dtypes import int64 as akint

__all__ = ["Graph", "DiGraph", "PropGraph"]

class Graph:
    """Base class for undirected graphs. 

    This is the double index graph data structure based graph representation. The graph data resides 
    on the arkouda server. The user should not call this class directly; rather its instances are 
    created by other arachne functions.

    Graphs hold undirected edges. Self loops and multiple edges are not allowed.

    Nodes currently are only allowed to be integers. They may contain optional key/value attributes.

    Edges are represented as links between nodes. They may contain optinal key/value attributes. 

    Parameters
    ----------
    None

    Attributes
    ----------
    n_vertices : int
        The number of vertices in the graph. 
    n_edges : int
        The number of edges in the graph.
    directed : int
        The graph is directed (True) or undirected (False).
    weighted : int
        The graph is weighted (True) or unweighted (False).
    name : string
        The name of the graph in the backend Chapel server. 
    logger : ArkoudaLogger
        Used for all logging operations.

    See Also
    --------
    DiGraph
        
    Notes
    -----
    """

    def __init__(self, *args) -> None:
        """Initializes the Graph instance by setting all instance
        attributes, some of which are derived from the array parameters.
        
        Parameters
        ----------
        n_vertices
            Must be provided in args[0].
        n_edges
            Must be provided in args[1].
        weighted
            Must be provided in args[3].
        name
            Must be provided in args[4].
        directed
            Defaults to 0 since Graph is inherently undirected. If needed,
            should be found in args[2].
        
            
        Returns
        -------
        None
        
        Raises
        ------
        RuntimeError
            Raised if there's an error from the server to create a graph.  
        ValueError
            Raised if not enough arguments are passed to generate the graph. 
        """
        try:
            if len(args) < 5:
                self.n_vertices = 0
                self.n_edges = 0
                self.weighted = None
                self.directed = 0
                self.name = None
            else:
                self.n_vertices = int(cast(int, args[0]))
                self.n_edges = int(cast(int, args[1]))
                self.weighted = int(cast(int, args[3]))
                oriname = cast(str, args[4])
                self.name = oriname.strip()
                self.directed = 0
        except Exception as error:
            raise RuntimeError(error)

        self.dtype = akint
        self.logger = getArkoudaLogger(name=__class__.__name__)

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
        repMsg = generic_msg(cmd=cmd, args=args)
        returned_vals = (cast(str, repMsg).split('+'))

        return create_pdarray(returned_vals[0]), create_pdarray(returned_vals[1])

    def degree(self) -> pdarray:
        """Returns the degree view for the whole graph as a pdarray. The format is NOTE: self-loops 
        count twice to the degree count due to the sum of degree theorem.

        Returns
        -------
        degree: pdarray
            The array containing the degree for each node.
        """
        src,dst = self.edges()
        degree = ak.GroupBy(src, assume_sorted=True).count()[1]
        self_loops = src == dst
        degree[src[self_loops]] += 1

        return degree

    def add_edges_from(self, akarray_src:pdarray, akarray_dst:pdarray,
                       akarray_weight:Union[None,pdarray] = None) -> None:
        """
        Populates the graph object with edges as defined by the akarrays. Uses an Arkouda-based
        reading version. 

        Returns
        -------
        None
        """
        cmd = "addEdgesFrom"

        ### Edge dedupping and delooping.
        # 1. Symmetrize the graph by concatenating the src to dst arrays and vice versa.
        src = ak.concatenate([akarray_src, akarray_dst])
        dst = ak.concatenate([akarray_dst, akarray_src])
        num_original_edges = src.size

        # 1a. Initialize and symmetrize the weights of each edge, if applicable.
        wgt = ak.array([1.0])
        if isinstance(akarray_weight,pdarray):
            wgt = ak.concatenate([akarray_weight, akarray_weight])
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
        if self_loops.size == 1:
            self_loops = 0 # This is our x.
        else:
            self_loops = self_loops[1]  # This is our x.

        num_edges_after_dedup = src.size
        num_removed_edges = num_original_edges - num_edges_after_dedup # This is our z.
        num_dupped_edges = (num_removed_edges - self_loops) / 2 # This is solving for y.
        num_edges = akarray_src.size - num_dupped_edges
        
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

    def add_edges_from_compat(self, akarray_src:pdarray, akarray_dst:pdarray) -> None:
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

class DiGraph(Graph):
    """Base class for directed graphs. Inherits from Graph.

    This is the double index graph data structure based graph representation. The graph data resides 
    on the arkouda server. The user should not call this class directly; rather its instances are 
    created by other arachne functions.

    DiGraphs hold directed edges. Self loops and multiple edges are not allowed.

    Nodes currently are only allowed to be integers. They may contain optional key/value attributes.

    Edges are represented as directed links between nodes. They may contain optional key/value 
    attributes. 

    Parameters
    ----------
    None

    Attributes
    ----------
    n_vertices : int
        The number of vertices in the graph. 
    n_edges : int
        The number of edges in the graph.
    directed : int
        The graph is directed (True) or undirected (False).
    weighted : int
        The graph is weighted (True) or unweighted (False).
    name : string
        The name of the graph in the backend Chapel server. 
    logger : ArkoudaLogger
        Used for all logging operations.

    See Also
    --------
    Graph
        
    Notes
    -----
    """

    def __init__(self, *args) -> None:
        """Initializes the Graph instance by setting all instance
        attributes, some of which are derived from the array parameters.
        
        Parameters
        ----------
        n_vertices
            Must be provided in args[0].
        n_edges
            Must be provided in args[1].
        weighted
            Must be provided in args[3].
        name
            Must be provided in args[4].
        directed
            Defaults to 1 since DiGraph is inherently directed. If needed,
            should be found in args[2].
         
        Returns
        -------
        None
        
        Raises
        ------
        RuntimeError
            Raised if there's an error from the server to create a graph.   
        ValueError
            Raised if not enough arguments are passed to generate the graph. 
        """
        try:
            if len(args) < 5:
                self.n_vertices = 0
                self.n_edges = 0
                self.weighted = None
                self.directed = 1
                self.name = None
            else:
                self.n_vertices = int (cast(int, args[0]))
                self.n_edges = int(cast(int, args[1]))
                self.weighted = int(cast(int, args[3]))
                oriname = cast(str, args[4])
                self.name = oriname.strip()
                self.directed = 1
        except Exception as e:
            raise RuntimeError(e)

        self.dtype = akint
        self.logger = getArkoudaLogger(name=__class__.__name__)

    def out_degree(self) -> pdarray:
        """Returns the out degree view for the whole graph as a pdarray.

        Returns
        -------
        out_degree: pdarray
            The array containing the out_degrees for each node.
        """
        src = self.edges()[0]
        
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
        dst = self.edges()[1]

        in_degree_keys,in_degree_count = ak.GroupBy(dst).count()
        in_degree = ak.full(self.n_vertices, 0, dtype=ak.int64)
        in_degree[in_degree_keys] = in_degree_count

        return in_degree

    def add_edges_from(self, akarray_src:pdarray, akarray_dst:pdarray,
                       akarray_weight:Union[None,pdarray] = None) -> None:
        """
        Populates the graph object with edges as defined by the akarrays. Uses an Arkouda-based
        reading version. 

        Returns
        -------
        None
        """
        cmd = "addEdgesFrom"

        ### Edge dedupping and delooping.
        # 1. Initialize the edge arrays.
        src = akarray_src
        dst = akarray_dst

        # 1a. Initialize the weights array, if applicable.
        wgt = ak.array([1.0])
        if isinstance(akarray_weight,pdarray):
            wgt = akarray_weight
            self.weighted = 1

        # 2. Sort the edges and remove duplicates.
        gb_edges = ak.GroupBy([src,dst])
        src = gb_edges.unique_keys[0]
        dst = gb_edges.unique_keys[1]
        if self.weighted == 1:
            wgt = gb_edges.aggregate(wgt, "sum")[1]

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
        self.n_edges = int(src.size)

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
        args = { "AkArraySrc" : src,
                 "AkArrayDst" : dst,
                 "AkArraySeg" : segs,
                 "AkArraySrcR" : src_reversed,
                 "AkArrayDstR" : dst_reversed,
                 "AkArraySegR" : segs_reversed,
                 "AkArrayWeight" : wgt,
                 "AkArrayVmap" : vmap,
                 "Directed": bool(self.directed),
                 "Weighted" : bool(self.weighted),
                 "NumVertices" : self.n_vertices,
                 "NumEdges" : self.n_edges }

        rep_msg = generic_msg(cmd=cmd, args=args)
        oriname = rep_msg
        self.name = oriname.strip()

class PropGraph(DiGraph):
    """Base class for property graphs. Inherits from `DiGraph`. This is the double index graph data 
    structure based graph representation. The graph data resides on the arkouda server. 

    Parameters
    ----------
    None

    Attributes
    ----------
    n_vertices : int
        The number of vertices in the graph. 
    n_edges : int
        The number of edges in the graph.
    directed : int
        The graph is directed (True) or undirected (False).
    weighted : int
        The graph is weighted (True) or unweighted (False).
    multied : int
        The graph is a multi graph (True) or not a multi graph (False).
    name : string
        The name of the graph in the backend Chapel server.
    logger : ArkoudaLogger
        Used for all logging operations.

    See Also
    --------
    Graph
        
    Notes
    -----
    """

    def __init__(self, *args) -> None:
        """Initializes the Graph instance by setting all instance
        attributes, some of which are derived from the array parameters.
        
        Parameters
        ----------
        n_vertices
            Must be provided in args[0].
        n_edges
            Must be provided in args[1].
        weighted
            Must be provided in args[3].
        name
            Must be provided in args[4].
        directed
            Defaults to 1 since PropGraph is inherently directed. If needed,
            should be found in args[2].
         
        Returns
        -------
        None
        
        Raises
        ------
        RuntimeError
            Raised if there's an error from the server to create a graph.   
        ValueError
            Raised if not enough arguments are passed to generate the graph. 
        """
        try:
            if len(args) < 5:
                self.n_vertices = 0
                self.n_edges = 0
                self.weighted = None
                self.directed = 1
                self.multied = 0
                self.name = None
            else:
                self.n_vertices = int (cast(int, args[0]))
                self.n_edges = int(cast(int, args[1]))
                self.weighted = int(cast(int, args[3]))
                oriname = cast(str, args[4])
                self.name = oriname.strip()
                self.directed = 1
                self.multied = 0
        except Exception as err:
            raise RuntimeError(err)

        self.dtype = akint
        self.logger = getArkoudaLogger(name=__class__.__name__)

    def _add_edges_from(self, akarray_src:pdarray, akarray_dst:pdarray) -> None:
        # NOTE: This will eventually be a way to allow multiedges in a property graph, but it will
        #       be only allowed of edges are specified with a relationship. DOES NOT WORK.
        """
        Populates the graph object with edges as defined by the akarrays.

        Returns
        -------
        None
        """
        cmd = "addEdgesFrom"

        ### Initialize the edge arrays.
        src = akarray_src
        dst = akarray_dst
        wgt = ak.array([-1]) # just a placeholder for now

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
        # 1. Build the neighbors of the adjacency lists for each vertex.
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
        self.n_edges = int(src.size)

        ### Store everything in a graph object in the Chapel server.
        # 1. Store data into an Graph object in the Chapel server.
        args = { "AkArraySrc" : src,
                 "AkArrayDst" : dst,
                 "AkArraySeg" : segs,
                 "AkArrayWeight" : wgt,
                 "AkArrayVmap" : vmap,
                 "Directed": bool(self.directed),
                 "Weighted" : bool(self.weighted),
                 "Multied" : bool(self.multied),
                 "NumVertices" : self.n_vertices,
                 "NumEdges" : self.n_edges }

        rep_msg = generic_msg(cmd=cmd, args=args)
        oriname = rep_msg
        self.name = oriname.strip()

    def add_node_labels(self, labels:ak.DataFrame) -> None:
        """Populates the graph object with labels from a dataframe. Passed dataframe should follow
        the same format specified in the Parameters section below.
        
        Parameters
        ----------
        labels : ak.DataFrame
            `ak.DataFrame({"vertex_ids" : vertices, "vertex_labels" : labels})`

        Returns
        -------
        None
        """
        cmd = "addNodeLabels"

        ### Preprocessing steps for faster back-end array population.
        # 0. Extract the vertex ids and vertex labels from the dataframe.
        columns = labels.columns
        vertex_ids = labels[columns[0]]
        vertex_labels = labels[columns[1]]

        # 1. Broadcast string label names to int values and extract the label str to int id map.
        gb_labels = ak.GroupBy(vertex_labels)
        new_label_ids = ak.arange(gb_labels.unique_keys.size)
        vertex_labels = gb_labels.broadcast(new_label_ids)
        label_mapper = gb_labels.unique_keys

        # 2. Convert the vertex_ids to internal vertex_ids.
        vertex_map = self.nodes()
        inds = ak.in1d(vertex_ids, vertex_map)
        vertex_ids = vertex_ids[inds]
        vertex_labels = vertex_labels[inds]
        vertex_ids = ak.find(vertex_ids, vertex_map)

        # 3. GroupBy of the vertex ids and labels.
        gb_vertex_ids_and_labels = ak.GroupBy([vertex_ids,vertex_labels])
        vertex_ids = gb_vertex_ids_and_labels.unique_keys[0]
        vertex_labels = gb_vertex_ids_and_labels.unique_keys[1]

        arrays = vertex_ids.name + " " + vertex_labels.name + " " + label_mapper.name
        args = { "GraphName" : self.name,
                 "Arrays" : arrays,
               }
        rep_msg = generic_msg(cmd=cmd, args=args)

    def add_node_properties(self, node_properties:ak.DataFrame) -> None:
        """Populates the graph object with properties derived from the columns of a dataframe. Node
        proprties are different from node labels where labels are always strings and can be 
        considered an extra identifier for different types of nodes. On the other hand, properties
        are key-value pairs more akin to storing the columns of a dataframe.
        
        Parameters
        ----------
        properties : ak.DataFrame
            `ak.DataFrame({"vertex_ids" : vertex_ids,
                           "property1" : property1, ..., "propertyN" : propertyN})`

        See Also
        --------
        add_node_labels, add_edge_relationships, add_edge_properties

        Notes
        -----
        
        Returns
        -------
        None
        """
        cmd = "addNodeProperties"

        ### Preprocessing steps for faster back-end array population.
        # 0. Perform a groupby and extract the sorted column names of the dataframe.
        start = time.time()
        columns = node_properties.columns
        node_properties_gb = node_properties.groupby([columns[0]])
        new_rows = node_properties_gb.permutation[node_properties_gb.segments]
        node_properties = node_properties[new_rows]
        end = time.time()
        print(f"Performing large groupby on input dataframe took {end-start} secs")

        # 1. Convert the vertex_ids to internal vertex_ids.
        start = time.time()
        vertex_map = self.nodes()
        vertex_ids = node_properties[columns[0]]
        inds = ak.in1d(vertex_ids, vertex_map)
        node_properties = node_properties[inds]
        vertex_ids = node_properties[columns[0]]
        vertex_ids = ak.find(vertex_ids, vertex_map)
        end = time.time()
        print(f"Generating internal indices took {end-start} secs")

        # 2. Remove the first column name, vertex ids, since those are sent separately.
        columns.remove(columns[0])
        vertex_properties = ak.array(columns)

        # 3. Extract symbol table names of arrays to use in the back-end.
        data_array_names = []
        for column in columns:
            data_array_names.append(node_properties[column].name)
        data_array_names = ak.array(data_array_names)

        perm = ak.GroupBy(vertex_properties).permutation
        vertex_properties = vertex_properties[perm]
        data_array_names = data_array_names[perm]

        args = { "GraphName" : self.name,
                 "VertexIdsName" : vertex_ids.name,
                 "PropertyMapperName" : vertex_properties.name,
                 "DataArrayNames" : data_array_names.name
               }
        start = time.time()
        rep_msg = generic_msg(cmd=cmd, args=args)
        end = time.time()

        internal_timings = rep_msg.split("+")
        print(f"Extracting datatypes per column took {internal_timings[0]} secs")
        print(f"Initializaing entire two-dimensional array took {internal_timings[1]} secs")
        print(f"Processing every column sequentially took {internal_timings[2]} secs")
        print(f"Cumulatively running Chapel code took {end-start} secs")

    def add_edge_relationships(self, relationships:ak.DataFrame) -> None:
        """Populates the graph object with edge relationships from a dataframe. Passed dataframe 
        should follow the same format specified in the Parameters section below.
        
        Parameters
        ----------
        relationships : ak.DataFrame
            `ak.DataFrame({"src" : src, "dst" : dst, "edge_relationships" : edge_relationships})`

        Returns
        -------
        None
        """
        cmd = "addEdgeRelationships"

        ### Preprocessing steps for faster back-end array population.
        # 0. Extract the source and destination vertex ids and the relationships from the dataframe.
        columns = relationships.columns
        src_vertex_ids = relationships[columns[0]]
        dst_vertex_ids = relationships[columns[1]]
        edge_relationships = relationships[columns[2]]

        # 1. Broadcast string relationship names to int values and extract the relationship str to
        #    int id map.
        gb_relationships = ak.GroupBy(edge_relationships)
        new_relationship_ids = ak.arange(gb_relationships.unique_keys.size)
        edge_relationships = gb_relationships.broadcast(new_relationship_ids)
        relationship_mapper = gb_relationships.unique_keys

        # 2. Convert the source and destination vertex ids to the internal vertex_ids.
        vertex_map = self.nodes()
        src_vertex_ids = ak.find(src_vertex_ids, vertex_map)
        dst_vertex_ids = ak.find(dst_vertex_ids, vertex_map)

        # 3. Ensure all edges are actually present in the underlying graph data structure.
        edges = self.edges()
        edge_inds = ak.in1d([src_vertex_ids,dst_vertex_ids],[edges[0],edges[1]])
        src_vertex_ids = src_vertex_ids[edge_inds]
        dst_vertex_ids = dst_vertex_ids[edge_inds]
        edge_relationships = edge_relationships[edge_inds]

        # 4. GroupBy of the src and dst vertex ids and relationships to remove any duplicates.
        gb_edges_and_relationships = ak.GroupBy([src_vertex_ids,dst_vertex_ids,edge_relationships])
        src_vertex_ids = gb_edges_and_relationships.unique_keys[0]
        dst_vertex_ids = gb_edges_and_relationships.unique_keys[1]
        edge_relationships = gb_edges_and_relationships.unique_keys[2]

        # 5. Generate internal edge indices.
        internal_edge_indices = ak.find([src_vertex_ids,dst_vertex_ids],[edges[0],edges[1]])

        arrays = internal_edge_indices.name + " " + edge_relationships.name + " " + relationship_mapper.name
        args = {  "GraphName" : self.name,
                  "Arrays" : arrays }
        rep_msg = generic_msg(cmd=cmd, args=args)

    def add_edge_properties(self, edge_properties:ak.DataFrame) -> None:
        """Populates the graph object with properties derived from the columns of a dataframe. Edge
        properties are different from edge relationships where relationships are always strings and
        can be considered an extra identifier for different types of edges. On the other hand, 
        properties are key-value pairs more akin to storing the columns of a dataframe.
        
        Parameters
        ----------
        properties : ak.DataFrame
            `ak.DataFrame({"src_vertex_ids" : src_vertex_ids, "dst_vertex_ids" : dst_vertex_ids,
                           "property1" : property1, ..., "propertyN" : propertyN})`

        See Also
        --------
        add_node_labels, add_edge_relationships, add_node_properties

        Notes
        -----
        
        Returns
        -------
        None
        """
        cmd = "addEdgeProperties"

        ### Preprocessing steps for faster back-end array population.
        # 0. Extract the column names of the dataframe.
        start = time.time()
        columns = edge_properties.columns
        edge_properties_gb = edge_properties.groupby([columns[0],columns[1]])
        new_rows = edge_properties_gb.permutation[edge_properties_gb.segments]
        edge_properties = edge_properties[new_rows]
        src_vertex_ids = edge_properties[columns[0]]
        dst_vertex_ids = edge_properties[columns[1]]
        end = time.time()
        print(f"Performing large groupby on input dataframe took {end-start} secs")

        # 1. Convert the source and destination vertex ids to the internal vertex_ids.
        start = time.time()
        vertex_map = self.nodes()
        src_vertex_ids = ak.find(src_vertex_ids, vertex_map)
        dst_vertex_ids = ak.find(dst_vertex_ids, vertex_map)

        # 2. Generate the internal edge indices.
        edges = self.edges()
        internal_edge_indices = ak.find([src_vertex_ids,dst_vertex_ids],[edges[0],edges[1]])
        end = time.time()
        print(f"Generating internal indices took {end-start} secs")

        # 3. Remove the first two column names, edge ids, since those are sent separately.
        columns.remove(columns[0])
        columns.remove(columns[0])
        edge_property_names = ak.array(columns)

        # 4. Extract symbol table names of arrays to use in the back-end.
        data_array_names = []
        for column in columns:
            data_array_names.append(edge_properties[column].name)
        data_array_names = ak.array(data_array_names)

        perm = ak.GroupBy(edge_property_names).permutation
        edge_property_names = edge_property_names[perm]
        data_array_names = data_array_names[perm]

        args = { "GraphName" : self.name,
                 "EdgeIdsName" : internal_edge_indices.name,
                 "PropertyMapperName" : edge_property_names.name,
                 "DataArrayNames" : data_array_names.name
               }
        start = time.time()
        rep_msg = generic_msg(cmd=cmd, args=args)
        end = time.time()
        internal_timings = rep_msg.split("+")
        print(f"Extracting datatypes per column took {internal_timings[0]} secs")
        print(f"Initializaing entire two-dimensional array took {internal_timings[1]} secs")
        print(f"Processing every column sequentially took {internal_timings[2]} secs")
        print(f"Cumulatively running Chapel code took {end-start} secs")

    def load_edge_attributes(self, edge_attributes:ak.DataFrame,
                             source_column:str|None = None,
                             destination_column:str|None = None,
                             relationship_column:str|None = None) -> None:
        """Populates the graph object with attributes derived from the columns of a dataframe. Edge
        properties are different from edge relationships where relationships are used to tell apart
        multiple edges. On the other hand, properties are key-value pairs more akin to storing the 
        columns of a dataframe. The column to be used as the edge relationship can be denoted by 
        setting the `relationship_column` parameter.
        
        Parameters
        ----------
        edge_attributes : ak.DataFrame
            `ak.DataFrame({"src_vertex_ids" : src_vertex_ids, "dst_vertex_ids" : dst_vertex_ids,
                           "attribute1" : attribute1, ..., "attributeN" : attributeN})`
        source_column : str
            The column denoting the values to be treated as the source vertices of an edge in 
            a graph. If unset, the first column of `edge_attributes` is used. 
        destination_column : str
            The column denoting the values to be treated as the destination vertices of an edge in
            a graph. If unset, the second column of `edge_attributes` is used.
        relationship_column : str
            Name of the column to be used to denote the relationships of each edge. If unset, no
            column is used as relationships and multiple edges will be deleted.

        See Also
        --------
        add_node_labels, add_edge_relationships, add_node_properties, add_edge_properties

        Notes
        -----
        
        Returns
        -------
        None
        """
        cmd = "loadEdgeAttributes"
        columns = edge_attributes.columns
        source_column = columns[0] if source_column is None else source_column
        destination_column = columns[1] if destination_column is None else destination_column
        relationship_mapper = ak.array(["none"])

        ### Process the dataframe to sort its edges and all of its columns.
        # 1a. This will allow multiple edges by adding relationship as an extra identifier.
        if relationship_column is not None:
            gb_relationships = ak.GroupBy(edge_attributes[relationship_column])
            new_relationship_ids = ak.arange(gb_relationships.unique_keys.size)
            relationship_column = gb_relationships.broadcast(new_relationship_ids)
            relationship_mapper = gb_relationships.unique_keys
            edge_attributes_gb = edge_attributes.groupby( [ source_column,
                                                            destination_column,
                                                            relationship_column ] )
            new_rows = edge_attributes_gb.permutation[edge_attributes_gb.segments]
            edge_attributes = edge_attributes[new_rows]
            self.multied = 1
        # 1b. This will build a graph without multiple edges, since extra identification is required
        #     by the property graph data model to distinguish multiple edges.
        else:
            edge_attributes_gb = edge_attributes.groupby( [ source_column, destination_column ] )
            new_rows = edge_attributes_gb.permutation[edge_attributes_gb.segments]
            edge_attributes = edge_attributes[new_rows]
            self.multied = 0

        # 2. Initialize our src and destination arrays.
        src = edge_attributes[source_column]
        dst = edge_attributes[destination_column]

        ### Build the graph into memory.
        # 1a. Multigraph uses the PropGraph add_edges_from() method.
        if self.multied:
            self._add_edges_from(src, dst)
        # 1b. Simple graph uses the DiGraph add_edges_from() method.
        else:
            super().add_edges_from(src, dst)

        ### Prepare the columns that are to be sent to the back-end to be stored per-edge.
        # 1. Remove the first two column names, edge ids, since those are sent separately.
        columns.remove(source_column)
        columns.remove(destination_column)
        column_names = ak.array(columns)

        # 2. Extract symbol table names of arrays to use in the back-end.
        column_ids = []
        for column in columns:
            column_ids.append(edge_attributes[column].name)
        column_ids = ak.array(column_ids)

        # 3. Sort the strings in size and lexical order.
        perm = ak.GroupBy(column_names).permutation
        column_names = column_names[perm]
        column_ids = column_ids[perm]

        # 4. Generate internal indices for the edges.
        edges = self.edges()
        nodes = self.nodes()
        src = ak.find([src], [nodes])
        dst = ak.find([dst], [nodes])
        internal_indices = ak.find([src,dst], [edges[0],edges[1]])

        args = { "GraphName" : self.name,
                 "ColumnNames" : column_names.name,
                 "ColumnIdsName" : column_ids.name,
                 "InternalIndicesName" : internal_indices.name,
                 "RelationshipMapperName" : relationship_mapper.name
               }
        rep_msg = generic_msg(cmd=cmd, args=args)

    def get_node_labels(self) -> ak.Strings:
        """Returns the sorted object of node labels stored for the property graph.

        Parameters
        ----------
        None

        Returns
        -------
        Strings
            The original labels inputted as strings.
        """
        cmd = "getNodeLabels"
        args = { "GraphName" : self.name }
        rep_msg = generic_msg(cmd=cmd, args=args)

        return ak.Strings.from_return_msg(rep_msg)

    def get_node_properties(self) -> ak.Strings:
        """Returns the node properties of the property graph.

        Parameters
        ----------
        None

        Returns
        -------
        Strings
            The original properties inputted as strings.
        """
        cmd = "getNodeProperties"
        args = { "GraphName" : self.name }
        rep_msg = generic_msg(cmd=cmd, args=args)

        return ak.Strings.from_return_msg(rep_msg)

    def get_edge_relationships(self) -> ak.Strings:
        """Returns the sorted object of edge relationships stored for the property graph.

        Parameters
        ----------
        None

        Returns
        -------
        Strings
            The original relationships inputted as strings.
        """
        cmd = "getEdgeRelationships"
        args = { "GraphName" : self.name }
        rep_msg = generic_msg(cmd=cmd, args=args)

        return ak.Strings.from_return_msg(rep_msg)

    def get_edge_properties(self) -> ak.Strings:
        """Returns the edge properties of the property graph.

        Parameters
        ----------
        None

        Returns
        -------
        Strings
            The original properties inputted as strings.
        """
        cmd = "getEdgeProperties"
        args = { "GraphName" : self.name }
        rep_msg = generic_msg(cmd=cmd, args=args)

        return ak.Strings.from_return_msg(rep_msg)

    def query_labels( self,
                      labels_to_find:pdarray,
                      op:str = "and" ) -> pdarray:
        """Given pdarrays specifiying a subset of node labels, this function returns to the user a 
        pdarray with the nodes that contain the labels. The operator specifies the operation to be
        conducted at the back-end. If the vertex should contain all of the labels specified in
        `labels_to_find` then the operaator to use should be "and" otherwise use "or".

        Parameters
        ----------
        labels_to_find : pdarray
            A pdarray with node labels whose nodes are to be returned.
        op : str
            Operator to apply to the search, either "and" or "or". 
        
        Returns
        -------
        pdarray
            Vertex names that contain the nodes that match the query.
        """
        cmd = "queryLabels"

        # Get internal representation of the labels to find.
        labels_to_find = ak.find(labels_to_find, self.get_node_labels())

        args = {  "GraphName" : self.name,
                  "LabelsToFindName" : labels_to_find.name,
                  "Op" : op }

        rep_msg = generic_msg(cmd=cmd, args=args)

        ### Manipulate data to return the external vertex representations of the found nodes.
        # 1. Convert Boolean array to actual pdarray.
        vertices_bool = create_pdarray(rep_msg)

        # 2. Use Boolean array to index original vertex names.
        final_vertices:pdarray = self.nodes()[vertices_bool]

        return final_vertices

    def query_node_properties( self,
                               column:str, value,
                               op:str = "<" ) -> pdarray:
        """Given a property name, value, and operator, performs a query and returns the nodes that
        match the query. Adhere to the operators accepted and ensure the values passed match the
        same type of the property.

        Parameters
        ----------
        column : str
            String specifying the column being search within.
        op : str
            Operator to apply to the search. Candidates vary and are listed below:
            `int64`, `uint64`, `float64`: "<", ">", "<=", ">=", "==", "<>". 
            `bool`: "==", "<>".
            `str`: "contains".
        
        Returns
        -------
        pdarray
            Vertex names that contain the nodes that match the query.
        """
        cmd = "queryNodeProperties"

        args = {  "GraphName" : self.name,
                  "Column" : column,
                  "Value" : value,
                  "Op" : op }

        rep_msg = generic_msg(cmd=cmd, args=args)

        ### Manipulate data to return the external vertex representations of the found nodes.
        # 1. Convert Boolean array to actual pdarray.
        vertices_bool = create_pdarray(rep_msg)

        # 2. Use Boolean array to index original vertex names.
        final_vertices:pdarray = self.nodes()[vertices_bool]

        return final_vertices

    def query_relationships( self,
                             relationships_to_find:pdarray,
                             op:str = "and" ) -> (pdarray,pdarray):
        """Given a pdarray specifiying a subset of edge relationships, this function returns to the 
        user a tuple of pdarrays with the edges that contain the relationships. The operator 
        specifies the operation to be conducted at the back-end. If the edge should contain all of 
        the relationships specified in `relationships_to_find` then the operator should be "and"
        otherwise use "or".

        Parameters
        ----------
        relationships_to_find : pdarray
            A pdarray with edge relationships whose edges are to be returned.
        op : str
            Operator to apply to the search, either "and" or "or". 
        
        Returns
        -------
        (pdarray,pdarray)
            Source and destination vertex pairs that contain the specified edges.
        """
        cmd = "queryRelationships"

        # Get internal representation of the relationships to find.
        relationships_to_find = ak.find(relationships_to_find,self.get_edge_relationships())

        args = {  "GraphName" : self.name,
                  "RelationshipsToFindName" : relationships_to_find.name,
                  "Op" : op }

        rep_msg = generic_msg(cmd=cmd, args=args)

        ### Manipulate data to turn internal vertex names to external ones.
        # 1. Convert Boolean array to actual pdarray.
        edges_bool:pdarray = create_pdarray(rep_msg)

        # 2. Extract edges and nodes of the graph and convert them to original vertex names.
        edges, nodes = self.edges(), self.nodes()
        src, dst = edges[0], edges[1]
        src:pdarray = nodes[src]
        dst:pdarray = nodes[dst]
        src, dst = src[edges_bool], dst[edges_bool]

        return (src,dst)
    
    def query_edge_properties( self,
                               column:str, value,
                               op:str = "<" ) -> pdarray:
        """Given a property name, value, and operator, performs a query and returns the edges that
        match the query. Adhere to the operators accepted and ensure the values passed match the
        same type of the property.

        Parameters
        ----------
        column : str
            String specifying the column being search within.
        op : str
            Operator to apply to the search. Candidates vary and are listed below:
            `int64`, `uint64`, `float64`: "<", ">", "<=", ">=", "==", "<>". 
            `bool`: "==", "<>".
            `str`: "contains".
        
        Returns
        -------
        pdarray
            Source and destination node names that contain the edges that match the query.
        """
        cmd = "queryEdgeProperties"

        args = {  "GraphName" : self.name,
                  "Column" : column,
                  "Value" : value,
                  "Op" : op }

        rep_msg = generic_msg(cmd=cmd, args=args)

        ### Manipulate data to turn internal vertex names to external ones.
        # 1. Convert Boolean array to actual pdarray.
        edges_bool:pdarray = create_pdarray(rep_msg)

        # 2. Extract edges and nodes of the graph and convert them to original vertex names.
        edges, nodes = self.edges(), self.nodes()
        src, dst = edges[0], edges[1]
        src:pdarray = nodes[src]
        dst:pdarray = nodes[dst]
        src, dst = src[edges_bool], dst[edges_bool]

        return (src,dst)

    def one_path( self,
                  labels_to_find:pdarray, relationships_to_find:pdarray,
                  lbl_op:str = "and", rel_op:str = "and") -> (pdarray,pdarray):
        """Given two pdarrays specifying labels and relationship to find, this function returns to
        the user a tuple of pdarrays with the edges that are length one paths with the node and
        edge types specified. The operations `lbl_op` and `rel_op` specify the operation to be
        conducted at the back-end. If the operation is `and` then the returned edges and nodes will
        have all of the specified attributes, if it is `or` then at least one of the attributes
        has to match. These can mix and matched. 

        Parameters
        ----------
        labels_to_find : pdarray
            A pdarray with node labels whose nodes are to be returned.
        lbl_op : str
            Operator to apply to the search, either "and" or "or".
        relationships_to_find : pdarray
            A pdarray with edge relationships whose edges are to be returned.
        rel_op : str
            Operator to apply to the search, either "and" or "or".

        Returns
        -------
        (pdarray,pdarray)
            Source and destination vertex pairs that contain the length one paths.
        """
        # 1. Get the nodes and edges that contain the specified labels and relationships.
        nodes = self.query_labels(labels_to_find, lbl_op)
        edges = self.query_relationships(relationships_to_find, rel_op)

        # 2. Find the overlap of returned edges and returned nodes.
        src = ak.in1d(edges[0], nodes)
        dst = ak.in1d(edges[1], nodes)

        # 3. Perform a Boolean and operation to keep only the edges where nodes were also returned
        #    in a query.
        kept_edges = src & dst

        # 4. Extract the actual edges with original node names.
        src = edges[0][kept_edges]
        dst = edges[1][kept_edges]

        return (src, dst)
    