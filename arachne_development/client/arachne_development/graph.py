"""Contains the three graph classes that users can build: `Graph` (for undirected graphs), `DiGraph` 
(for directed graphs), and `PropGraph` (for property graphs that are inherently directed). `Graph` 
and `DiGraph` support weights on edges, but `PropGraph` does not since it supports types and 
properties on vertices and edges.
"""

from __future__ import annotations
from typing import cast, Tuple, Union
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray
from arkouda.logger import getArkoudaLogger
from arkouda.dtypes import int64 as akint

from typeguard import typechecked

__all__ = ["Graph","DiGraph", "PropGraph", "graph_query",
           "rmat_gen", "graph_file_read",
           "graph_add_property",
           "graph_edgearray", 
           "graph_file_preprocessing",
           "graph_file_tonde",
           "graph_file_read_mtx",
           "graph_bfs",
           "graph_triangle",
           "graph_cc",
           "graph_diameter",
           "graph_tri_ctr",
           "stream_file_read",
           "stream_tri_cnt",
           "streamPL_tri_cnt",
           "graph_ktruss",
           "graph_jaccard_coefficient", 
           "graph_jaccard_hash" ]


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
                 "NumVertices" : self.n_vertices,
                 "NumEdges" : self.n_edges }

        rep_msg = generic_msg(cmd=cmd, args=args)
        oriname = rep_msg
        self.name = oriname.strip()

class PropGraph(DiGraph):
    """Base class for property graphs. Inherits from DiGraph.

    This is the double index graph data structure based graph representation. The graph data resides 
    on the arkouda server. The user should not call this class directly; rather its instances are 
    created by other arachne functions.

    PropGraphs hold directed edges. Self loops and multiple edges are allowed.

    Nodes currently are only allowed to be integers. They can contain labels as strings and 
    properties as tuples.

    Edges are represented as directed links between nodes. They can contain relationships as strings
    and properties as tuples.

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
                self.name = None
            else:
                self.n_vertices = int (cast(int, args[0]))
                self.n_edges = int(cast(int, args[1]))
                self.weighted = int(cast(int, args[3]))
                oriname = cast(str, args[4])
                self.name = oriname.strip()
                self.directed = 1
        except Exception as err:
            raise RuntimeError(err)

        self.dtype = akint
        self.logger = getArkoudaLogger(name=__class__.__name__)

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
        # 0. Extract the column names of the dataframe.
        columns = node_properties.columns

        # 1. Convert the vertex_ids to internal vertex_ids.
        vertex_map = self.nodes()
        vertex_ids = node_properties[columns[0]]
        inds = ak.in1d(vertex_ids, vertex_map)
        node_properties = node_properties[inds]
        vertex_ids = node_properties[columns[0]]
        vertex_ids = ak.find(vertex_ids, vertex_map)

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
        rep_msg = generic_msg(cmd=cmd, args=args)

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
        columns = edge_properties.columns
        src_vertex_ids = edge_properties[columns[0]]
        dst_vertex_ids = edge_properties[columns[1]]

        # 1. Convert the source and destination vertex ids to the internal vertex_ids.
        vertex_map = self.nodes()
        src_vertex_ids = ak.find(src_vertex_ids, vertex_map)
        dst_vertex_ids = ak.find(dst_vertex_ids, vertex_map)

        # 2. Generate the internal edge indices.
        edges = self.edges()
        internal_edge_indices = ak.find([src_vertex_ids,dst_vertex_ids],[edges[0],edges[1]])

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
    







@typechecked
def graph_query(graph: Graph, component: str) -> pdarray:
    """
        This function returns the component array of given graph
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphQue"
    if component == "src":
        attr=1
    elif component =="dst":
        attr=2
    elif component =="start_i":
        attr=3
    elif component =="neighbour":
        attr=4
    elif component =="srcR":
        attr=5
    elif component =="dstR":
        attr=6
    elif component =="start_iR":
        attr=7
    elif component =="neighbourR":
        attr=8
    elif component =="astart_i":
        attr=-3
    elif component =="aneighbour":
        attr=-4
    elif component =="astart_iR":
        attr=-7
    elif component =="aneighbourR":
        attr=-8
    elif component =="v_weight":
        attr=-1
    elif component =="e_weight":
        attr=-2
    '''
    if int(graph.directed) > 0  :
        assert (attr<=4) 
    if attr < 0:
        assert graph.weighted > 0
'''
    args = {"GraphName":graph.name,"Component":component}
    repMsg = generic_msg(cmd=cmd, args=args)

    return create_pdarray(repMsg)

@typechecked
def graph_edgearray(src:pdarray, dst:pdarray, directed: int=0, \
                    RemapFlag:int=1, DegreeSortFlag:int=0, RCMFlag:int=0, \
                    WriteFlag:int=1, BuildAlignedArray:int=0) -> Graph:
    """
        This function is used for building a graph from two edge arrays 
        srcS : the source array of an edge
        dstS : the destination array of an edge
        directed: 0 means undirected graph and 1 means directed graph
        RemapFlag: if the vertex ID is larger than the total number of vertices, we will relabel the vertex ID
        DegreeSortFlag: we will let small vertex ID be the vertex whose degree is small
        RCMFlag: we will remap the vertex ID based on the RCM algorithm
        WriteFlag: we will output the final edge list src->dst array as a new input file.
        BuildAlignedArray: using the Edge-Vertex-Locale aligned mapping instead of the default distribution
        Returns
        -------
        Graph
            The Graph class to represent the data

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphArray"
    args ={"SRC":src,"DST": dst, "Directed":directed,  \
            "RemapFlag":RemapFlag, "DegreeSortFlag":DegreeSortFlag, \
            "RCMFlag":RCMFlag, "WriteFlag":WriteFlag,"AlignedFlag":BuildAlignedArray}
    # currently we will not handle the BuildAlignedArray flag except in the read procedure
    repMsg = generic_msg(cmd=cmd, args=args)
    return Graph(*(cast(str, repMsg).split('+')))


@typechecked
def graph_file_preprocessing(Ne: int, Nv: int, Ncol: int, directed: int, \
                    filename: str,skipline:int=0,\
                    RemapFlag:int=1, DegreeSortFlag:int=0, RCMFlag:int=0, \
                    WriteFlag:int=1, BuildAlignedArray:int=0) -> None:
    """
        This function is used for creating a preprocessed graph file (mapping vertices, 
                remove duplicated edges and self loop ) from a given file.
        Ne : the total number of edges of the graph
        Nv : the total number of vertices of the graph
        Ncol: how many column of the file. Ncol=2 means just edges (so no weight and weighted=0) 
              and Ncol=3 means there is weight for each edge (so weighted=1). 
        directed: 0 means undirected graph and 1 means directed graph
        filename: the file that has the edge list
        skipline: 0 means how many lines should be skiped
        RemapFlag: if the vertex ID is larger than the total number of vertices, we will relabel the vertex ID
        DegreeSortFlag: we will let small vertex ID be the vertex whose degree is small
        RCMFlag: we will remap the vertex ID based on the RCM algorithm
        WriteFlag: we will output the final edge list src->dst array as a new input file.
        BuildAlignedArray: using the Edge-Vertex-Locale aligned mapping instead of the default distribution
        Returns
        -------
        Graph
            The Graph class to represent the data

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphPreProcessing"
    args = {"NumOfEdges":Ne,"NumOfVertices":Nv,"NumOfColumns":Ncol,\
            "Directed":directed, "FileName":filename,"SkipLines":skipline, \
            "RemapFlag":RemapFlag, "DegreeSortFlag":DegreeSortFlag,\
            "RCMFlag":RCMFlag, "WriteFlag":WriteFlag,"AlignedFlag":BuildAlignedArray}
    repMsg = generic_msg(cmd=cmd, args=args)
    print(repMsg)
    return 




@typechecked
def graph_file_tonde(Ne: int, Nv: int, Ncol: int, directed: int, filename: str,skipline:int=0,\
                    RemapFlag:int=1, DegreeSortFlag:int=0, RCMFlag:int=0, WriteFlag:int=1) -> None:
    """
        This function is used for transferring a graph file to NDE format

- first line contains `N`, the number of nodes.
- the next `N` lines contain two numbers, `i` and `degree[i]`
- all the other lines contain two numbers, `a[i]` and `b[i]`, representing an
  edge from node `a[i]` to node `b[i]`.


        Ne : the total number of edges of the graph
        Nv : the total number of vertices of the graph
        Ncol: how many column of the file. Ncol=2 means just edges (so no weight and weighted=0) 
              and Ncol=3 means there is weight for each edge (so weighted=1). 
        directed: 0 means undirected graph and 1 means directed graph
        skipline: 0 means how many lines should be skiped
        filename: the file that has the edge list
        RemapFlag: if the vertex ID is larger than the total number of vertices, we will relabel the vertex ID
        DegreeSortFlag: we will let small vertex ID be the vertex whose degree is small
        RCMFlag: we will remap the vertex ID based on the RCM algorithm
        WriteFlag: we will output the final file to NDE format
        Returns
        -------
        Graph
            The Graph class to represent the data

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphToNDE"
    args = {"NumOfEdges":Ne, "NumOfVertices":Nv, "NumOfColumns":Ncol,\
             "Directed":directed, "FileName":filename,"SkipLines":skipline, \
            "RemapFlag":RemapFlag, "DegreeSortFlag":DegreeSortFlag,\
            "RCMFlag":RCMFlag, "WriteFlag":WriteFlag}
    repMsg = generic_msg(cmd=cmd, args=args)
    return 




@typechecked
def graph_file_read(Ne: int, Nv: int, Ncol: int, directed: int, filename: str,\
                    RemapFlag:int=1, DegreeSortFlag:int=0, RCMFlag:int=0, WriteFlag:int=0, BuildAlignedArray:int=0) -> Graph:
    """
        This function is used for creating a graph from a file.
        The file should like this
          1   5
          13  9
          7   6 
        This file means the edges are <1,5>,<13,9>,<7,6>. If additional column is added, it is the weight
        of each edge.
        Ne : the total number of edges of the graph
        Nv : the total number of vertices of the graph
        Ncol: how many column of the file. Ncol=2 means just edges (so no weight and weighted=0) 
              and Ncol=3 means there is weight for each edge (so weighted=1). 
        directed: 0 means undirected graph and 1 means directed graph
        filename: the file that has the edge list
        RemapFlag: if the vertex ID is larger than the total number of vertices, we will relabel the vertex ID
        DegreeSortFlag: we will let small vertex ID be the vertex whose degree is small
        RCMFlag: we will remap the vertex ID based on the RCM algorithm
        WriteFlag: we will output the final edge list src->dst array as a new input file.
        BuildAlignedArray: using the Edge-Vertex-Locale aligned mapping instead of the default distribution
        Returns
        -------
        Graph
            The Graph class to represent the data

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphFile"
    args = {"NumOfEdges":Ne, "NumOfVertices":Nv, "NumOfColumns":Ncol,\
             "Directed":directed, "FileName":filename, \
            "RemapFlag":RemapFlag, "DegreeSortFlag":DegreeSortFlag,\
            "RCMFlag":RCMFlag, "WriteFlag":WriteFlag,"AlignedFlag":BuildAlignedArray}
    repMsg = generic_msg(cmd=cmd, args=args)

    return Graph(*(cast(str, repMsg).split('+')))


@typechecked
def graph_file_read_mtx(Ne: int, Nv: int, Ncol: int, directed: int, filename: str,\
                        RemapFlag:int=1, DegreeSortFlag:int=0, RCMFlag:int=0, WriteFlag:int=0, BuildAlignedArray:int=0) -> Graph:
    """
        This function is used for creating a graph from a mtx graph file.
        compared with the graph_file_read function, it will skip the mtx head part
        Ne : the total number of edges of the graph
        Nv : the total number of vertices of the graph
        Ncol: how many column of the file. Ncol=2 means just edges (so no weight and weighted=0) 
              and Ncol=3 means there is weight for each edge (so weighted=1). 
        directed: 0 means undirected graph and 1 means directed graph
        filename: the file that has the edge list
        RemapFlag: if the vertex ID is larger than the total number of vertices, we will relabel the vertex ID
        DegreeSortFlag: we will let small vertex ID be the vertex whose degree is small
        RCMFlag: we will remap the vertex ID based on the RCM algorithm
        WriteFlag: we will output the final edge list src->dst array as a new input file.
        BuildAlignedArray: using the Edge-Vertex-Locale aligned mapping instead of the default distribution
        Returns
        -------
        Graph
            The Graph class to represent the data

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphFileMtx"
    args = {"NumOfEdges":Ne, "NumOfVertices":Nv, "NumOfColumns":Ncol,\
             "Directed":directed, "FileName":filename, \
            "RemapFlag":RemapFlag, "DegreeSortFlag":DegreeSortFlag,\
            "RCMFlag":RCMFlag, "WriteFlag":WriteFlag,"AlignedFlag":BuildAlignedArray}
    repMsg = generic_msg(cmd=cmd, args=args)

    return Graph(*(cast(str, repMsg).split('+')))


@typechecked
def rmat_gen(lgNv: int, Ne_per_v: int, p: float=0.4, directed: int=0, weighted: int=0,RCMFlag:int=0) -> Graph:
    """
        This function is for creating a graph using rmat graph generator
        Returns
        -------
        Graph
            The Graph class to represent the data

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedRMAT"
    RCMFlag = 1
    args = {"LogNumOfVertices":lgNv, "NumOfEdgesPerV":Ne_per_v,"SP":p,\
             "Directed":directed,"Weighted": weighted,\
            "RCMFlag":RCMFlag}
    repMsg = generic_msg(cmd=cmd, args=args)

    return Graph(*(cast(str, repMsg).split('+')))


@typechecked
def graph_bfs(graph: Graph, root: int=0, rcm_flag:int=0) -> pdarray:
    """
        This function is generating the breadth-first search vertices sequences in given graph
        starting from the given root vertex
        Returns
        -------
        pdarray
            The bfs vertices results

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphBFS"
    DefaultRatio = -0.9
    args = {"RCMFlag":rcm_flag,"NumOfVertices":graph.n_vertices,"NumOfEdges":graph.n_edges,\
             "Directed":graph.directed,"Weighted": graph.weighted,\
             "GraphName":graph.name,"Root":root,"Ratio":DefaultRatio}

    repMsg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(repMsg)

@typechecked
def graph_cc(graph: Graph) -> pdarray:
    """
        This function is generating the connected components of a given graph.
        Returns
        -------
        pdarray
            The component each vertex belongs to.

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphCC"
    args = {"NumOfVertices":graph.n_vertices,"NumOfEdges":graph.n_edges,\
             "Directed":graph.directed,"Weighted":graph.weighted,\
             "GraphName":graph.name}
    repMsg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(repMsg)



@typechecked
def graph_diameter(graph: Graph) -> pdarray:
    """
        This function calculates the diameter of different connected components of a given graph.
        Returns
        -------
        pdarray
            The component each vertex belongs to.

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
    cmd = "segmentedGraphDiameter"
    args = {"NumOfVertices":graph.n_vertices,"NumOfEdges":graph.n_edges,\
             "Directed":graph.directed,"Weighted":graph.weighted,\
             "GraphName":graph.name}
    repMsg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(repMsg)



@typechecked
def stream_file_read(Ne:int, Nv:int,Ncol:int,directed:int, filename: str,\
                     factor:int)  -> Graph:
        """
        This function is used for creating a graph from a file.
        The file should like this
          1   5
          13  9
          4   8
          7   6
        This file means the edges are <1,5>,<13,9>,<4,8>,<7,6>. If additional column is added, it is the weight
        of each edge.
        Ne : the total number of edges of the graph
        Nv : the total number of vertices of the graph
        Ncol: how many column of the file. Ncol=2 means just edges (so no weight and weighted=0) 
              and Ncol=3 means there is weight for each edge (so weighted=1). 
        directed: 0 means undirected graph and 1 means directed graph
        Returns
        -------
        Graph
            The Graph class to represent the data

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
        cmd = "segmentedStreamFile"
        args = { "NumOfEdges":Ne, "NumOfVertices":Nv, \
                 "NumOfColumns":Ncol, "Directed":directed,\
                 "FileName":filename,"Factor":factor}
        repMsg = generic_msg(cmd=cmd,args=args)

        return Graph(*(cast(str,repMsg).split('+')))


@typechecked
def graph_triangle (graph: Graph, vertexArray:pdarray ) -> pdarray:
        """
        This function will return the number of triangles in a static graph if the vertexArray is [-1], 
        otherwise, it will return the number of triangles of containing the given vertex. If the input vertexArray is 
        [0,10,40] and return array is [3,20,5], it means that there are 3 triangles contain vertex 0; 20 triangles 
        contains vertex 10; 5 triangles contain vertex 40
        Returns
        -------
        pdarray
            The total number of triangles.

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
        cmd="segmentedGraphTri"
        args = {"NumOfVertices":graph.n_vertices,"NumOfEdges":graph.n_edges,\
             "Directed":graph.directed,"Weighted": graph.weighted,\
             "GraphName":graph.name,"VertexArray":vertexArray}

        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)
        
@typechecked
def graph_ktruss(graph: Graph,kTrussValue:int) -> pdarray:
        """
        This function will return the number of triangles in a static graph for each edge
        Returns
        -------
        pdarray
            The total number of triangles incident to each edge.

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
        cmd="segmentedTruss"
        args = {"KValue":kTrussValue,"NumOfVertices":graph.n_vertices,"NumOfEdges":graph.n_edges,\
             "Directed":graph.directed,"Weighted": graph.weighted,\
             "GraphName":graph.name}
        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)



@typechecked
def stream_tri_cnt(Ne:int, Nv:int,Ncol:int,directed:int, filename: str,\
                     factor:int)  -> pdarray:
        cmd = "segmentedStreamTri"
        args = { "NumOfEdges":graph.n_edges, "NumOfVertices":graph.n_vertices,\
                 "NumOfColumns":Ncol, "Directed":directed, "FileName": filename,\
                 "Factor":factor}
        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)

@typechecked
def streamPL_tri_cnt(Ne:int, Nv:int,Ncol:int,directed:int, filename: str,\
                     factor:int, case:int)  -> pdarray:
        """
        This function is used for creating a graph from a file.
        The file should like this
          1   5
          13  9
          4   8
          7   6
        This file means the edges are <1,5>,<13,9>,<4,8>,<7,6>. If additional column is added, it is the weight
        of each edge.
        Ne : the total number of edges of the graph
        Nv : the total number of vertices of the graph
        Ncol: how many column of the file. Ncol=2 means just edges (so no weight and weighted=0) 
              and Ncol=3 means there is weight for each edge (so weighted=1). 
        factor: the sampling graph will be 1/factor of the original one
        case: 0 calculate the average, 1: using power law regression paramter 2: using normal regression parameter 
        Returns
        -------
        Graph
            The Graph class to represent the data

        See Also
        --------

        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
        cmd = "segmentedPLStreamTri"
        args = { "NumOfEdges":Ne, "NumOfVertices":Nv,\
                 "NumOfColumns":Ncol, "Directed":directed, "FileName": filename,\
                 "Factor":factor,"Case":case}
        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)


@typechecked
def graph_tri_ctr (graph: Graph) -> pdarray:
        """
        This function will return the triangle centrality of each vertex in a static graph.
        Returns
        -------
        pdarray
            The triangle centrality value of each vertex.
        See Also
        --------
        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
        cmd="segmentedGraphTriCtr"

        args = {"NumOfVertices":graph.n_vertices,"NumOfEdges":graph.n_edges,\
             "Directed":graph.directed,"Weighted": graph.weighted,\
             "GraphName":graph.name}
        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)


@typechecked
def graph_jaccard_coefficient(graph: Graph) -> pdarray:
        """
        This function will return the jaccard coefficient of each vertex in a static graph.
        Returns
        -------
        pdarray
            The jaccard coefficient value of each vertex.
        See Also
        --------
        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
        cmd="segmentedGraphJaccard"
        args = {"NumOfVertices":graph.n_vertices,"NumOfEdges":graph.n_edges,\
             "Directed":graph.directed,"Weighted": graph.weighted,\
             "GraphName":graph.name}

        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)


@typechecked
def graph_jaccard_hash(graph: Graph) -> pdarray:
        """
        This function will return the jaccard coefficient of each vertex in a static graph.
        Returns
        -------
        pdarray
            The jaccard coefficient value of each vertex.
        See Also
        --------
        Notes
        -----
        
        Raises
        ------  
        RuntimeError
        """
        cmd="segmentedGraphJaccardHash"
        args = {"NumOfVertices":graph.n_vertices,"NumOfEdges":graph.n_edges,\
             "Directed":graph.directed,"Weighted": graph.weighted,\
             "GraphName":graph.name}

        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)



@typechecked
def graph_add_property(graph:Graph, propertyname:str,array:pdarray) -> Graph:
        cmd="segmentedGraphProperty"
        args = { "GraphName":graph.name, "Property":propertyname, "Data":array }
        repMsg = generic_msg(cmd=cmd,args=args)
        return Graph(*(cast(str, repMsg).split('+')))

