"""Contains all current Arachne functionality. Includes different graph classes, building methods, 
and graph algorithmic kernels. Please look at each class and function docstrings for more 
information.
"""
from __future__ import annotations
from typing import cast, Tuple, Union
from typeguard import typechecked
import time
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray
from arkouda.logger import getArkoudaLogger
from arkouda.dtypes import int64 as akint

__all__ = ["Graph",
           "DiGraph",
           "PropGraph",
           "bfs_layers",
           "subgraph_isomorphism",
           "triangles",
           "k_truss",
           "triangle_centrality",
           "connected_components",
           "read_matrix_market_file"
           ]

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
        labels
            `ak.DataFrame({"vertex_ids" : vertices, "vertex_labels" : labels})`

        Returns
        -------
        None
        """
        cmd = "addNodeLabels"

        ### Preprocessing steps for faster back-end array population.
        # 0. Extract the vertex ids and vertex labels from the dataframe.
        vertex_ids = labels["vertex_ids"]
        vertex_labels = labels["vertex_labels"]

        # 1. Broadcast string label names to int values and extract the label str to int id map.
        start = time.time()
        gb_labels = ak.GroupBy(vertex_labels)
        new_label_ids = ak.arange(gb_labels.unique_keys.size)
        vertex_labels = gb_labels.broadcast(new_label_ids)
        label_mapper = gb_labels.unique_keys
        end = time.time()
        label_id_time = round(end-start,2)

        # 2. Convert the vertex_ids to internal vertex_ids.
        start = time.time()
        vertex_map = self.nodes()
        inds = ak.in1d(vertex_ids, vertex_map)
        vertex_ids = vertex_ids[inds]
        vertex_labels = vertex_labels[inds]
        vertex_ids = ak.find(vertex_ids, vertex_map)
        end = time.time()
        internal_id_time = round(end-start,2)

        # 3. GroupBy of the vertex ids and labels.
        start = time.time()
        gb_vertex_ids_and_labels = ak.GroupBy([vertex_ids,vertex_labels])
        vertex_ids = gb_vertex_ids_and_labels.unique_keys[0]
        vertex_labels = gb_vertex_ids_and_labels.unique_keys[1]
        end = time.time()
        dedup_and_sort_time = round(end-start,2)

        arrays = vertex_ids.name + " " + vertex_labels.name + " " + label_mapper.name
        start = time.time()
        args = { "GraphName" : self.name,
                 "Arrays" : arrays,
               }
        rep_msg = generic_msg(cmd=cmd, args=args)
        end = time.time()
        add_into_data_structure_time = round(end-start,2)

        return (label_id_time, internal_id_time, dedup_and_sort_time, add_into_data_structure_time)

    def add_edge_relationships(self, relationships:ak.DataFrame) -> None:
        """Populates the graph object with edge relationships from a dataframe. Passed dataframe 
        should follow the same format specified in the Parameters section below.
        
        Parameters
        ----------
        relationships
            `ak.DataFrame({"src" : src, "dst" : dst, "edge_relationships" : edge_relationships})`

        Returns
        -------
        None
        """
        cmd = "addEdgeRelationships"

        ### Preprocessing steps for faster back-end array population. 
        # 0. Extract the source and destination vertex ids and the relationships from the dataframe.
        src_vertex_ids = relationships["src"]
        dst_vertex_ids = relationships["dst"]
        edge_relationships = relationships["edge_relationships"]

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

    def query_labels(   self,
                        labels_to_find:pdarray,
                        op:str = "and" ) -> pdarray:
        """Given pdarrays specifiying a subset of node labels, this function returns to the user a 
        pdarray with the nodes that contain any of the labels. The operator specifies the operation
        to be conducted at the back-end. If the vertex should contain all of the labels specified
        in `labels_to_find` then the operaator to use should be "and" otherwise use "or".

        Parameters
        ----------
        labels_to_find : pdarray
            A pdarray with node labels whose nodes are to be returned.
        op : str
            Operator to apply to the search, either "and" or "or". 
        
        Returns
        -------
        pdarray : int64
            Vertex names that contain the specified nodes.
        """
        cmd = "queryLabels"
        labels_to_find = ak.find(labels_to_find, self.get_node_labels())
        
        args = {  "GraphName" : self.name,
                  "LabelsToFindName" : labels_to_find.name,
                  "Op" : op }
        
        rep_msg = generic_msg(cmd=cmd, args=args)
        vertices_bool = create_pdarray(rep_msg)
        final_vertices = self.nodes()[vertices_bool]

        return final_vertices

    def query_relationships(    self,
                                relationships_to_find:pdarray,
                                op:str = "and" ) -> pdarray:
        """Given a pdarray specifiying a subset of edge relationships, this function returns to the 
        user a pdarray with the edges that contain any of the relationships. The operator specifies
        the operation to be conducted at the back-end. If the vertex should contain all of the
        relationships specified in `relationships_to_find` then the operayor should be "and"
        otherwise use "or".

        Parameters
        ----------
        relationships_to_find : pdarray
            A pdarray with edge relationships whose edges are to be returned.
        op : str
            Operator to apply to the search, either "and" or "or". 
        
        Returns
        -------
        (pdarray,pdarray) : Tuple(int64, int64)
            Source and destination vertex pairs that contain the specified edges.
        """
        cmd = "queryRelationships"
        relationships_to_find_to_find = ak.find(relationships_to_find,self.get_edge_relationships())

        args = {  "GraphName" : self.name,
                  "RelationshipsToFindName" : relationships_to_find_to_find.name,
                  "Op" : op }

        rep_msg = generic_msg(cmd=cmd, args=args)

        edges_bool = create_pdarray(rep_msg)
        edges, nodes = self.edges(), self.nodes()
        src, dst = edges[0], edges[1]
        src, dst = nodes[src], nodes[dst]
        final_edges = (src[edges_bool], dst[edges_bool])

        return final_edges

@typechecked
def read_matrix_market_file(filepath: str, directed = False) -> Graph | DiGraph:
    """Reads a matrix market file and returns the graph specified by the matrix indices. NOTE: the
    absolute path to the file must be given.

    Returns
    -------
    Graph | DiGraph
        The graph specified by the matrix market file.

    See Also
    --------

    Notes
    -----

    Raises
    ------
    """
    cmd = "readMatrixMarketFile"
    args = { "Path": filepath,
             "Directed": directed }
    rep_msg = generic_msg(cmd=cmd, args=args)
    returned_vals = (cast(str, rep_msg).split('+'))

    src = create_pdarray(returned_vals[0])
    dst = create_pdarray(returned_vals[1])

    wgt = ak.array([-1])
    weighted = False
    if returned_vals[2].strip() != "nil":
        wgt = create_pdarray(returned_vals[2])
        weighted = True

    if not directed:
        graph = Graph()
        if not weighted:
            graph.add_edges_from(src, dst)
        else:
            graph.add_edges_from(src, dst, wgt)
        return graph
    else:
        di_graph = DiGraph()
        if not weighted:
            di_graph.add_edges_from(src, dst)
        else:
            di_graph.add_edges_from(src, dst, wgt)
        return di_graph

@typechecked
def bfs_layers(graph: Graph, source: int) -> pdarray:
    """ This function generates the breadth-first search sequence of the vertices in a given graph
    starting from the given source vertex.
        
    Returns
    -------
    pdarray
        The depth of each vertex in relation to the source vertex. NOTE: The indices of the returned
        array correspond to the internal Chapel server vertex values. To properly index, the user
        must perform a find operation on "graph.nodes()" adn then use the returned pdarray to index
        into depths.
    
    See Also
    --------
    
    Notes
    -----
    
    Raises
    ------  
    RuntimeError
    """
    cmd = "segmentedGraphBFS"
    args = { "GraphName":graph.name,
             "Source":source }

    repMsg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(repMsg)

@typechecked
def triangles(graph: Graph, vertexArray: pdarray = None) -> pdarray:
    """
    This function will return the number of triangles in a static graph if the vertexArray is [-1], 
    otherwise, it will return the number of triangles containing the given vertex. If the input vertexArray is 
    [0,10,40] and return array is [3,20,5], it means that there are 3 triangles contain vertex 0; 20 triangles 
    contains vertex 10; 5 triangles contain vertex 40.
    
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

    if vertexArray is None:
        vertexArray = ak.array([-1])

    args = { "NumOfVertices":graph.n_vertices,
             "NumOfEdges":graph.n_edges,
             "Directed":graph.directed,
             "Weighted": graph.weighted,
             "GraphName":graph.name,
             "VertexArray":vertexArray}

    repMsg = generic_msg(cmd=cmd,args=args)
    return create_pdarray(repMsg)

@typechecked
def subgraph_isomorphism(G: PropGraph, H:PropGraph, type: str = "ullmann") -> pdarray:
    """
    Given a graph G and a subgraph H, perform a search in G matching all possible subgraphs that
    are isomorphic to H. Current contains implementations for Ullmann and VF2. 

    Parameters
    ----------
    G : PropGraph | DiGraph
        Main graph that will be searched into. 
    H : PropGraph | DiGraph
        Subgraph (pattern) that will  be searched for. 
    type : str
        Algorithmic variation to run. 

    Returns
    -------
    pdarray
        Graph IDs of matching subgraphs from G. 
    
    See Also
    --------
    
    Notes
    -----
    
    Raises
    ------  
    RuntimeError
    """
    ### Preprocessing steps for subgraph isomorphism.
    # 1. Sort vertices by degree in non-ascending order.
    subgraph_vertex_map = H.nodes()
    subgraph_internal_vertices = ak.arange(0,len(subgraph_vertex_map))
    subgraph_in_degree = H.in_degree()
    subgraph_out_degree = H.out_degree()
    subgraph_degree = subgraph_in_degree + subgraph_out_degree # TODO: fix to inspect in- and out- degrees separately.
    perm = ak.argsort(subgraph_degree)
    subgraph_internal_vertices = subgraph_internal_vertices[perm]

    # 2. Generate the cumulative degree for each vertex in graph.
    graph_in_degree = G.in_degree()
    graph_out_degree = G.out_degree()
    graph_degree = graph_in_degree + graph_out_degree

    cmd = "subgraphIsomorphism"
    args = { "MainGraphName":G.name,
             "SubGraphName":H.name,
             "GraphDegreeName":graph_degree.name,
             "SubGraphDegreeName":subgraph_degree.name,
             "SubGraphInternalVerticesSortedName":subgraph_internal_vertices.name,
             "Type":type }

    repMsg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(repMsg)

@typechecked
def triangle_centrality(graph: Graph) -> pdarray:
    """ This function returns the triangle centrality of each vertex in a given graph.
        
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
    args = { "NumOfVertices":graph.n_vertices,
                "NumOfEdges":graph.n_edges,
                "Directed":graph.directed,
                "Weighted": graph.weighted,
                "GraphName":graph.name}
    
    repMsg = generic_msg(cmd=cmd,args=args)
    return create_pdarray(repMsg)

@typechecked
def connected_components(graph: Graph) -> pdarray:
    """ This function generates the connected components of a given graph.
    
    Returns
    -------
    pdarray
        The label of the component each vertex belongs to.
    
    See Also
    --------
    
    Notes
    -----
    
    Raises
    ------  
    RuntimeError
    """
    cmd = "segmentedGraphCC"
    args = { "NumOfVertices":graph.n_vertices,
             "NumOfEdges":graph.n_edges,
             "Directed":graph.directed,
             "Weighted":graph.weighted,
             "GraphName":graph.name}
    
    repMsg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(repMsg)

@typechecked
def k_truss(graph: Graph, kTrussValue:int) -> pdarray:
    """
    This function returns the number of triangles in a static graph for each edge that satisfies the
    k requirement.
    
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
    args = { "KValue":kTrussValue,
             "NumOfVertices":graph.n_vertices,
             "NumOfEdges":graph.n_edges,
             "Directed":graph.directed,
             "Weighted": graph.weighted,
            "GraphName":graph.name}

    repMsg = generic_msg(cmd=cmd,args=args)
    return create_pdarray(repMsg)
