"""Contains all current Arachne functionality. Includes different graph classes, building methods, 
and graph algorithmic kernels. Please look at each class and function docstrings for more 
information.
"""
from __future__ import annotations
from typing import cast, Tuple, Union
from typeguard import typechecked
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray
from arkouda.logger import getArkoudaLogger
from arkouda.dtypes import int64 as akint

__all__ = ["Graph",
           "DiGraph",
           "PropGraph",
           "bfs_layers",
           "triangles",
           "k_truss",
           "triangle_centrality",
           "connected_components",
           "subgraph_view"
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
        """Returns the degree view for the whole graph as a tuple of pdarray objects. The format is
        as follows:

        (out_degree: pdarray, in_degree: pdarray)

        where, for an undirected graph, the in_degree is composed of all 0s.

        Returns
        -------
        (out_degree: pdarray, in_degree: pdarray): tuple.
            The array containing the number of degrees for each node.
        """
        cmd = "degree"
        args = {"GraphName" : self.name}
        repMsg = generic_msg(cmd=cmd, args=args)
        returned_vals = (cast(str, repMsg).split('+'))

        return create_pdarray(returned_vals[0]), create_pdarray(returned_vals[1])

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
        self_loops = ak.value_counts(self_loops)[1][1] # This is our x.
        num_edges_after_dedup = src.size
        num_removed_edges = num_original_edges - num_edges_after_dedup # This is our z.
        num_dupped_edges = (num_removed_edges - self_loops) / 2 # This is solving for.
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
        except Exception as e:
            raise RuntimeError(e)

        self.dtype = akint
        self.logger = getArkoudaLogger(name=__class__.__name__)
    
    def add_node_labels(self, labels:ak.DataFrame) -> None:
        """Populates the graph object with labels from a dataframe. Passed dataframe should follow
        this same format for key names: 
        
        labels = ak.DataFrame({"nodeIDs" : nodes, "nodeLabels" : labels})

        Returns
        -------
        None
        """
        cmd = "addNodeLabels"
        arrays = labels["nodeIDs"].name + " " + labels["nodeLabels"].name
        args = {  "GraphName" : self.name,
                  "Arrays" : arrays }
        repMsg = generic_msg(cmd=cmd, args=args)

    def add_edge_relationships(self, relations:ak.DataFrame) -> None:
        """Populates the graph object with edge relationships from a dataframe. Passed dataframe should 
        follow this same format for key-value pairs: 
        
        relationships = ak.DataFrame({"src" : src, "dst" : dst, "edgeRelationships" : edgeRelationships})

        where X is an arbitrary number of property columns. 

        Returns
        -------
        None
        """
        cmd = "addEdgeRelationships"
        arrays = relations["src"].name + " " + relations["dst"].name + " " + relations["edgeRelationships"].name + " "
        args = {  "GraphName" : self.name,
                  "Arrays" : arrays }
        repMsg = generic_msg(cmd=cmd, args=args)

    def add_node_properties(self, properties:ak.DataFrame) -> None:
        """Populates the graph object with node properties from a dataframe. Passed dataframe should follow
        this same format for key names below:
        
        node_properties = ak.DataFrame({"nodeIDs" : nodes, "prop1" : prop1, ... , "propN" L propN})

        Returns
        -------
        None
        """
        cmd = "addNodeProperties"
        arrays = properties["nodeIDs"].name + " " 
        columns = "nodeIDs" + " "

        for column in properties.columns:
            if column != "nodeIDs":
                arrays += properties[column].name + " "
                columns += column + " "

        args = {  "GraphName" : self.name,
                  "Arrays" : arrays,
                  "Columns" : columns }
        repMsg = generic_msg(cmd=cmd, args=args)

    def add_edge_properties(self, properties:ak.DataFrame) -> None:
        """Populates the graph object with edge properties from a dataframe. Passed dataframe should follow
        this same format for key names below:
        
        edge_properties = ak.DataFrame({"src" : src, "dst" : dst, "prop1" : prop1, ... , "propM" : propM})

        Returns
        -------
        None
        """
        cmd = "addEdgeProperties"
        arrays = properties["src"].name + " " + properties["dst"].name + " "
        columns = "src" + " " + "dst" + " "

        for column in properties.columns:
            if column != "src" and column != "dst":
                arrays += properties[column].name + " "
                columns += column + " "

        args = {  "GraphName" : self.name,
                  "Arrays" : arrays,
                  "Columns" : columns }
        repMsg = generic_msg(cmd=cmd, args=args)

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
def subgraph_view(graph: Graph,
                  return_as: Union[Graph, DiGraph, PropGraph] = Graph,
                  filter_labels: pdarray = None,
                  filter_relationships: ak.DataFrame = None,
                  filter_node_properties: pdarray = None,
                  filter_edge_properties: ak.DataFrame = None) -> Graph:
    """ This function generates a subgraph view (a filtered graph) of a passed Graph. The returned
    graph is a simple graph where no labels, relationships, or properties are maintained.

    Format of filter_labels and filter_node_properties:
    [node_1, node_2, ..., node_n]:pdarray
    where the nodes listed are computed by Arkouda filtering and are to be kept in the generated 
    subgraph.

    Format of filter_relationships and filter_edge_properties:
    {
    "src":[node_1, node_2, ..., node_m]
    "dst":[node_1, node_2, ..., node_m]
    }
    where the nodes listed ar the src and dst of the edges computed by Arkouda filtering and are to
    be kept in the generated subgraph.
    

    Returns
    -------
    Graph
        The induced simple graph from filtering labels, edges, and/or properties.

    See Also
    --------

    Notes
    -----

    Raises
    ------
    RuntimeError
    """
    cmd = "subgraphView"
    args = {"GraphName" : graph.name}

    if filter_labels is not None:
        args["FilterLabelsExists"] = "true"
        args["FilterLabelsName"] = filter_labels.name
    
    if filter_relationships is not None:
        args["FilterRelationshipsExists"] = "true"
        args["FilterRelationshipsSrcName"] = filter_relationships["src"].name
        args["FilterRelationshipsDstName"] = filter_relationships["dst"].name
    
    if filter_node_properties is not None:
        args["FilterNodePropertiesExists"] = "true"
        args["FilterNodePropertiesName"] = filter_node_properties.name
    
    if filter_edge_properties is not None:
        args["FilterEdgePropertiesExists"] = "true"
        args["FilterEdgePropertiesSrcName"] = filter_edge_properties["src"].name
        args["FilterEdgePropertiesDstName"] = filter_edge_properties["dst"].name

    repMsg = generic_msg(cmd=cmd, args=args)
    returned_vals = (cast(str, repMsg).split('+'))
        
    src = create_pdarray(returned_vals[0])
    dst = create_pdarray(returned_vals[1])
    subgraph = return_as
    subgraph.add_edges_from(src, dst)
    return subgraph

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
