"""Contains all current Arachne functionality. Includes building methods and algorithmic kernels.
"""
from __future__ import annotations
from typing import cast, Tuple, Union
from typeguard import typechecked
import arachne as ar
from arachne.graphclass import Graph
from arachne.digraphclass import DiGraph
from arachne.propgraphclass import PropGraph
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray

__all__ = [ "read_matrix_market_file",
            "bfs_layers",
            "subgraph_isomorphism",
            "triangles",
            "squares",
            "k_truss",
            "max_truss",
            "truss_decomposition",
            "triangle_centrality",
            "connected_components",
            "diameter",
            "well_connected_components"
           ]

@typechecked
def read_matrix_market_file(filepath: str,
                            directed = False,
                            only_edges = False) -> Union[Graph,DiGraph,Tuple]:
    """Reads a matrix market file and returns the graph specified by the matrix indices. NOTE: the
    absolute path to the file must be given.

    Parameters
    ----------
    filepath : str
        The graph whose breadth-first search layers we want.
    directed : int
        Starting vertex for breadth-first search.
    only_edges : bool

    Returns
    -------
    Graph | DiGraph
        The graph specified by the matrix market file.
    """
    cmd = "readMatrixMarketFile"
    args = { "Path": filepath,
             "Directed": directed }
    rep_msg = generic_msg(cmd=cmd, args=args)
    returned_vals = (cast(str, rep_msg).split('+'))

    src = create_pdarray(returned_vals[0])
    dst = create_pdarray(returned_vals[1])

    if only_edges:
        return (src,dst)

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
def bfs_layers(graph: Union[ar.Graph,ar.DiGraph], source: int) -> pdarray:
    """ This function generates the breadth-first search sequence of the vertices in a given graph
    starting from the given source vertex.

    Parameters
    ----------
    graph : ar.Graph | ar.DiGraph
        The graph whose breadth-first search layers we want.
    source : int
        Starting vertex for breadth-first search.
        
    Returns
    -------
    pdarray
        The depth of each vertex in relation to the source vertex. NOTE: The indices of the returned
        array correspond to the internal Chapel server vertex values. To properly index, the user
        must perform a find operation on "graph.nodes()" adn then use the returned pdarray to index
        into depths.
    """
    cmd = "segmentedGraphBFS"
    args = { "GraphName":graph.name,
             "Source":source }

    repMsg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(repMsg)

@typechecked
def triangles(graph: ar.Graph, vertices: pdarray = None) -> Union[int,pdarray]:
    """
    Returns the number of triangles in a graph. If `vertices` exists and is nonempty, it returns the
    number of triangles that each vertex in `vertices` takes a part of. For example, if the input
    `vertices` contains `[0, 10, 40]` and it returns `[3, 20, 5]` then it means that 3 triangles
    contain vertex 0, 20 contain vertex 10, and 5 contain vertex 40.

    Note: Keeps in line with NetworkX triangles function where the returned value has to be divided
    3.

    Parameters
    ----------
    graph : Graph
        The graph whose triangles we want to find.
    vertices : pdarray
        Optional, if we only want to find triangles on specific vertices.
    
    Returns
    -------
    pdarray
        The total number of triangles.
    
    See Also
    --------
    squares, triangle_centrality, k-truss
    
    Notes
    -----
    
    Raises
    ------  
    RuntimeError
    """
    cmd = "segmentedGraphTri"

    if vertices is not None:
        vertices = ak.find(vertices, graph.nodes())
        not_found = vertices == -1
        vertices = vertices[~not_found]
    else:
        vertices = ak.array([-1])

    args = { "GraphName":graph.name,
             "VerticesName":vertices.name}

    rep_msg = generic_msg(cmd=cmd,args=args)
    if rep_msg.find("created") == -1:
        return int(rep_msg)
    return create_pdarray(rep_msg)

@typechecked
def squares(graph: Graph) -> int:
    """
    This function will return the number of squares in an undirected graph.

    Parameters
    ----------
    graph : Graph
        An undirected graph whose number of squares are to be returned
    
    Returns
    -------
    int
        The total number of squares
    
    See Also
    --------
    triangles
    
    Raises
    ------  
    RuntimeError
    """
    degree = graph.degree()
    cmd = "segmentedGraphSquares"
    args = { "GraphName" : graph.name,
             "DegreeName" : degree.name }
    rep_msg = generic_msg(cmd=cmd,args=args)
    return int(rep_msg)

@typechecked
def triangle_centrality(graph: ar.Graph) -> pdarray:
    """
    Given a graph, returns the triangle centrality for each node of the graph. The triangle 
    centrality of a node is given by the number of triangles that surround a particular node. It is
    based off the paper by Paul Burkardt (https://arxiv.org/abs/2105.00110). 

    Parameters
    ----------
    G : ar.Graph
        Main undirected graph that will be searched into.

    Returns
    -------
    pdarray
        Array that is the same size of the number of vertices where each element is the triangle 
        centrality measure.
    """
    cmd = "TriangleCentrality"
    args = {"GraphName" : graph.name}

    rep_msg = generic_msg(cmd=cmd,args=args)
    return create_pdarray(rep_msg)

@typechecked
def k_truss(graph: Graph, k_truss_value:int) -> pdarray:
    """
    This function returns an array of edges that make up the k requirement. NOTE: If the value
    contains -1 this means that that edge IS a k-truss edge.
    
    Returns
    -------
    pdarray
        The total number of triangles incident to each edge.
    
    See Also
    --------
    max_truss, truss_decomposition
    """
    cmd = "segmentedTruss"

    if not graph.has_reversed_arrays():
        edges = graph.edges()
        graph._generate_reversed_di(edges[0], edges[1])

    args = { "KValue":k_truss_value,
             "NumOfVertices":graph.n_vertices,
             "NumOfEdges":graph.n_edges,
             "Directed":graph.directed,
             "Weighted": graph.weighted,
             "GraphName":graph.name }

    rep_msg = generic_msg(cmd=cmd,args=args)
    return create_pdarray(rep_msg)

@typechecked
def max_truss(graph: Graph) -> int:
    """
    This function returns the maximum k for k-truss.
    
    Returns
    -------
    pdarray
        The total number of triangles incident to each edge.
    
    See Also
    --------
    k_truss, truss_decomposition
    """
    cmd = "segmentedTruss"

    if not graph.has_reversed_arrays():
        edges = graph.edges()
        graph._generate_reversed_di(edges[0], edges[1])

    args = { "KValue":-1,
             "NumOfVertices":graph.n_vertices,
             "NumOfEdges":graph.n_edges,
             "Directed":graph.directed,
             "Weighted": graph.weighted,
             "GraphName":graph.name }

    rep_msg = generic_msg(cmd=cmd,args=args)
    return int(rep_msg)

@typechecked
def truss_decomposition(graph: Graph) -> pdarray:
    """
    This function returns the maximum k that each edge belongs to.
    
    Returns
    -------
    pdarray
        The total number of triangles incident to each edge.
    
    See Also
    --------
    k_truss, max_truss
    """
    cmd = "segmentedTruss"

    if not graph.has_reversed_arrays():
        edges = graph.edges()
        graph._generate_reversed_di(edges[0], edges[1])

    args = { "KValue":-2,
             "NumOfVertices":graph.n_vertices,
             "NumOfEdges":graph.n_edges,
             "Directed":graph.directed,
             "Weighted": graph.weighted,
             "GraphName":graph.name }

    rep_msg = generic_msg(cmd=cmd,args=args)
    return create_pdarray(rep_msg)

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
    args = { "GraphName":graph.name }

    if not graph.has_reversed_arrays():
        edges = graph.edges()
        graph._generate_reversed_di(edges[0], edges[1])

    repMsg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(repMsg)

@typechecked
def diameter(graph: Graph) -> int:
    """ This function generates the diameterof a given graph.
    
    Returns
    -------
    int
        The diameter of the graph.
    
    See Also
    --------
    
    Notes
    -----
    
    Raises
    ------  
    RuntimeError
    """
    cmd = "diameter"
    args = { "GraphName":graph.name }

    if not graph.has_reversed_arrays():
        edges = graph.edges()
        graph._generate_reversed_di(edges[0], edges[1])

    repMsg = generic_msg(cmd=cmd, args=args)
    return int(repMsg)

@typechecked
def subgraph_isomorphism(graph: PropGraph, subgraph: PropGraph,
                         semantic_check:str = None,
                         size_limit:int = None) -> pdarray:
    """
    Given a graph and a subgraph, perform a search in graph matching all possible subgraphs that
    are isomorphic to the subgraph. Uses parallel implementation of the VF2 algorithm 
    (https://ieeexplore.ieee.org/document/1323804).

    Parameters
    ----------
    G : PropGraph
        Host graph that will be searched into. 
    H : PropGraph
        Subgraph (pattern/query) that is being searched for.
    semantic_check : str
        Enables semantic checking on the attributes of the graphs. If `None` then no semantic 
        checking is performed. If `"and"` then all attributes must match for every vertex and edge in
        both the graph and subgraph. If `"or"` then at least one attribute must match for evert vertex
        and edge in both the graph and subgraph.

    Returns
    -------
    pdarray
        Mappings of vertices from graph that match the vertices in subgraph. If there are `n` 
        vertices in the subgraph and the graph has `k` subgraphs that are isomorphic, then the size
        of the returned `pdarray` is `nk`. The array can be thought of as a segmented array where 
        slices of size `k` will give a complete subgraph from the main graph as long as they are 
        made with the assumption that the array starts at index 0.
    
    See Also
    --------
    triangles, k_truss

    Notes
    -----
    The vertices of the subgraph are remapped to a one-up range starting from 0 and this is how they
    are portrayed in the returned `pdarray`. The graph vertices are also remapped internally BUT
    the returned mappings are the original vertex values of the graph.
    """
    cmd = "subgraphIsomorphism"
    args = { "MainGraphName":graph.name,
             "SubGraphName":subgraph.name,
             "SemanticCheckType": str(semantic_check).lower(),
             "TrackSize": str(size_limit).lower() }

    rep_msg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(rep_msg)


@typechecked
def well_connected_components(graph: PropGraph, file_path: str) -> pdarray:
    """
    WORK IN PROGRESS. This is just the skeletong to call the Chapel back-end functionality.

    Parameters
    ----------

    Returns
    -------
    
    See Also
    --------

    Notes
    -----
    """
    cmd = "wellConnectedComponents"
    args = { "MainGraphName":graph.name,
             "FilePath": file_path}

    rep_msg = generic_msg(cmd=cmd, args=args)
    return create_pdarray(rep_msg)
