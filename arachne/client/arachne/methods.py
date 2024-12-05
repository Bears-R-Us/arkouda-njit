"""Contains all current Arachne functionality. Includes building methods and algorithmic kernels.
"""
from __future__ import annotations
from typing import cast, Tuple, Union, Literal
import os
from pathlib import Path
from typeguard import typechecked
import arachne as ar
from arachne.graphclass import Graph
from arachne.digraphclass import DiGraph
from arachne.propgraphclass import PropGraph
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray

__all__ = [ "read_matrix_market_file",
            "read_tsv_file",
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
                            only_edges = False,
                            comment_header = "%") -> Union[Graph,DiGraph,Tuple]:
    """Reads a matrix market file and returns the graph specified by the matrix indices. NOTE: the
    absolute path to the file must be given.

    Parameters
    ----------
    filepath : str
        The graph whose breadth-first search layers we want.
    directed : int
        Starting vertex for breadth-first search.
    only_edges : bool
        If `True` will return only `src` and `dst` arrays instead of a graph.
    comment_header : str
        The reader will ignore any files that begin with the comment header.

    Returns
    -------
    Graph | DiGraph
        The graph specified by the matrix market file.
    """
    cmd = "readMatrixMarketFile"
    args = { "Path": filepath,
             "Directed": directed,
             "CommentHeader": comment_header }
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
def read_tsv_file(  filepath: str,
                    directed = False,
                    only_edges = False,
                    comment_header = "#") -> Union[Graph,DiGraph,Tuple]:
    """Reads a `.tsv` file and returns the graph specified by the matrix indices. NOTE: the
    absolute path to the file must be given.

    Parameters
    ----------
    filepath : str
        The graph whose breadth-first search layers we want.
    directed : int
        Starting vertex for breadth-first search.
    only_edges : bool
        If `True` will return only `src` and `dst` arrays instead of a graph.
    comment_header : str
        The reader will ignore any files that begin with the comment header.

    Returns
    -------
    Graph | DiGraph
        The graph specified by the `.tsv` file.
    """
    cmd = "readTSVFile"
    args = { "Path": filepath,
             "Directed": directed,
             "CommentHeader": comment_header }
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
                         size_limit:int = None,
                         time_limit:int = 30,
                         return_isos_as:str = "vertices",
                         algorithm_type:str = "ps",
                         print_progress_interval:int = 2) -> Union[pdarray,Tuple]:
    """
    Given a graph and a subgraph, perform a search in graph matching all possible subgraphs that
    are isomorphic to the subgraph. Uses parallel implementation of the VF2 algorithm 
    (https://ieeexplore.ieee.org/document/1323804).

    Parameters
    ----------
    graph : PropGraph
        Host graph that will be searched into. 
    subgraph : PropGraph
        Subgraph (pattern/query) that is being searched for.
    semantic_check : str
        Enables semantic checking on the attributes of the graphs. If `None` then no semantic 
        checking is performed. If `"and"` then all attributes must match for every vertex and edge 
        in both the graph and subgraph. If `"or"` then at least one attribute must match for every 
        vertex and edge in both the graph and subgraph.
    time_limit : int
        Enables a time limit to return whatever motifs have been found up to that minute.
    size_limit : int
        Caps the number of isomorphisms returned. If `None` then no size limit is enforced. Due to
        the highly parallel nature of subgraph isomorphism, the actual returned number of 
        isomorphisms will always be greater than or equal to `size_limit`. This is due to the fact
        that some parallel tasks may still be in the process of adding a found isomorphism after
        the size limit has been reached. This is allowed to prevent the `size_limit` check from 
        cutting up isomorphisms before they are fully formed and leaving partially found
        isomorphisms in the results.
    return_isos_as : str
        If `"vertices"` then the found isomorphism are returned as vertices corresponding to the
        ordered list of subgraph vertices. If `"edges"` then the edges that make up each isomorphism
        in the original graph are returned. If `"complete"` then both vertices AND edges are
        returned with a mapper to faciliatate finding which subgraph vertex is mapped to a given 
        host graph vertex per subgraph slice.
    algorithm_type : str
        There are currently two versions of subgraph isomorphism available. The version denoted
        by `ps` is a paralell and scalable version of the original VF2 algorithm. The version `si`
        is experimental and creates original states based off existing edges only. Experiments show
        that `si` outperforms `ps` for large graphs.
    print_progress_interval : int
        Maintains how often the progress should be printed server-side for how many patterns have
        been found.

    Returns
    -------
    (pdarray,pdarray)
        If there are `n` vertices in the subgraph and the graph has `k` subgraphs that are 
        isomorphic, then the size of the returned `pdarray` is `n*k`. The array can be thought of as
        a segmented array where slices of size `n` will give a complete subgraph from the main 
        graph. Selected with `return_isos_as = "vertices"`.
    (pdarray,pdarray)
        If there are `m` edges in the subgraph and the graph has `k` subgraphs that are isomorphic, 
        then the size of the returned `pdarray` is `m*k`. The array can be thought of as a segmented
        array where slices of size `m` will give a complete subgraph from the main graph.
        Selected with `return_isos_as = "edges"`.
    (pdarray,pdarray,pdarray,pdarray)
        All the vertex and edge information combined. Selected with `return_isos_as = "complete"`.
    
    See Also
    --------
    triangles, k_truss
    """
    cmd = "subgraphIsomorphism"
    args = { "MainGraphName":graph.name,
             "SubGraphName":subgraph.name,
             "SemanticCheckType": str(semantic_check).lower(),
             "SizeLimit": str(size_limit).lower(),
             "TimeLimit": time_limit,
             "ReturnIsosAs": return_isos_as,
             "AlgorithmType": algorithm_type,
             "PrintProgressInterval": print_progress_interval }

    rep_msg = generic_msg(cmd=cmd, args=args)
    returned_vals = (cast(str, rep_msg).split('+'))

    if return_isos_as == "complete":
        return (create_pdarray(returned_vals[0]), create_pdarray(returned_vals[1]),
                create_pdarray(returned_vals[2]), create_pdarray(returned_vals[3]))

    if return_isos_as == "edges":
        return (create_pdarray(returned_vals[0]), create_pdarray(returned_vals[1]))

    return (create_pdarray(returned_vals[0]), create_pdarray(returned_vals[1]))

@typechecked
def well_connected_components(graph: Graph, file_path: str, output_folder_path: str,
                              output_filename: str = None,
                              output_type: Literal["post", "during", "debug"] = "post",
                              connectedness_criterion: Literal["log10", "log2",
                                                               "sqrt", "mult"] = "log10",
                              connectedness_criterion_mult_value: float = None,
                              pre_filter_min_size: int = 10, post_filter_min_size: int = 10) -> int:
    """
    Executes parallel well-connected components on a given graph and its clustering. Each induced
    cluster subgraph is checked for multiple connected components. If it is composed of more
    than one connected component, each is assigned to a new cluster identifier. Each of these 
    clusters is then checked against a metric (`connectedness_criterion`) to consider if it is 
    well-connected or not. If it is not well-connected, the minimum cut is calculated via VieCut and 
    the cluster is partitioned. Then, the process is repeated until all the clusters are deemed 
    to be well-connected.

    Parameters
    ----------
    graph : Graph
        The input graph.
    file_path : str
        The file containing the clusters each vertex belongs to. NOTE: Must be the absolute path
        to the file.
    output_folder_path : str
        The output folder path to where the new clusters are to be written to. NOTE: Must be the 
        absolute path to the folder.
    output_filename : str
        If not specified, the default output filename will be extrapolated from the name of the
        file specified by `file_path`. If the name of the input file is `foo.tsv` and the 
        `output_type` is `post` then the output filename will be `foo_wcc_output_post.tsv`.
    output_type : str
        If "post" then output is written at the end of WCC. If "during" then output is written as
        soon as a cluster is considered well-connected. If "debug" then verbose output is written
        as soon as a cluster is considered well-connected. NOTE: The "debug" mode is intended to be
        used ONLY with small graphs and clusters. If used with large graphs and clusters, then the
        verbose output is going to clog the whole output folder.
    connectedness_criterion : str
        Specifies the function criterion that should be met for a cluster to be considered
        well-connected. The default is `log10` where if the number of vertices is `n` and the
        minimum cut is `cut` then the inequality `cut > log10(n)` must be true. The other options
        are "log2", "sqrt", and "mult". If "mult" is specified, then 
        `connectedness_criterion_mult_value` must also be specified.
    connectedness_criterion_mult_value : real
        If "mult" is specified as the criterion for `connectedness_criterion`, then the value of
        this must be some nonnegative `int` or `float`.
    pre_filter_min_size : int
        The minimum size of each cluster prior to establishing if the connectedness criterion is
        met or not. The cluster sizes kept are any strictly greater than `pre_filter_min_size`. 
        Defaults to 10.
    post_filter_min_size : int
        The minimum size of each cluster after the connectedness criterion is established to be
        unsatisfactory and the cluster is partitioned. The cluster sizes kept are strictly greater
        than `post_filter_min_size`. Defaults to 10.

    Returns
    -------
    int
        The number of clusters that are found to be well-connected.
    
    See Also
    --------
    connected_components

    Notes
    -----
    Work in progress

    Raises
    ------
    TypeError, ValueError, RuntimeError, FileExistsError
    """
    default_name_used = False
    if output_filename is None:
        try:
            default_name_used = True
            output_filename = Path(file_path).stem
        except TypeError:
            print("Error: `file_path` is not a valid path.")

    if connectedness_criterion == "mult" and connectedness_criterion_mult_value is None:
        raise ValueError(("Connectedness criterion is `mult` and requires a valid "
                          "`connectedness_criterion_mult_value`."))

    if output_folder_path[-1] != "/":
        output_folder_path = output_folder_path + "/"

    output_path = ""
    if default_name_used:
        if output_type == "during":
            output_path = output_folder_path + output_filename + "_wcc_output_during.tsv"
        elif output_type == "post":
            output_path = output_folder_path + output_filename + "_wcc_output_post.tsv"
        elif output_type == "debug":
            output_path = output_folder_path + output_filename + "_wcc_output_debug"
        else:
            raise ValueError(f"The output type {output_type} is not recognized.")
    else:
        output_path = output_folder_path + output_filename

    if os.path.exists(output_path) and output_type == "during":
        raise FileExistsError(f"File {output_filename} already exists.")

    # Explicit value needed for Chapel FCF.
    connectedness_criterion_mult_value = 0.0

    cmd = "wellConnectedComponents"
    args = { "GraphName":graph.name,
             "FilePath": file_path,
             "OutputPath": output_path,
             "OutputType": output_type,
             "ConnectednessCriterion": connectedness_criterion,
             "ConnectednessCriterionMultValue": connectedness_criterion_mult_value,
             "PreFilterMinSize": pre_filter_min_size,
             "PostFilterMinSize": post_filter_min_size}
    rep_msg = generic_msg(cmd=cmd, args=args)
    print("Cluster files written to: ", output_path)

    # TODO: For now returns the number of clusters. In future will return two arrays, one to store
    #       the vertices in all the clusters and the other to store the information to segment this
    #       array to extract what vertices belong to one cluster. For example, indexing this array
    #       in Chapel, to get the vertices for cluster c would look like this:
    #            clusters[seg[c]..<seg[c+1]]
    return int(rep_msg)
