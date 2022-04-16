from __future__ import annotations
from typing import cast, Tuple, Union
from typeguard import typechecked
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray
from arkouda.logger import getArkoudaLogger
from arkouda.dtypes import int64 as akint

__all__ = ["Graph","graph_query",
           "rmat_gen", "graph_file_read",
           "graph_file_read_mtx",
           "graph_bfs",
           "graph_tri_cnt",
           "graph_tri_ctr",
           "stream_file_read",
           "stream_tri_cnt",
           "streamPL_tri_cnt",
           "graph_ktruss",
           "graph_jaccard_coefficient" ]

class Graph:
    """
    This is a double index graph data structure based graph representation. The graph data resides on the
    arkouda server. The user should not call this class directly;
    rather its instances are created by other arkouda functions.

    Attributes
    ----------
    n_vertices : int
        The starting indices for each string
    n_edges : int
        The starting indices for each string
    directed : int
        The graph is directed (True) or undirected (False)
    weighted : int
        The graph is weighted (True) or not
    name : string
        The graph name in Chapel
    logger : ArkoudaLogger
        Used for all logging operations
        
    Notes
    -----
    """

    def __init__(self, *args) -> None:
        """
        Initializes the Graph instance by setting all instance
        attributes, some of which are derived from the array parameters.
        
        Parameters
        ----------
        n_vertices  : must provide args[0]
        n_edges     : must provide args[1]
        directed    : must provide args[2]
        weighted    : must provide args[3]
        name        : must provide args[4]
        
            
        Returns
        -------
        None
        
        Raises
        ------
        RuntimeError
            Raised if there's an error converting a Numpy array or standard
            Python array to either the offset_attrib or bytes_attrib   
        ValueError
            Raised if there's an error in generating instance attributes 
            from either the offset_attrib or bytes_attrib parameter 
        """
        try:
            if len(args) < 5:
                raise ValueError
            self.n_vertices = int (cast(int, args[0]))
            self.n_edges = int(cast(int, args[1]))
            self.directed = int(cast(int, args[2]))
            self.weighted = int(cast(int, args[3]))
            oriname=cast(str, args[4])
            self.name = oriname.strip()
        except Exception as e:
            raise RuntimeError(e)

        self.dtype = akint
        self.logger = getArkoudaLogger(name=__class__.__name__)  # type: ignore

    def __iter__(self):
        raise NotImplementedError('Graph does not support iteration')

    def __size__(self) -> int:
        return self.n_vertices


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
    elif component =="v_weight":
        attr=-1
    elif component =="e_weight":
        attr=-2
    if int(graph.directed) > 0  :
        assert (attr<=4) 
    if attr < 0:
        assert graph.weighted > 0
    args = "{} {}".format(graph.name,component)
    repMsg = generic_msg(cmd=cmd, args=args)

    return create_pdarray(repMsg)


@typechecked
def graph_file_read(Ne: int, Nv: int, Ncol: int, directed: int, filename: str,\
                    RemapFlag:int=1, DegreeSortFlag:int=0, RCMFlag:int=0, WriteFlag:int=0) -> Graph:
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
    args = "{} {} {} {} {} {} {} {} {}".format(Ne, Nv, Ncol, directed, filename, \
            RemapFlag, DegreeSortFlag, RCMFlag, WriteFlag)
    print(args)
    repMsg = generic_msg(cmd=cmd, args=args)

    return Graph(*(cast(str, repMsg).split('+')))





@typechecked
def graph_file_read_mtx(Ne: int, Nv: int, Ncol: int, directed: int, filename: str,\
                        RemapFlag:int=1, DegreeSortFlag:int=0, RCMFlag:int=0, WriteFlag:int=0) -> Graph:
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
    args = "{} {} {} {} {} {} {} {} {}".format(Ne, Nv, Ncol, directed, filename, \
            RemapFlag, DegreeSortFlag, RCMFlag, WriteFlag)
    print(args)
    repMsg = generic_msg(cmd=cmd, args=args)

    return Graph(*(cast(str, repMsg).split('+')))


@typechecked
def rmat_gen(lgNv: int, Ne_per_v: int, p: float, directed: int, weighted: int) -> Graph:
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
    args = "{} {} {} {} {} {}".format(lgNv, Ne_per_v, p, directed, weighted, RCMFlag)
    msg = "segmentedRMAT {} {} {} {} {}".format(lgNv, Ne_per_v, p, directed, weighted)
    repMsg = generic_msg(cmd=cmd, args=args)

    return Graph(*(cast(str, repMsg).split('+')))


@typechecked
def graph_bfs(graph: Graph, root: int) -> pdarray:
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
    DefaultRatio = 0.9
    RCMFlag = 1
    args = "{} {} {} {} {} {} {} {}".format(
        RCMFlag,
        graph.n_vertices, graph.n_edges,
        graph.directed, graph.weighted,
        graph.name,
        root, DefaultRatio)
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
        args="{} {} {} {} {} {}".format(Ne, Nv, Ncol,directed, filename,factor);
        repMsg = generic_msg(cmd=cmd,args=args)

        return Graph(*(cast(str,repMsg).split('+')))


@typechecked
def graph_triangle (graph: Graph) -> pdarray:
        """
        This function will return the number of triangles in a static graph.
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
        args = "{} {} {} {} {}".format(
                 graph.n_vertices,graph.n_edges,\
                 graph.directed,graph.weighted,\
                 graph.name)

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
        args = "{} {} {} {} {} {}".format(
                 kTrussValue,\
                 graph.n_vertices,graph.n_edges,\
                 graph.directed,graph.weighted,\
                 graph.name)
        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)



@typechecked
def graph_tri_cnt(Ne:int, Nv:int,Ncol:int,directed:int, filename: str)  -> pdarray:
        cmd = "segmentedGraphTri"
        args="{} {} {} {} {}".format(Ne, Nv, Ncol,directed, filename);
        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)

@typechecked
def stream_tri_cnt(Ne:int, Nv:int,Ncol:int,directed:int, filename: str,\
                     factor:int)  -> pdarray:
        cmd = "segmentedStreamTri"
        args="{} {} {} {} {} {}".format(Ne, Nv, Ncol,directed, filename,factor);
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
        args="{} {} {} {} {} {} {}".format(Ne, Nv, Ncol,directed, filename,factor,case);
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
        args = "{} {} {} {} {}".format(
                 graph.n_vertices,graph.n_edges,\
                 graph.directed,graph.weighted,\
                 graph.name)

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
        args = "{} {} {} {} {}".format(
                 graph.n_vertices,graph.n_edges,\
                 graph.directed,graph.weighted,\
                 graph.name)

        repMsg = generic_msg(cmd=cmd,args=args)
        return create_pdarray(repMsg)
