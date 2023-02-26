from __future__ import annotations
from typing import cast, Tuple, Union
from typeguard import typechecked
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray
from arkouda.logger import getArkoudaLogger
from arkouda.dtypes import int64 as akint
import arkouda as ak

__all__ = ["Graph","DiGraph", "graph_query",
           "rmat_gen", "graph_file_read",
           "graph_add_property",
           "graph_edgearray", 
           "graph_file_preprocessing",
           "graph_file_tonde",
           "graph_file_read_mtx",
           "graph_bfs",
           "graph_triangle",
           "graph_cc",
           "graph_tri_ctr",
           "stream_file_read",
           "stream_tri_cnt",
           "streamPL_tri_cnt",
           "graph_ktruss",
           "graph_jaccard_coefficient", 
           "graph_jaccard_hash" ]

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
                self.n_vertices = 0
                self.n_edges = 0
                self.weighted = None
                self.directed = 0
                self.name = None
            else:
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

    def nodes(self) ->pdarray:
        print("We should return the original node array")
        print("to be implemented")
        return None

    def edges(self) -> Tuple[pdarray, pdarray]:
        src=graph_query(self,"src")
        dst=graph_query(self,"dst")
        return [src,dst]

class DiGraph(Graph):
    """Base class for directed graphs. Inherits from Graph.
    This is the double index graph data structure based graph representation. The graph data resides 
    on the arkouda server. The user should not call this class directly; rather its instances are 
    created by other arachne functions.
    Graphs hold undirected edges. Self loops and multiple edges are not allowed.
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
def graph_bfs(graph: Graph, root: int, rcm_flag:int) -> pdarray:
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

