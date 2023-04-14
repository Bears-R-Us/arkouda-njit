# Arachne

## Abstract
Due to the emergence of massive real-world graphs such as social networks, computer networks, and genomes, whose sizes extend to terabytes, new tools must be developed to enable data scientists to handle such graphs efficiently. Arkouda has been developed to allow users to perform massively parallel computations on distributed data with an interface similar to NumPy. This Python package is ubiquitous in the world of Python data science workflows. Based on the Arkouda framework, we have developed a fundamental graph data structure and operations to support graph analytics. Futher, several typical graph algorithms were developed in Chapel to form a basic algorithm library. The methods we have implemented thus far include breadth-first search (BFS), connected components (CC), k-truss (KT), calculating the jaccard coefficient (JC), triangle counting (TC), and triangle centrality (TCE). All our work has been organized as an Arkouda extension package, and it is publicly available on GitHub.

## Modules
- Graph Double-Index Data Structuren Class(es) and Methods
    - `Graph` class for undirected (un)weighted graphs. 
    - `DiGraph` class for directed weighted graphs. 
    - `__len__(self) -> int` returns the number of vertices of a Graph (DiGraph) G. Use `len(G)`.
    - `size(self) -> int` returns the number of edges of a Graph (DiGraph) G. Use `G.size()`.
    - `add_edges_from(self, akarray_src: pdarray, akarray_dst: pdarray, akarray_weight: Union[None, pdarray] = None) -> None` adds to a Graph (DiGraph) object edges from arkouda arrays. The arrays `akarray_src` and `akarray_dst` must be specificed. An optional extra array called `akarray_weight` could be used to make a weighted Graph (DiGraph).
- Graph Building Methods
    - `read_edgelist(path: str, weighted: bool = False, directed: bool = False, comments: str = "#", filetype: str = "txt") -> Union[Graph, DiGraph]` returns a Graph or DiGraph object with read graph data. Removes self-loops and multiedges. Has option to enable reading in a matrix market file that is typically used to store graphs. 
    - `read_known_edgelist(ne: int, nv: int, path: str, weighted: bool = False, directed: bool = False, comments: str = "#", filetype: str = "txt") -> Union[Graph, DiGraph]` returns a Graph or DiGraph object with read graph data. Does not remove self-loops or multiedges. Intended for use when the number of vertices or edges are known for faster graph building times. 
- Algorithms
    - `bfs_layers(graph: Graph, source: int) -> pdarray` returns a depth array with how far each vertex is from the source vertex. Currently, we only support single source BFS.
    - **More to Come!**