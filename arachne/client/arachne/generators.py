"""Algorithms to create (random) graphs."""
from __future__ import annotations
from typing import Tuple, Union
import arachne as ar
import numpy as np
import arkouda as ak

__all__ = [
    "complete_graph",
    "gnp",
    "karate_club_graph",
    "random_tree",
    "rmat",
    "path_graph",
    "watts_strogatz_graph"
]

def complete_graph(n: int, create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph]) -> Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Generate the complete graph on n nodes.

    Parameters
    ----------
    n : int
        number of nodes

    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor
        constructors supported
        ar.Graph
        ar.DiGraph
        ar.PropGraph

    Returns
    -------
    graph: Union[ar.Graph,ar.DiGraph,ar.PropGraph]
    """
    V = ak.broadcast(ak.arange(0, n * n, n), ak.arange(n), n * n)
    U = ak.arange(V.size) % n
    not_self_loop = V != U
    filtered_V = V[not_self_loop]
    filtered_U = U[not_self_loop]
    graph = empty_graph(create_using)
    graph.add_edges_from(filtered_V,filtered_U)
    return graph

def empty_graph(create_using):
    """Creates empty graph of given type in `create_using`"""
    if create_using is ar.Graph:
        return ar.Graph()
    elif create_using is ar.DiGraph:
        return ar.DiGraph()
    elif create_using is ar.PropGraph:
        return ar.PropGraph()
    else:
        raise Exception("Invalid Constructor")

def gnp(n: int, p: float,
        create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph]
    ) -> Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Generate a random binomial graph.

    Also known as an  Erdos-Renyi or completely random graph.

    Strip out isolates, self-loops and duplicate edges so n_out <= n.

    Parameters
    ----------
    n : int
        number of nodes
    p : float in [0, 1]
        probability of edge formation

    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor
        constructors supported
        ar.Graph
        ar.DiGraph
        ar.PropGraph

    Returns
    -------
    graph: Union[ar.Graph,ar.DiGraph,ar.PropGraph]
    
    """
    m = np.random.binomial(n * (n - 1) // 2, p)  # determine number of edges
    V, U = ak.randint(0, n, m), ak.randint(0, n, m)  # random pairs of nodes
    graph = empty_graph(create_using)
    if V.size == 0 or U.size == 0:
        return graph
    graph.add_edges_from(V,U)
    return graph

def karate_club_graph(create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph]) -> Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Parameters
    ----------
    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor
        constructors supported
        ar.Graph
        ar.DiGraph
        ar.PropGraph

    Return's Zachary's Karate Club Graph

    Each node of the 34 nodes is labelled with a ground truth community.

    Returns
    -------
    C : ak.pdarray[int64] (34 elements)
        community label
    V : ak.pdarray[int64] (156 elements)
        out nodes
    U : ak.pdarray[int64] (156 elements)
        in nodes

    References
    ----------
    An Information Flow Model for Conflict and Fission in Small Groups.
        Wayne W. Zachary. Journal of Anthropological Research, 33, 452-473
        (1977)
    """
    C = ak.array([ 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1,
                   0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ])
    V = ak.array([ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1,
                   1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3,
                   3, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8,
                   8, 9, 9, 10, 10, 10, 11, 12, 12, 13, 13, 13, 13, 13, 14, 14,
                   15, 15, 16, 16, 17, 17, 18, 18, 19, 19, 19, 20, 20, 21, 21,
                   22, 22, 23, 23, 23, 23, 23, 24, 24, 24, 25, 25, 25, 26, 26,
                   27, 27, 27, 27, 28, 28, 28, 29, 29, 29, 29, 30, 30, 30, 30,
                   31, 31, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32,
                   32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
                   33, 33, 33, 33, 33 ])
    U = ak.array([ 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 17, 19, 21, 31, 0, 2,
                   3, 7, 13, 17, 19, 21, 30, 0, 1, 3, 7, 8, 9, 13, 27, 28, 32,
                   0, 1, 2, 7, 12, 13, 0, 6, 10, 0, 6, 10, 16, 0, 4, 5, 16, 0,
                   1, 2, 3, 0, 2, 30, 32, 33, 2, 33, 0, 4, 5, 0, 0, 3, 0, 1, 2,
                   3, 33, 32, 33, 32, 33, 5, 6, 0, 1, 32, 33, 0, 1, 33, 32, 33,
                   0, 1, 32, 33, 25, 27, 29, 32, 33, 25, 27, 31, 23, 24, 31, 29,
                   33, 2, 23, 24, 33, 2, 31, 33, 23, 26, 32, 33, 1, 8, 32, 33,
                   0, 24, 25, 28, 32, 33, 2, 8, 14, 15, 18, 20, 22, 23, 29, 30,
                   31, 33, 8, 9, 13, 14, 15, 18, 19, 20, 22, 23, 26, 27, 28, 29,
                   30, 31, 32 ])
    graph = empty_graph(create_using)
    graph.add_edges_from(V,U)
    return graph  #TODO: when community detection is implemented (C,U,V)

def random_tree(n: int,create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph]) -> Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Generate a random tree

    Parameters
    ----------
    n : int
        number of nodes

    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor
        constructors supported
        ar.Graph
        ar.DiGraph
        ar.PropGraph

    Returns
    -------
    graph: Union[ar.Graph,ar.DiGraph,ar.PropGraph]
    """
    V = ak.arange(n)
    U = ak.randint(0, n, n)
    U = U % V
    graph = empty_graph(create_using)
    graph.add_edges_from(V,U)
    return graph

def rmat(
    scale: int,
    create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph],
    edge_factor: int = 16,
    p: Union[float, Tuple[float]] = (0.57, 0.19, 0.19, 0.05),
    weighted: bool = False,
    permute: bool = True,
) -> Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Recursive MATrix random graph generator.

    Parameters
    ----------
    scale : int
        number of nodes = 2 ** scale
    edge_factor : int
        each node has this many edges
    p : { float | Tuple[float] }
        link-formation probabilites. Single float interpreted as upper-left
        quadrant probability with other quadrants equally sharing the
        complement. Tuples will be intepreted as (a, b, c, d) as described in
        the reference. Defaults to specification from Graph500.
    weighted : bool (default False)
        output uniformly random weights in [0, 1] for each edge.
    permute : bool (default True)
        randomly relabel nodes and permute edges
    

    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor
        constructors supported
        ar.Graph
        ar.DiGraph
        ar.PropGraph

    Returns
    -------
    graph: Union[ar.Graph,ar.DiGraph,ar.PropGraph]

    References
    ----------
    R-MAT: A Recursive Model for Graph Mining.
        Deepayan Chakrabarti, Yiping Zhan and Christos Faloutsos.
        Proceedings of the Fourth SIAM International Conference on Data Mining.
        Apr 22-24 2004

    Notes
    -----
    Stolen brazenly from arkouda/toys/connected_components.py and the Graph500
    benchmark description.
    """
    n = 2 ** scale              # number nodes
    m = n * edge_factor         # number edges

    if isinstance(p, float) and 0 <= p <= 1:
        a = p
        b = c = d = (1.0 - p) / 3.0
    elif isinstance(p, tuple) and all(0 <= x <= 1 for x in p) and sum(p) == 1:
        a, b, c, d = p
    else:
        raise ValueError(f"p = {p} doesn't represent valid probability for RMAT.")
    ab, cNorm, aNorm = a + b, c / (c + d), a / (a + b)

    V, U = ak.zeros(m, dtype='int64'), ak.zeros(m, dtype='int64')
    for i in range(scale):
        vMask = ak.randint(0, 1, m, dtype='float64') > ab
        uMask = (ak.randint(0, 1, m, dtype='float64')
                 > (cNorm * vMask + aNorm * (~vMask)))
        V += vMask * (2 ** i)
        U += uMask * (2 ** i)

    if permute:
        # permute vertex labels
        pi = get_perm(n)
        V, U = pi[V], pi[U]

        # permute edges
        pi = get_perm(m)
        V, U = V[pi], U[pi]

    if weighted:
        W = ak.uniform(V.size)
        graph = empty_graph(create_using)
        if standardize:
            graph.add_edges_from(V, U, W)
        return graph
    else:
        graph = empty_graph(create_using)
        graph.add_edges_from(V, U)
        return graph

def get_perm(n: int) -> ak.pdarray:
    """Create random permutation of [0..n-1]. taken from akgraph.util"""
    randnums = ak.randint(0, 1, n, dtype=ak.float64)
    return ak.argsort(randnums)

def path_graph(n: int,create_using: Union[ar.Graph|ar.DiGraph,ar.PropGraph] ) -> Tuple[ak.pdarray]:
    """Generate the sequential path with n nodes on nodes [0..n-1].
    
    Parameters
    ----------
    n : int
        number of nodes

    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor
        constructors supported
        ar.Graph
        ar.DiGraph
        ar.PropGraph

    Returns
    -------
    graph: Union[ar.Graph,ar.DiGraph,ar.PropGraph]
    """
    V = ak.arange(n - 1)
    U = V + 1
    graph = empty_graph(create_using)
    graph.add_edges_from(V,U)
    return graph

def watts_strogatz_graph(n: int, k: int, p: float,create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph]) ->  Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Generate a small-world network on n nodes.

    Based on the Watts-Strogatz model.

    No self loops or duplicate edges allowed.

    This probably isn't exactly the same as the academic definition
    but it's fast in arkouda.

    Parameters
    ----------
    n : int
        number of nodes to create
    k : int
        average degree of the graph
    p : float
        probability to rewire edges
    
    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor
        constructors supported
        ar.Graph
        ar.DiGraph
        ar.PropGraph

    Returns
    -------
    graph: Union[ar.Graph,ar.DiGraph,ar.PropGraph]

    """
    # create initial sources
    V = ak.broadcast(ak.arange(0, n * k, k), ak.arange(n), n * k)

    # each source is connected to it's k closest neighbors (alphabetically)
    krange = ak.arange(-k // 2, k // 2)
    krange[k // 2 :] += 1
    idx = ak.arange(V.size) % krange.size
    U = krange[idx]
    U[U < 0] = U[U < 0] + n

    # pick some random subset of edges to alter
    changes = ak.randint(0, 1, U.size, dtype=ak.float64) < p
    n_changes = changes.sum()
    U[changes] = ak.randint(0, n, n_changes)

    graph = empty_graph(create_using)
    if V.size == 0 or U.size == 0:
        return graph
    graph.add_edges_from(V,U)

    return graph
