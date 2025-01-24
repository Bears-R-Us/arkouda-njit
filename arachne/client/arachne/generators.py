"""Algorithms to create (random) graphs."""
from __future__ import annotations
from typing import Tuple, Union, cast
import random
import arachne as ar
import numpy as np
import arkouda as ak
from arkouda.client import generic_msg
from arkouda.pdarrayclass import create_pdarray

__all__ = [
    "complete_graph",
    "karate_club_graph",
    "path_graph",
    "random_tree",
    "gnp_random_graph",
    "rmat_graph",
    "watts_strogatz_graph",
    "barabasi_albert_graph"
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

def path_graph(n: int,create_using: Union[ar.Graph|ar.DiGraph,ar.PropGraph] ) -> Tuple[ak.pdarray]:
    """Generate the sequential path with n nodes on nodes [0..n-1].
    
    Parameters
    ----------
    n : int
        number of nodes

    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor.

    Returns
    -------
    graph: Union[ar.Graph,ar.DiGraph,ar.PropGraph]
    """
    V = ak.arange(n - 1)
    U = V + 1
    graph = empty_graph(create_using)
    graph.add_edges_from(V,U)
    return graph

def rmat_graph(
    scale: int,
    create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph],
    edge_factor: int = 16,
    p: Tuple[float] = (0.57, 0.19, 0.19, 0.05),
    weighted: bool = False,
) -> Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Recursive MATrix random graph generator.

    Parameters
    ----------
    scale : int
        Number of vertices is 2**scale.
    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor
    edge_factor : int
        Each node has up to this many edges.
    p : Tuple[float]
        Link-formation probabilites. Tuples will be intepreted as (a, b, c, d) as described in
        the reference. Defaults to specification from Graph500.
    weighted : bool (default False)
        output uniformly random weights in [0, 1] for each edge.

    Returns
    -------
    graph: Union[ar.Graph,ar.DiGraph,ar.PropGraph]

    References
    ----------
    R-MAT: A Recursive Model for Graph Mining.
           Deepayan Chakrabarti, Yiping Zhan and Christos Faloutsos.
           Proceedings of the Fourth SIAM International Conference on Data Mining.
           Apr. 22-24, 2004.

    Notes
    -----
    Uses the Graph500 RMAT benchmark description algorithm.
    """
    n = 2 ** scale              # number nodes
    m = n * edge_factor         # number edges

    if isinstance(p, tuple) and all(0 <= x <= 1 for x in p) and sum(p) == 1:
        a, b, c, d = p
    else:
        raise ValueError(f"p = {p} doesn't represent valid probability for RMAT.")
    
    cmd = "buildRMATGraph"
    args = {  "A": a,
              "B": b,
              "C": c,
              "D": d,
              "Scale": scale,
              "EdgeFactor": edge_factor }

    rep_msg = generic_msg(cmd=cmd, args=args)
    returned_vals = (cast(str, rep_msg).split('+'))

    U = create_pdarray(returned_vals[0])
    V = create_pdarray(returned_vals[1])

    if weighted:
        W = ak.uniform(U.size)
        graph = empty_graph(create_using)
        graph.add_edges_from(U, V, W)
        return graph
    else:
        graph = empty_graph(create_using)
        graph.add_edges_from(U, V)
        return graph

def gnp_random_graph(n: int, p: float,
                     create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph], 
                     seed: int = None) -> Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Generate a random binomial graph. Also known as an Erdos-Renyi or completely random graph.
    Does not allow for the creation of isolates, self-loops, or duplicated edges.

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
    U = ak.broadcast(ak.arange(0, n*n, n), ak.arange(n), n*n)
    V = ak.arange(U.size) % n

    not_self_loop = V != U
    filtered_U = U[not_self_loop]
    filtered_V = V[not_self_loop]

    probabilities = ak.randint(0, 1, filtered_U.size, dtype=ak.float64, seed=seed)

    kept_edges = probabilities < p
    kept_U = filtered_U[kept_edges]
    kept_V = filtered_V[kept_edges]

    graph = empty_graph(create_using)

    if V.size == 0 or U.size == 0:
        return graph

    graph.add_edges_from(kept_U,kept_V)

    return graph

def watts_strogatz_graph(n: int, k: int, p: float, 
                         create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph]) ->  Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    Generate a small-world network on n nodes based on the Watts-Strogatz model. Each vertex will
    have an average degree of k. No self loops or duplicated edges allowed.

    Parameters
    ----------
    n : int
        Number of vertices to create.
    k : int
        Average degree of the graph.
    p : float
        Probability to rewire edges.
    
    create_using : Union[ar.Graph,ar.DiGraph,ar.PropGraph]
        Arachne graph constructor.

    Returns
    -------
    graph : Union[ar.Graph,ar.DiGraph,ar.PropGraph]

    """
    # Create nodes.
    nodes = ak.arange(n)

    # Used to track the pdarrays that will make up the source and destination arrays.
    sources = []
    targets = []

    # Create the lattice.
    for j in range(1, k // 2 + 1):
        a = nodes[j:]
        b = nodes[0:j]
        targets.extend([a,b])
        sources.append(nodes)

    # Concatenate all sources together into U and all targets together into V.
    U = ak.concatenate(sources)
    V = ak.concatenate(targets)

    # Pick some random subset of edges to alter.
    changes = ak.randint(0, 1, V.size, dtype=ak.float64) < p
    n_changes = changes.sum()
    V[changes] = ak.randint(0, n, n_changes)

    graph = empty_graph(create_using)
    if V.size == 0 or U.size == 0:
        return graph
    graph.add_edges_from(V,U)

    return graph

def barabasi_albert_graph(
    n: int,
    m: int,
    create_using: Union[ar.Graph,ar.DiGraph,ar.PropGraph],
) -> Union[ar.Graph,ar.DiGraph,ar.PropGraph]:
    """
    TODO: Add documentation.
    """
    # Create star graph.
    src = ak.full(m, 0, dtype=ak.int64)
    dst = ak.arange(1, m+1)
    repeated_nodes = ak.concatenate([src, dst])
    
    cmd = "buildBarabasiAlbertGraph"
    args = {  "N": n,
              "M": m,
              "Src": src,
              "Dst": dst,
              "RepeatedNodes": repeated_nodes }

    rep_msg = generic_msg(cmd=cmd, args=args)
    returned_vals = (cast(str, rep_msg).split('+'))

    U = create_pdarray(returned_vals[0])
    V = create_pdarray(returned_vals[1])

    graph = empty_graph(create_using)
    graph.add_edges_from(U, V)
    return graph