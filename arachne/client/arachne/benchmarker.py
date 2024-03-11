"""Benchmark wrapper, where for each implementation, two execution times are generated, the
internal server execution time for the kernel only, and the full Python execution time including
server transmissions and any possible preprocessing of data structures. 

Further, some of the benchmarkers return amount of communications made for multilocale 
(distributed-memory) implementations.
"""
from typing import Union
from typeguard import typechecked
import arachne as ar
import arkouda as ak

__all__ = ["bfs_layers_benchmark"]

@typechecked
def bfs_layers_benchmark(graph: Union[ar.Graph,ar.DiGraph],
                         source_vertices: ak.pdarray,
                         check_comms: bool = False) -> ak.pdarray:
    """Copied and pasted breadth-first search python method, used for benchmarking purposes."""
    cmd = "segmentedGraphBFSBenchmark"

    nodes = graph.nodes()
    source_vertices = ak.find(source_vertices, nodes)

    args = {"GraphName":graph.name,
            "SourceVerticesName":source_vertices.name,
            "CheckComms":check_comms}

    rep_msg = ak.generic_msg(cmd=cmd, args=args)
    return ak.create_pdarray(rep_msg)
