import arachne as ar
import networkx as nx
import arkouda as ak

ak.connect("n116", 5555)

def create_networkx_graph(src,dst):
    ebunch = list(zip(src.to_list(), dst.to_list()))
    nx_graph = nx.DiGraph()
    nx_graph.add_edges_from(ebunch)
    return nx_graph

def in_degree_ordered_edges(g:ar.DiGraph):
    in_degrees = g.in_degree()
    vertices = g.nodes()
    perm = ak.argsort(ak.coargsort([in_degrees, vertices]))
    edges = g._internal_edges()
    new_src = perm[edges[0]]
    new_dst = perm[edges[1]]
    new_graph = ar.DiGraph()
    new_graph.add_edges_from(new_src,new_dst)
    return new_graph

def out_degree_ordered_edges(g:ar.DiGraph):
    out_degrees = g.out_degree()
    vertices = g.nodes()
    perm = ak.argsort(ak.coargsort([out_degrees, vertices]))
    edges = g._internal_edges()
    new_src = perm[edges[0]]
    new_dst = perm[edges[1]]
    new_graph = ar.DiGraph()
    new_graph.add_edges_from(new_src,new_dst)
    return new_graph

def degree_ordered_edges(g:ar.DiGraph):
    degrees = g.in_degree() + g.out_degree()
    vertices = g.nodes()
    perm = ak.argsort(ak.coargsort([degrees, vertices]))
    edges = g._internal_edges()
    new_src = perm[edges[0]]
    new_dst = perm[edges[1]]
    new_graph = ar.DiGraph()
    new_graph.add_edges_from(new_src,new_dst)
    return new_graph

src = [1, 1, 2, 3, 3, 4, 5, 6, 7, 7, 7, 8, 9, 10, 11, 12]
dst = [5, 4, 7, 4, 4, 7, 2, 3, 3, 9, 4, 3, 3, 11, 10, 11]

graph = ar.DiGraph()
graph.add_edges_from(ak.array(src), ak.array(dst))
original_edges = graph.edges()
original_graph_check = create_networkx_graph(original_edges[0], original_edges[1])

in_degree_ordered_graph = in_degree_ordered_edges(graph)
in_degree_ordered_graph_edges = in_degree_ordered_graph.edges()
in_degree_ordered_check = create_networkx_graph(in_degree_ordered_graph_edges[0],
                                                in_degree_ordered_graph_edges[1])

out_degree_ordered_graph = out_degree_ordered_edges(graph)
out_degree_ordered_graph_edges = out_degree_ordered_graph.edges()
out_degree_ordered_check = create_networkx_graph(out_degree_ordered_graph_edges[0],
                                                out_degree_ordered_graph_edges[1])

degree_ordered_graph = degree_ordered_edges(graph)
degree_ordered_graph_edges = degree_ordered_graph.edges()
degree_ordered_check = create_networkx_graph(degree_ordered_graph_edges[0],
                                             degree_ordered_graph_edges[1])

print(f"In-degree ordering is correct: {nx.is_isomorphic(original_graph_check,in_degree_ordered_check)}")
print(f"Out-degree ordering is correct: {nx.is_isomorphic(original_graph_check,out_degree_ordered_check)}")
print(f"Degree ordering is correct: {nx.is_isomorphic(original_graph_check,degree_ordered_check)}")
