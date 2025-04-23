import arkouda as ak
import arachne as ar
import time

ak.connect("n120", 5555)

# Parameters
p = 0.0005
node_sizes = [60_000]
seed = 42
num_tests = 3

# Fixed attributes for subgraph
subgraph_node_ints = ak.array([10, 10,10])
subgraph_node_bools = ak.array([True, True, True])
subgraph_edge_ints = ak.array([5, 5, 5, 5, 5])
subgraph_edge_bools = ak.array([True, True, True, True, True])

# Subgraph structure
src_list = [0, 1, 1, 2, 0]
dst_list = [1, 0, 2, 0, 2]

 
src_subgraph = ak.array(src_list)
dst_subgraph = ak.array(dst_list)

# Subgraph dataframes
edge_df_h = ak.DataFrame({
    "src": src_subgraph,
    "dst": dst_subgraph,
    "rels1": subgraph_edge_ints,
    "rels2": subgraph_edge_bools
})

node_df_h = ak.DataFrame({
    "nodes": ak.array(list(set(src_list + dst_list))),
    "lbls2": subgraph_node_ints,
    "lbls3": subgraph_node_bools
})

# Create the subgraph
sg = ar.PropGraph()
sg.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst")
sg.load_node_attributes(node_df_h, node_column="nodes")

# Run for different node sizes
for num_nodes in node_sizes:
    print(f"\nRunning for num_nodes = {num_nodes} with p = {p}")

    # Generate the property graph
    start = time.time()
    temp_prop_graph = ar.gnp_random_graph(num_nodes, p, create_using=ar.PropGraph, seed=seed)
    end = time.time()
    build_time = end - start

    print(f"Graph with {len(temp_prop_graph)} vertices and {temp_prop_graph.size()} edges "
          f"built in {round(build_time, 2)} seconds.")

    # Generate random attributes for the main graph
    num_edges = temp_prop_graph.size()
    edges = temp_prop_graph.edges()
    nodes = temp_prop_graph.nodes()

    node_ints = ak.array([10] * len(nodes))  # Fixed for simplicity
    node_bools = ak.array([True] * len(nodes))  # Fixed for simplicity
    edge_ints = ak.array([5] * len(edges[0]))  # Fixed for simplicity
    edge_bools = ak.array([True] * len(edges[0]))  # Fixed for simplicity

    edge_df = ak.DataFrame({
        "src": edges[0],
        "dst": edges[1],
        "rels1": edge_ints,
        "rels2": edge_bools
    })

    node_df = ak.DataFrame({
        "nodes": nodes,
        "lbls2": node_ints,
        "lbls3": node_bools
    })

    prop_graph = ar.PropGraph()
    prop_graph.load_edge_attributes(edge_df, source_column="src", destination_column="dst")
    prop_graph.load_node_attributes(node_df, node_column="nodes")

    # Initialize averages
    test_results = {
        "VF2-SI": {"monos": 0, "time": 0},
        # "VF2-SI PROBABILITY-MVE": {"monos": 0, "time": 0},
        "VF2-PS DEFAULT": {"monos": 0, "time": 0},
        # "VF2-PS MVE-REORDERING": {"monos": 0, "time": 0},
        # "VF2-PS PROBABILITY-MVE": {"monos": 0, "time": 0},
    }

    # Run tests
    for test_run in range(num_tests):
        print(f"  Test run {test_run + 1}/{num_tests}")

        # VF2-SI
        start = time.time()
        isos_as_vertices = ar.subgraph_isomorphism(
            prop_graph, sg, semantic_check="and",
            match_type = "iso",
            algorithm_type="si", reorder_type="structural", return_isos_as="vertices"
        )
        end = time.time()
        result = len(isos_as_vertices[0]) / len(sg)
        test_results["VF2-SI"]["monos"] += result
        test_results["VF2-SI"]["time"] += (end - start)
        print("iso Time: ",end - start )
        print("We found: ",result )        

        # start = time.time()
        # # isos_as_vertices = ar.subgraph_isomorphism(
        # #     prop_graph, sg, semantic_check="and",
        # #     match_type = "mono",
        # #     algorithm_type="si", reorder_type="structural", return_isos_as="vertices"
        # # )
        # isos_as_vertices = ar.subgraph_isomorphism(prop_graph, sg, 
        #                                    semantic_check = "and", algorithm_type = "ps", 
        #                                    reorder_type = None, return_isos_as = "vertices")

        # print(f"We found {len(isos_as_vertices[0])/len(sg)} monos inside of the graph")
        
        # end = time.time()
        # result = len(isos_as_vertices[0]) / len(sg)
        # test_results["VF2-SI"]["monos"] += result
        # test_results["VF2-SI"]["time"] += (end - start)
        # print("mono Time: ",end - start )        
        # print("We found: ",result )        
        # # VF2-SI PROBABILITY-MVE
        # start = time.time()
        # isos_as_vertices = ar.subgraph_isomorphism(
        #     prop_graph, sg, semantic_check="and",
        #     algorithm_type="si", reorder_type="probability", return_isos_as="vertices"
        # )
        # end = time.time()
        # result = len(isos_as_vertices[0]) / len(sg)
        # test_results["VF2-SI PROBABILITY-MVE"]["monos"] += result
        # test_results["VF2-SI PROBABILITY-MVE"]["time"] += (end - start)

        # # VF2-PS DEFAULT
        # start = time.time()
        # isos_as_vertices = ar.subgraph_isomorphism(
        #     prop_graph, sg, semantic_check="and",
        #     algorithm_type="ps", reorder_type=None, return_isos_as="vertices"
        # )
        # end = time.time()
        # result = len(isos_as_vertices[0]) / len(sg)
        # test_results["VF2-PS DEFAULT"]["monos"] += result
        # test_results["VF2-PS DEFAULT"]["time"] += (end - start)

        # # VF2-PS MVE-REORDERING
        # start = time.time()
        # isos_as_vertices = ar.subgraph_isomorphism(
        #     prop_graph, sg, semantic_check="and",
        #     algorithm_type="ps", reorder_type="structural", return_isos_as="vertices"
        # )
        # end = time.time()
        # result = len(isos_as_vertices[0]) / len(sg)
        # test_results["VF2-PS MVE-REORDERING"]["monos"] += result
        # test_results["VF2-PS MVE-REORDERING"]["time"] += (end - start)

        # # VF2-PS PROBABILITY-MVE
        # start = time.time()
        # isos_as_vertices = ar.subgraph_isomorphism(
        #     prop_graph, sg, semantic_check="and",
        #     algorithm_type="ps", reorder_type="probability", return_isos_as="vertices"
        # )
        # end = time.time()
        # result = len(isos_as_vertices[0]) / len(sg)
        # test_results["VF2-PS PROBABILITY-MVE"]["monos"] += result
        # test_results["VF2-PS PROBABILITY-MVE"]["time"] += (end - start)

    # Compute averages
    for test in test_results:
        test_results[test]["monos"] /= num_tests
        test_results[test]["time"] /= num_tests

    # Print results
    print(f"\nResults for num_nodes = {num_nodes}:")
    for test, results in test_results.items():
        print(f"  {test}:")
        print(f"    Average monos found: {results['monos']}")
        print(f"    Average execution time: {results['time']:.2f} seconds")
