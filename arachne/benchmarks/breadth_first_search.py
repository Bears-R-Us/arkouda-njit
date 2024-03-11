"""Breadth-First Search Benchmark"""
import argparse
import os
import time
import sys
import random
import statistics as st
import arachne as ar
import arkouda as ak

def create_parser():
    """Creates the command line parser for this script"""
    parser = argparse.ArgumentParser(
        description="Benchmark for breadth-first search."
    )
    parser.add_argument("hostname", help="Hostname of the arkouda server")
    parser.add_argument("port", type=int, default=5555,
                        help="Port used by the arkouda server")

    parser.add_argument("--rand", action="store_true", help="Run random benchmark?")

    parser.add_argument("--rand_type", type=str, default="rmat", help="Random graph type to use")
    parser.add_argument("--edge_factor", type=int, default=16,
                        help="Each vertex has this many edges")
    parser.add_argument("--no_permute", action="store_false", help="Do not permute edges?")
    parser.add_argument("--scale", type=int, default=10, help="Scale of RMAT graph")
    parser.add_argument("-a", type=float, default=0.57, help="a of probability list p")
    parser.add_argument("-b", type=float, default=0.19, help="b of probability list p")
    parser.add_argument("-c", type=float, default=0.19, help="c of probability list p")
    parser.add_argument("-d", type=float, default=0.05, help="d of probability list p")

    parser.add_argument("--mtx", action="store_true", help="Run mtx benchmark?")
    parser.add_argument("--filepath", type=str, default="../data/karate.mtx",
                        help=".mtx file to benchmark")

    parser.add_argument("--is_directed", action="store_true", help="Is graph directed?")
    parser.add_argument("-t", "--trials", type=int, default=10,
                        help="Number of trials for BFS"
                        )

    return parser

def run_rand_benchmark(rand_type, is_directed, trials,
                       edge_factor, scale, no_permute, a, b, c, d):
    """Runs rand benchmark and prints out results to terminal."""
    create_using = ar.DiGraph if is_directed else ar.Graph
    graph = None
    start = time.time()
    if rand_type == "rmat":
        permute = not no_permute
        graph = ar.rmat(scale,
                        create_using=create_using,
                        edge_factor=edge_factor,
                        permute=permute,
                        p=(a,b,c,d)
                    )
    else:
        print("Unrecognized random type. Terminating.")
        sys.exit()
    end = time.time()
    direction_as_string = "directed" if is_directed else "undirected"
    print(f"Building {direction_as_string} graph with {len(graph)} vertices and {graph.size()} "
          f"edges took {round(end-start,2)} seconds")

    print("### Arachne Breadth-First Search")
    bfs_trials = []
    trial_vertices = random.sample(range(len(graph)), trials)
    nodes = graph.nodes()
    for u in trial_vertices:
        start = time.time()
        bfs = ar.bfs_layers(graph, int(nodes[u]))
        end = time.time()
        bfs_gb = ak.GroupBy(bfs)
        keys,counts = bfs_gb.count()
        print(keys)
        print(counts)
        print()
        bfs_trials.append(end-start)
    avg_runtime = round(st.mean(bfs_trials), 2)
    print(f"Running breadth-first search on graph took on average {avg_runtime} seconds")

    print("### Full Timings")
    bfs_trials = [round(x,2) for x in bfs_trials]
    print(f"bfs_trials = {bfs_trials}")

def run_mtx_benchmark(args):
    """Runs mtx benchmark and prints out results to terminal."""
    ### Build graph from matrix market file.
    # 1. Use Arachne's matrix_market reading method.
    print("### Arachne Graph Building")
    start = time.time()
    graph = ar.read_matrix_market_file(os.path.abspath(args.filepath), args.directed)
    end = time.time()
    graph_type = "directed" if args.directed else "undirected"
    print(f"Building {graph_type} graph with {len(graph)} vertices and {graph.size()} edges took "
          f"{round(end-start,2)} seconds")

    print()
    print("### Arachne Breadth-First Search")
    ### Run Arachne breadth-first search on the input graph.
    bfs_trials = []
    highest_degree = ak.argmax(graph.degree())
    for _ in range(args.trials):
        start = time.time()
        _ = ar.bfs_layers(graph, int(graph.nodes()[highest_degree]))
        end = time.time()
        bfs_trials.append(end-start)
    avg_runtime = round(st.mean(bfs_trials),2)
    print(f"Running breadth-first search on {graph_type} graph took on average "
          f"{avg_runtime} seconds")

    # 3. Print out times in comma-delimited manner.
    print("### Full Timings")
    bfs_trials = [round(x,2) for x in bfs_trials]
    print(f"bfs_trials = {bfs_trials}")

if __name__ == "__main__":
    # Command line parser and extraction.
    benchmark_parser = create_parser()
    args = benchmark_parser.parse_args()

    # Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)

    # Get Arkouda server configuration information.
    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")

    if args.rand:
        print("\n##### RAND BENCHMARK")
        run_rand_benchmark(args.rand_type,
                           args.is_directed,
                           args.trials,
                           args.edge_factor,
                           args.scale,
                           args.no_permute,
                           args.a, args.b, args.c, args.d)
    elif args.mtx:
        filename = args.filepath.split("/")[-1]
        print(f"\n##### MTX BENCHMARK FOR GRAPH {filename}")
        run_mtx_benchmark(args)
    else:
        print("Unrecognized benchmark type. Terminating.")

    ak.shutdown()
