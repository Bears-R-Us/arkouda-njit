import arkouda as ak
import arachne as ar
import argparse
import random
import time
import numpy as np
import sys

def create_parser():
    parser = argparse.ArgumentParser(description="Benchmark for RMAT random graphs")
    parser.add_argument("hostname", help="Hostname of the arkouda server")
    parser.add_argument("port", type=int, default=5555, help="Port used by the arkouda server")

    parser.add_argument("--edge_factor", type=int, default=16,
                        help="Number of edges per vertex")
    parser.add_argument("--scale", type=int, default=16,
                        help="Scale of RMAT graph")
    parser.add_argument("-a", type=float, default=0.57, help="Probability a in RMAT")
    parser.add_argument("-b", type=float, default=0.19, help="Probability b in RMAT")
    parser.add_argument("-c", type=float, default=0.19, help="Probability c in RMAT")
    parser.add_argument("-d", type=float, default=0.05, help="Probability d in RMAT")
    parser.add_argument("-t", "--trials", type=int, default=10,
                        help="Number of trials to run")

    parser.add_argument("--run_bfs", action="store_true", help="Run breadth-first search")
    parser.add_argument("--run_cc", action="store_true", help="Run connected components")
    parser.add_argument("--run_tc", action="store_true", help="Run triangle counting")
    parser.add_argument("--run_tce", action="store_true", help="Run triangle centrality")
    parser.add_argument("--run_mt", action="store_true", help="Run max truss")
    parser.add_argument("--run_td", action="store_true", help="Run truss decomposition")
    parser.add_argument("--run_si", action="store_true", help="Run subgraph isomorphism")
    parser.add_argument("--run_sc", action="store_true", help="Run square counting")
    parser.add_argument("--run_di", action="store_true", help="Run diameter estimation")

    return parser

def compute_statistics(values):
    arr = np.array(values)
    return {
        "min": np.min(arr),
        "first_quartile": np.percentile(arr, 25),
        "median": np.median(arr),
        "third_quartile": np.percentile(arr, 75),
        "max": np.max(arr),
        "mean": np.mean(arr),
        "std_dev": np.std(arr, ddof=1)
    }

def print_statistics(stats, label):
    for k, v in stats.items():
        print(f"{label:<20} {k:<20}: {v:.4f}")

def main():
    parser = create_parser()
    args = parser.parse_args()
    ak.connect(args.hostname, args.port)

    # Ensure only one algorithm is selected
    alg_flags = {
        "bfs": args.run_bfs,
        "cc": args.run_cc,
        "tc": args.run_tc,
        "tce": args.run_tce,
        "mt": args.run_mt,
        "td": args.run_td,
        "si": args.run_si,
        "sc": args.run_sc,
        "di": args.run_di
    }

    enabled = [name for name, active in alg_flags.items() if active]
    if len(enabled) != 1:
        sys.exit("Error: Please select exactly one algorithm to run.")

    algorithm_name = enabled[0]

    # Construct G
    print("Constructing graph G...")
    start_time = time.time()
    g = ar.rmat_graph(args.scale, ar.Graph)
    g_time = time.time() - start_time
    print(f"Graph constructed in {g_time:.4f} seconds.\n")
    print(f"Graph has {len(g):_} vertices and {g.size():_} edges")

    if algorithm_name == "bfs":
        src_idxs = [random.randint(0, len(g) - 1) for _ in range(args.trials)]
        sources = g.nodes()[ak.array(src_idxs)]

    if algorithm_name == "si":
        print("Constructing pattern and directed host graph...")
        src = ak.array([0, 1, 2, 0])
        dst = ak.array([1, 2, 0, 3])
        h = ar.PropGraph()
        h.add_edges_from(src, dst)

        start_time = time.time()
        gd = ar.PropGraph()
        edges = g.edges()
        gd.add_edges_from(edges[0], edges[1])
        gd_time = time.time() - start_time
        print(f"Directed graph constructed in {gd_time:.4f} seconds.\n")

    run_times = []
    teps_values = []

    for i in range(args.trials):
        trial_start = time.time()

        if algorithm_name == "bfs":
            _ = ar.bfs_layers(g, int(sources[i]))
        elif algorithm_name == "cc":
            _ = ar.connected_components(g)
        elif algorithm_name == "tc":
            _ = ar.triangles(g)
        elif algorithm_name == "tce":
            _ = ar.triangle_centrality(g)
        elif algorithm_name == "mt":
            _ = ar.max_truss(g)
        elif algorithm_name == "td":
            _ = ar.truss_decomposition(g)
        elif algorithm_name == "si":
            _ = ar.subgraph_isomorphism(gd, h)
        elif algorithm_name == "sc":
            _ = ar.squares(g)
        elif algorithm_name == "di":
            _ = ar.diameter(g)

        trial_time = time.time() - trial_start
        run_times.append(trial_time)

        # TEPS calculation
        if algorithm_name == "si":
            teps_values.append(gd.size() / trial_time)
        else:
            teps_values.append(g.size() / trial_time)

    print("\n=== Timing Statistics ===")
    timing_stats = compute_statistics(run_times)
    print_statistics(timing_stats, label=f"{algorithm_name} runtime")

    print("\n=== TEPS Statistics ===")
    teps_stats = compute_statistics(teps_values)
    print_statistics(teps_stats, label=f"{algorithm_name} TEPS")

    ak.shutdown()

if __name__ == "__main__":
    main()
