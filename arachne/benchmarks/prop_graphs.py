"""Property Graph ETL and Query Benchmark"""
import argparse
import time
import arachne as ar
import arkouda as ak

def create_parser():
    """Creates the command line parser for this script"""
    script_parser = argparse.ArgumentParser(
        description="Run property graph ETL and Query benchmark")
    script_parser.add_argument("hostname", help="Hostname of arkouda server")
    script_parser.add_argument("port", type=int, default=5555, help="Port of arkouda server")
    script_parser.add_argument("scale", type=int, default=10, help="Scale of RMAT graph")

    return script_parser

if __name__ == "__main__":
    parser = create_parser()
    args = parser.parse_args()

    ak.verbose = False
    ak.connect(args.hostname, args.port)

    config = ak.get_config()
    num_locales = config["numLocales"]
    num_pus = config["numPUs"]
    print(f"Arkouda server running with {num_locales}L and {num_pus}PUs.")

    graph = ar.rmat(args.scale, create_using=ar.PropGraph)
    edges = graph.edges()

    k=2
    m=graph.size()
    src_array = edges[0]
    dst_array = edges[1]
    int_array = ak.randint(-1, k, m, dtype=ak.dtype('int64'))
    uint_array = ak.randint(0, k, m, dtype=ak.dtype('uint64'))
    real_array = ak.randint(0, k, m, dtype=ak.dtype('float64'))
    bool_array = ak.randint(0, k, m, dtype=ak.dtype('bool'))
    strings_array = ak.random_strings_uniform(k, k+2, m, characters="ABCDEF")
    test_edge_dict = {
        "src":src_array,
        "dst":dst_array,
        "data1":int_array,
        "data2":uint_array,
        "data3":real_array,
        "data4":bool_array,
        "data5":strings_array,
    }
    test_edge_df = ak.DataFrame(test_edge_dict)
    start = time.time()
    graph.load_edge_attributes(test_edge_df, source_column="src", destination_column="dst",
                               relationship_columns=["data5"])
    end = time.time()
    print(f"ETL process on graph with {graph.size()} edges took {round(end-start,2)} seconds")
    edge_attributes = graph.edge_attributes

    start = time.time()
    int_bool = edge_attributes["data1"] == 0
    new_src = src_array[int_bool]
    new_dst = dst_array[int_bool]
    end = time.time()
    print(f"Integer query on graph with {graph.size()} edges took {round(end-start,2)} seconds")

    start = time.time()
    strings_bool = edge_attributes["data5"].contains("A")
    new_src = src_array[strings_bool]
    new_dst = dst_array[strings_bool]
    end = time.time()
    print(f"String query on graph with {graph.size()} edges took {round(end-start,2)} seconds")

    ak.shutdown()
