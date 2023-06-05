# Arachne: Graph Analysis Extension to Arkouda

## Overview
The Arachne project provides an extension for graph analysis that works with Arkouda. Arachne mimics the NetworkX API while providing high-performance implementations of graph kernels in Chapel. 

## Installation
Installation is performed by running `module_configuration.py` in the main `arkouda-njit` repo. The `module_configuration.py` script should be run as below. Then, follow all the further instructions in the base `arkouda-njit` repo. 

```bash
python3 module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/
```

## Usage
To ensure Arachne is property installed, you can use a `arkouda-njit/arachne/arachne-simple-tests.py` to build a small property graph, filer it, and run some graph kernels. This assumes that you have started an arkouda server using `./arkouda_server` in the arkouda home directory. The file is executed as follows:
```bash
python3 arachne_simple_tests.py node port
```
Where the host name and port number change according to your configuration.

For more involved benchmarking, we have included benchmark files that can be used as a sample found in the `arkouda-njit/arachne/benchmarks` folder. These are currently only available for breadth-first search (bfs). For benchmarking a single graph you can execute: 
```bash
python3 bfs.py node port -f /path/to/arkouda-njit/arachne/data/karate.mtx -t 10
```

For benchmarking a directory of graphs you can execute: 
```bash
python3 bfs.py node port -d /path/to/arkouda-njit/arachne/data -t 10
```

## Testing
The Arachne tests are executed from the arkouda-njit/arachne directory as follows with pytest:
```bash
python3 -m pytest test/algorithm_test.py test/class_test.py test/prop_graph_test.py test/reading_test.py
```
