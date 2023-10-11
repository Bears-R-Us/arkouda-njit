# Arachne: Graph Analysis Extension to Arkouda

## Overview
The Arachne project provides an extension for graph analysis that works with Arkouda. Arachne mimics the NetworkX API while providing high-performance implementations of graph kernels in Chapel. 

## Installation
Installation is performed by running `module_configuration.py` in the main `arkouda-njit` repo. The `module_configuration.py` script should be run as below. Then, follow all the further instructions in the base `arkouda-njit` repo. 

```bash
python3 module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/
```

## Usage
To see an example on how to run and use Arachne, please use `arkouda-njit/arachne/arachne_sample.py` to build a random graph and run breadth-first search on it. This assumes that you have started an Arkouda server using `./arkouda_server` in the Arkouda home directory. The file is executed as follows:
```bash
python3 arachne_sample.py node port n m x y
```
Where `n` is the number of vertices in the graph, `m` is the number of edges, `host` is the locale that the Arkouda server is running on, and `port` is where the Arkouda server is listening on for messages. Further, the graph is populated with `x` labels and `y` relationships.

## Testing
The Arachne tests are executed from the arkouda-njit/arachne directory as follows with pytest:
```bash
python3 -m pytest test/algorithm_test.py test/class_test.py
```
