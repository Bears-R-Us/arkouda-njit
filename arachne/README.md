# Arachne: Graph Analysis Extension to Arkouda

## Overview
The Arachne project provides an extension for graph analysis that works with Arkouda. Arachne mimics the NetworkX API while providing high-performance implementations of graph kernels in Chapel. 

## Installation
Installation is performed by running `module_configuration.py` in the main `arkouda-njit` repo. The `module_configuration.py` script should be run as below. Then, follow all the further instructions in the base `arkouda-njit` repo. 

```bash
python3 module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/
```

## Usage
To see an example on how to run and use Arachne, please use `arkouda-njit/arachne/arachne_sample.ipynb` to build a random property graph and run queries. This assumes that you have started an Arkouda server using `./arkouda_server` in the Arkouda home directory.

## Testing
The Arachne tests are executed from the arkouda-njit/arachne directory by running the `pytest` command.
