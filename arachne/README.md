# Arachne: Graph Analysis Extension to Arkouda

## Overview
The Arachne project provides an extension for graph analysis that works with Arkouda. Arachne mimics the NetworkX API while providing high-performance implementations of graph kernels in Chapel. 

## Installation
Installation is performed by running `module_configuration.py`. This file is copied from the `Bears-R-Us/arkouda-contrib` repository. When running `module_configuration.py`, the complete path to the location of the Arkouda repo must be specificed through the `ak_loc` flag along with the complete path to the Arkouda contrib repo. In our case, it would be the complete path to this directory housing Arachne. An example follows below:

```
python3 module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/
```

When the above command completes, the result will be a couple of commands along the lines of:
```
pip install -U /rhome/oaa9/Research/arkouda-njit/arachne/client
cp /rhome/oaa9/Research/arkouda/ServerModules.cfg ~/TmpServerModules.cfg.1681487975
ARKOUDA_SERVER_USER_MODULES=" /rhome/oaa9/Research/arkouda-njit/arachne/server/GraphMsg.chpl" ARKOUDA_CONFIG_FILE=~/TmpServerModules.cfg.1681487975 ARKOUDA_SKIP_CHECK_DEPS=true make -C /rhome/oaa9/Research/arkouda
```

The length of the last command is dependent on the number of modules you have listen inside of `arkouda-njit/arachne/server/ServerModules.cfg`. Within here you can comment in and out the lines of the modules you wish to compile and not compile. By default, all of them are left uncommented.

Next, simply just copy and paste the outputted commands into terminal and your arkouda server should start to build with Arachne added onto it. 

If you run into environment errors, you can run the commands below to ensure both Arachne and Arkouda have been pip installed into your environment. 
```
pip3 install -e /path/to/arachne/client/.
pip3 install -e /path/to/arkouda/.
```

## Usage
Functions currently available can be found in `client/README.md` with a benchmark file that can be used as a sample found in `benchmarks/bfs.py`. Sample executions of benchmark file follow.

For benchmarking a single graph you can execute: 
```
python3 bfs.py node port -f /path/to/arkouda-njit/arachne/data/karate.mtx -t 10
```

For benchmarking a directory of graphs you can execute: 
```
python3 bfs.py node01 5554 -d /path/to/arkouda-njit/arachne/data -t 10
```

## Testing
The Arachne tests are executed from the arkouda-njit/arachne directory as follows:
```
python3 -m pytest test/bfs_test.py test/reading_test.py test/class_test.py
```
**Note**: Errors when executing using pytest from arachne directory. 
