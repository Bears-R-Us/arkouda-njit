## Installation
Follow the steps from within the main `arkouda-njit` repo. The `module_configuration.py` script should be run as below. 
```bash
# Print usage instructions.
python module_configuration.py --help

# Sample invocation.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne_development/

# Sample execution.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne_development/ | bash
```

## Client Code
Now we have two python files
```bash
clinet/arachne_development/graph.py
All graph algorithm related functions

client/arachne_development/suffix_array.py
All suffix array related python functions
```

## Server Code
Now we have the following chapel modules.
```bash
BFSMsg-- for breadth first search
TrussMsg-- for truss analysis
SuffixArrayMsg-- for suffix array
GraphMsg-- for the basic graph operation
TriCntMsg-- for triangle counting
TriCtrMsg-- for triangle centrality
JaccardMsg-- for Jaccard coefficients
CCMsg-- for Connected Components
```

## Test Code
```bash
client: Python test code
   benchmarks: different benchmark code
server:
   UnitTestCh: chaple unit testing code of the extended functions
```