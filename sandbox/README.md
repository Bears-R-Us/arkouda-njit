## Installation
Run the second or third commands below from within the main `arkouda-njit` directory. The second command generates three comands that have to be copied and pasted into the terminal whereas the third command just automatically pipes them tot he shell. 
```bash
# Print usage instructions.
python module_configuration.py --help

# Sample invocation.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/sandbox/

# Sample execution.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/sandbox/ | bash
```

## Client Code
Now we have two directories
```bash
arkouda_graph/
All graph algorithm related functions

suffix_array/
All suffix array related python functions
```

## Server Code
Now we have the following chapel modules.
```bash
BFSMsg--for breadth first search
TrussMsg--for truss analysis
SuffixArrayMsg--for suffix array
GraphMsg-- for the basic graph operation
TriCntMsg--for triangle counting
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