## Purpose
This is an external repo to build Graph related functionality for `Arkouda`
(see https://github.com/Bears-R-Us/Arkouda)

## Generate Server Code
To generate the server code run the `server-config.py` file.
It will generate commands which you can pipe to a shell for execution which
will build the Arkouda server including the Graph server functions.

```bash
# Print usage instructions
python server-config.py --help

# Sample invocation
python server-config.py --arkouda=$ArkoudaHomeDirectory

# Sample execution
python server-config.py --arkouda=$ArkoudaHomeDirectory | bash
```

## Client code
Now we have two directories
```bash
arkouda_graph/
All graph algorithm related functions

suffix_array/
All suffix array related python functions

```

## Server code
Now we have the following chapel modules.
```bash
BFSMsg--for breadth first search
TriCntMsg--for triangle counting
TrussMsg--for truss analysis
SuffixArrayMsg--for suffix array
SuffixArrayMsg
GraphMsg-- for the basic graph operation
TriCtrMsg-- for triangle centrality
JaccardMsg-- for Jaccard coefficients
CCMsg-- for Connected Components
```


## Test  code
```bash
client: Python test code
   benchmarks: different benchmark code
server:
   UnitTestCh: chaple unit testing code of the extended functions
```


## Call extended functions in
```bash
(1) Under the master arkouda directory, copy the arkouda-njit directory to here and rename it as arkouda_njit or 
create a arkouda_njit link to the arkouda-njit directory
(2) import arkouda_njit as njit
(3) call all the extended function  as njit.function
```
