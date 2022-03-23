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
python server-config.py --arkouda=$HOME/projects/arkouda

# Sample execution
python server-config.py --arkouda=$HOME/projects/arkouda | bash
```

## Client code
Now we have three directories
arkouda_graph/
All graph algorithm related functions

suffix_array/
All suffix array related python functions

benchmark/
All python testing code for different python functions

## Server code
Now we have the following chapel modules.
BFSMsg--for bread first search
TriCntMsg--for triangle counting
TrussMsg--for truss analysis
SuffixArrayMsg--for suffix array

##Run Python Code
Just copy the arkouda-njit directory under the master arkouda and rename it as arkouda_njit, 
next, import arkouda_njit as njit,
then all the extended functions can be used in python as njit.function

