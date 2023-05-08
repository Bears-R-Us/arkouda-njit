## Arkouda-NJIT
This is an external repository to build functionality for [Arkouda](https://github.com/Bears-R-Us/Arkouda) with a focus on advanced graph processing. It is built with the same structure as [arkouda-contrib](https://github.com/Bears-R-Us/arkouda-contrib) to manage modules and easily swap between the production (`arachne`) and development (`arachne_development`) directories.

## Prerequisites
1. Download and build [Chapel](https://chapel-lang.org/download.html).
2. Download but **do not build** [Arkouda](https://github.com/Bears-R-Us/arkouda). We recommend using the most recent release.
3. Follow instructions to activate the Arkouda environment and install all [prerequisites](https://github.com/Bears-R-Us/arkouda#prerequisites-toc). **Note: we recommend you use `Anaconda` to manage all dependencies.** 

## Installation Overview
Installation is performed through runing the `module_configuration.py` file. The complete path to the location of `arkouda` must be specified through `ak_loc` and the complete path to the location of `arachne` should be specified through `pkg_path`. Executing this file will generate commands that can be piped to the shell for execution or copied and pasted. 

```bash
# Print usage instructions.
python module_configuration.py --help

# Sample invocation to generate commands that must then be copied and pasted.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/

# Sample execution that pipes the commands directly to the terminals.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/ | bash
```

After running the above command, the result should commands along the lines of:
```bash
pip install -U /complete/path/to/arkouda-njit/arachne/client
cp /complete/path/to/arkouda/ServerModules.cfg ~/TmpServerModules.cfg.1683320760
ARKOUDA_SERVER_USER_MODULES=" /complete/path/to/arkouda-njit/arachne/server/BuildGraphMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/PropertyGraphMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/GraphInfoMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/BFSMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TriCtrMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TriCntMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TrussMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/CCMsg.chpl" ARKOUDA_CONFIG_FILE=~/TmpServerModules.cfg.1683320760 ARKOUDA_SKIP_CHECK_DEPS=true make -C /Users/alvaradoo/Research/arkouda
```

These commands will need to be executed to build the Arkouda server with the added functionality. Then, the server can be started as specified in the [Arkouda documentation](https://github.com/Bears-R-Us/arkouda#running-arkouda_server-toc).

## Usage Notes
```python
import arkouda as ak
import arachne as ar
# code using arachne and arkouda below
```

## Common Issues
* **Issue**: Unrecognized HDF5, Apache Arrow, etc. installations. 
  **Fix**: Ensure `Makefile.paths` was properly added to the base Arkouda directory. More information can be found in the [Arkouda build instructions](https://github.com/Bears-R-Us/arkouda#building-arkouda-toc).