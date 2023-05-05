## Arkouda-NJIT
This is an external repository to build functionality for [Arkouda](https://github.com/Bears-R-Us/Arkouda) such as advanced string and graph processing. It is built with the same structure as [arkouda-contrib](https://github.com/Bears-R-Us/arkouda-contrib) to manage modules and easily swap out functionality. 

## Installation Overview
To install, the user just has to run the `module_configuration.py` file. It will generate commands which you can pipe to a shell for execution which will build the Arkouda server including the functionality from the files specified in `pkg_path`. The complete path to the location of Arkouda must be specified through `ak_loc`.

```bash
# Print usage instructions.
python module_configuration.py --help

# Sample invocation.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/module/

# Sample execution.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/module/ | bash
```

For example, if we are building Arkouda with the functionality provided Arachne we would run the command below:
```bash
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/
```

This generates three commands along the lines of that must be copied and pasted into the terminal unless they were piped straight to the shell ("Sample execution" above):
```bash
pip install -U /complete/path/to/arkouda-njit/arachne/client
cp /complete/path/to/arkouda/ServerModules.cfg ~/TmpServerModules.cfg.1683320760
ARKOUDA_SERVER_USER_MODULES=" /complete/path/to/arkouda-njit/arachne/server/BuildGraphMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/PropertyGraphMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/GraphInfoMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/BFSMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TriCtrMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TriCntMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TrussMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/CCMsg.chpl" ARKOUDA_CONFIG_FILE=~/TmpServerModules.cfg.1683320760 ARKOUDA_SKIP_CHECK_DEPS=true make -C /Users/alvaradoo/Research/arkouda
```

Let's now dissect what each of these commands do separately. The first command, `pip`, installs the dependencies defined by the `setup.py` found at `/complete/path/to/arkouda-njit/arachne/client`. **Note: for the `pip` command to execute without error, the client folder must contain both a `setup.py` file and a `README.md` file**. The second command, `cp`, copies the server modules specified at `/complete/path/to/arkouda/ServerModules.cfg` to a temporary file. Finally, the third command, `make` compiles the `arkouda_server` executable by including both of the modules specified in `ServerModules.cfg` from `/complete/path/to/arkouda-njit/arachne/` and `/complete/path/to/arkouda/`. 

### Usage Notes
```python
import arkouda as ak
import yourModule as ym
# code using module and arkouda below
```

## Available Modules
Currently, there are two available modules, `arachne` and `sandbox`. The graph algorithm implementations with best performance can be found in `arachne` that include code for breadth-first search, triangle counting, triangle centrality, connected components, and k-truss. Unit tests are provided that can be executed by the command available from within the `arachne` folder. Test algorithms and functionality as well as upcoming functionality can be found inside of the `sandbox` folder. 