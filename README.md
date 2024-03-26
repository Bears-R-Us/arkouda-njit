## Arkouda-NJIT
This is an external repository to build functionality for [Arkouda](https://github.com/Bears-R-Us/Arkouda) with a focus on advanced graph processing. It is built with the same structure as [arkouda-contrib](https://github.com/Bears-R-Us/arkouda-contrib) to manage modules and easily swap between the production (`arachne`) and development (`arachne_development`) directories.

## Installing Prerequisites
We recommend following the installation instructions provided by the Arkouda development team. Most specifically, follow the [Prerequisites](https://github.com/Bears-R-Us/arkouda?tab=readme-ov-file#prerequisites-toc) section in its entirety, and only the [Dependency Configuration](https://github.com/Bears-R-Us/arkouda/blob/master/pydoc/setup/BUILD.md#building-the-server) section of the build instructions. The installation steps usually involve the following:

1. Download [Arkouda](https://github.com/Bears-R-Us/arkouda). **Arkouda version v2024.03.18 is recommended.** A specified version can be selected for download by clicking on `Releases` in the main repository for Arkouda.
2. Install dependencies with `Anaconda`. An environment containing all dependencies can be installed from `arkouda-env.yml` or `arkouda-env-dev.yml` within your Arkouda home directory.
3. Download and build [Chapel](https://chapel-lang.org/download.html). **Chapel versions 1.33.0 or later are supported.**
4. [Configure your dependencies](https://github.com/Bears-R-Us/arkouda/blob/master/pydoc/setup/BUILD.md#dependency-configuration). This involves creating (or modifying) the `Makefile.paths` within your Arkouda home directory.

## Installing Arachne and Building the Arkouda Server with Arachne Capabilities
Installation is performed through running the `module_configuration.py` file. The complete path to the location of `arkouda` must be specified through `ak_loc` and the complete path to the location of `arachne` should be specified through `pkg_path`.

```bash
# Print usage instructions.
python module_configuration.py --help

# Command to execute to build the Arkouda server with Arachne.
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/ | bash
```

The above command will pipe the following three commands to terminal that installs Arachne using pip, copies the Arkouda server modules to a temporary file, and combines them with the Arachne server modules to build the enhanced `arkouda_server`.
```bash
pip install -U /complete/path/to/arkouda-njit/arachne/client
cp /complete/path/to/arkouda/ServerModules.cfg ~/TmpServerModules.cfg.1683320760
ARKOUDA_SERVER_USER_MODULES=" /complete/path/to/arkouda-njit/arachne/server/BuildGraphMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/PropertyGraphMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/GraphInfoMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/BFSMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TriCtrMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TriCntMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TrussMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/CCMsg.chpl" ARKOUDA_CONFIG_FILE=~/TmpServerModules.cfg.1683320760 ARKOUDA_SKIP_CHECK_DEPS=true make -C /Users/alvaradoo/Research/arkouda
```

The server can be started as specified in the [Arkouda documentation](https://github.com/Bears-R-Us/arkouda#running-arkouda_server-toc). To run a simple test file as well as pytests please proceed to the [arachne](arachne/) folder for those instructions.

### Installing Development Arachne
If you are interested in installing the development version of Arachne, please follow the same instructions as above, but for `pkg_path` include `/complete/path/to/arkouda-njit/arachne_development/`.

## Usage Notes
```python
import arkouda as ak
import arachne as ar
# code using arachne and arkouda below
```

## Common Issues
* **Issue**: Unrecognized HDF5, Apache Arrow, etc. installations. 
  **Fix**: Ensure `Makefile.paths` was properly added to the base Arkouda directory. More information can be found in the [Arkouda build instructions](https://github.com/Bears-R-Us/arkouda#building-arkouda-toc).
* **Issue**: Arkouda or Arachne functions are not recognized when executing scripts.
  **Fix**: Make sure to run `pip3 install -e .` at both `/complete/path/to/arkouda-njit/arachne/client/.` and `/complete/path/to/arkouda/.`
