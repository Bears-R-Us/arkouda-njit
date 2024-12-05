## Arkouda-NJIT
This is an external repository to build functionality for [Arkouda](https://github.com/Bears-R-Us/Arkouda) with a focus on advanced graph processing. It is built with the same structure as [arkouda-contrib](https://github.com/Bears-R-Us/arkouda-contrib) to manage modules and easily swap between the production (`arachne`) and development (`arachne_development`) directories.

## Configuring Prerequisites
To install the prerequisites below, the following libraries must be installed on your system. This can be done via any package handler depending on your distribution, or if on a cluster HPC system, they can be loaded in as modules. At the time of writing, the following versions were confirmed to work.
1. GCC 11.2.0 or later.
2. CMake 3.26.3.
3. OpenMPI GNU 4.1.4 (needed by CMake)
4. Anaconda 2023.09-0
5. `jq` 1.6 [command-line JSON processor](https://jqlang.github.io/jq/).

### Prerequisite Installation Steps
We recommend following the installation instructions provided by the Arkouda development team. Most specifically, follow the [Prerequisites](https://github.com/Bears-R-Us/arkouda?tab=readme-ov-file#prerequisites-toc) section in its entirety, and only the [Dependency Configuration](https://github.com/Bears-R-Us/arkouda/blob/master/pydoc/setup/BUILD.md#building-the-server) section of the build instructions. The installation steps usually involve the following:
1. Download [Chapel](https://chapel-lang.org/download.html) from the Chapel downloads page. **Use Chapel version 2.1.0.**
    * Alternatively, you may clone [Chapel](https://github.com/chapel-lang/chapel) and switch to a given tagged version. The commands for these should look something like:
        ```bash
        git clone https://github.com/chapel-lang/chapel.git
        cd chapel
        git fetch --tags origin
        git checkout tags/2.1.0 --force
        ```
2. Build Chapel by executing the commands below. This assumes you have installed all [Chapel prerequisites](https://chapel-lang.org/docs/usingchapel/prereqs.html#chapel-prerequisites). **Note:** We recommend using `gcc/11.2.0` or later due to dependencies with [VieCut](https://github.com/MinhyukPark/VieCut).
    ```bash
    cd /path/to/chapel/
    source ./util/setchplenv.bash
    export CHPL_GMP=bundled
    export CHPL_HWLOC=bundled
    export CHPL_RE2=bundled
    export CHPL_LLVM=bundled
    make -j 4 # This value can be increased dependent on your device's number of processors
    ```
    * **Note:** This installs single locale (shared-memory) Chapel. For multilocale (distributed-memory) Chapel please follow the documentation guide on [Multilocale Chapel Execution](https://chapel-lang.org/docs/usingchapel/multilocale.html#multilocale-chapel-execution). Arachne has its best performance on shared-memory. However, kernels such as breadth-first search and property graph querying have multilocale-optimized versions that require multilocale Chapel to be installed.
3. Download, **but do not build**, [Arkouda](https://github.com/Bears-R-Us/arkouda). **Use Arkouda version v2024.06.21.** A specified version can be selected for download by clicking on `Releases` in the main GitHub page for [Arkouda](https://github.com/Bears-R-Us/arkouda).
    * Alternatively, you may clone Arkouda and switch to a given tagged version.
        ```bash
        git clone https://github.com/Bears-R-Us/arkouda.git
        cd arkouda
        git fetch --tags origin
        git checkout tags/v2024.06.21 --force
        ```
4. Install Arkouda dependencies with `Anaconda`. An environment containing all dependencies can be installed from `arkouda-env.yml` within your Arkouda home directory.
    * This can be done by executing the following command within your Arkouda directory:
        ```bash
        conda env create -f arkouda-env.yml
        ```
5. [Configure your Arkouda dependencies](https://github.com/Bears-R-Us/arkouda/blob/master/pydoc/setup/BUILD.md#dependency-configuration). This involves creating (or modifying) the `Makefile.paths` within your Arkouda home directory.
6. Install [constrained-clustering](https://github.com/MinhyukPark/constrained-clustering) and compile the C++ object files required by Arachne by following the commands below. Constrained-clustering requires a C++ compiler that supports `c++-20`, such as `clang++11`, and `cmake`. These and other prerequisites should be covered by the prerequisites in items 1-5 above.
    ```bash
    cd /path/to/arkouda-njit/arachne/server/external_libs
    git clone https://github.com/MinhyukPark/constrained-clustering.git
    cd constrained-clustering
    ./setup.sh
    ./easy_build_and_compile.sh
    cd ../../../../arachne/server/viecut_helpers/
    source compileLogger.sh -f logger.cpp -o logger.cpp.o
    gcc -c -fPIC -I../external_libs/constrained-clustering/external_libs/VieCut/lib/ -I../external_libs/constrained-clustering/external_libs/VieCut/extlib/tlx/ computeMinCut.cpp -o computeMinCut.o
    cd ../../../
    ```

## Building Arachne
Building Arachne is performed through executing the `module_configuration.py` file. The complete path to the location of `arkouda` must be specified through `ak_loc` and the complete path to the location of `arachne` should be specified through `pkg_path`.

```bash
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/ | bash
```

The above command will pipe the following three commands to terminal that installs Arachne using pip, copies the Arkouda server modules to a temporary file, and combines them with the Arachne server modules to build the enhanced `arkouda_server`.
```bash
pip install -U /complete/path/to/arkouda-njit/arachne/client
cp /complete/path/to/arkouda/ServerModules.cfg ~/TmpServerModules.cfg.1683320760
ARKOUDA_SERVER_USER_MODULES=" /complete/path/to/arkouda-njit/arachne/server/BuildGraphMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/PropertyGraphMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/GraphInfoMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/BFSMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TriCtrMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TriCntMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/TrussMsg.chpl  /complete/path/to/arkouda-njit/arachne/server/CCMsg.chpl" ARKOUDA_CONFIG_FILE=~/TmpServerModules.cfg.1683320760 ARKOUDA_SKIP_CHECK_DEPS=true make -C /Users/alvaradoo/Research/arkouda
```

For usage instructions of `module_configuration.py` please execute the the following.
```bash
python module_configuration.py --help
```

### Building Development Arachne
If you are interested in installing the development version of Arachne, please follow the same instructions as above, but for `pkg_path` include `/complete/path/to/arkouda-njit/arachne_development/`.

## Starting the Arachne and Arkouda Server
The server can be started as specified in the [Arkouda documentation](https://github.com/Bears-R-Us/arkouda#running-arkouda_server-toc). Simply put, navigate to your Arkouda directory, and an executable named `arkouda_server` should exist. Execute it with the command below to start a server instance.
```bash
./arkouda_server # - nl X
```

The output should be something that looks like below.
```bash
********************************************************************************************************
********************************************************************************************************
*                                                                                                      *
*                          server listening on tcp://n118.cluster.local:5555                           *
*                                 arkouda server version = v2024.06.21                                 *
*                                    built with chapel version2.1.0                                    *
*                                     memory limit = 973796998348                                      *
*                                       bytes of memory used = 0                                       *
*                                                                                                      *
********************************************************************************************************
********************************************************************************************************
```

To run a simple test file as well as pytests please proceed to the [Arachne](arachne/) directory for those instructions.

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
