## Arkouda-NJIT
This is an external repository to build functionality for [Arkouda](https://github.com/Bears-R-Us/Arkouda) with a focus on advanced graph processing. It is built with the same structure as [arkouda-contrib](https://github.com/Bears-R-Us/arkouda-contrib) to manage modules and easily swap between the production (`arachne`) and development (`arachne_development`) directories.

## Verified Versions
The following combination has been tested end-to-end on the Wulver HPC cluster (RHEL 9.5) and on standard Linux desktops:

| Component | Version |
|-----------|---------|
| Chapel | 2.7.0 |
| Arkouda | v2026.02.27 |
| Python | 3.13.1 |
| GCC | 14.2.0 (via foss/2025a on Wulver) |
| CMake | 3.31.3 |
| igraph | 1.0.0 |
| libleidenalg | 0.12 |

## Wulver HPC (Automated Setup)
If you are on the Wulver cluster at NJIT, an automated setup script is available under `training/`. It handles Chapel compilation, Arkouda cloning, conda environment creation, all external library builds, and the OpenSSL workaround.

**Step 1 — Request an interactive node with sufficient memory:**
```bash
srun -p general -N 1 -n 1 --cpus-per-task=32 --qos=standard \
     --account=bader --time=4:00:00 --mem=128G --exclusive --pty bash
```

**Step 2 — Clone this repository and run the setup script:**
```bash
git clone https://github.com/Bears-R-Us/arkouda-njit.git ~/arkouda-njit
cd ~/arkouda-njit
git checkout cm

# Distributed memory (multi-node):
source training/wulver_setup_distributed.sh

# Shared memory (single node):
source training/wulver_setup_shared.sh
```

Each script accepts `--skip-*` flags for phases you have already completed. Run the script with `--help` for the full list.

**Step 3 — Copy the executor helper to your HOME (once):**
```bash
cp training/chpl_wulver_executor.sh ~/chpl_wulver_executor.sh
```

**Step 4 — Launch the server (distributed, multi-node):**
```bash
cd ~/arkouda
source ~/arkouda-njit/training/setDistributedMemoryArachneEnvironment_2.7.0
source ~/chpl_wulver_executor.sh
chpl_wulver_executor --filename=arkouda_server -nl 4 \
    --partition=general --qos=standard --time=2:00:00
```

**To launch shared-memory (single node):**
```bash
cd ~/arkouda
source ~/arkouda-njit/training/setSharedMemoryArachneEnvironment_2.7.0
./arkouda_server
```

## Manual Setup — All Platforms

### Prerequisites

**Linux (apt-based):**
```bash
sudo apt install gcc g++ cmake libopenmpi-dev libglpk-dev python3-dev git
```

**Linux (rpm-based / RHEL / Rocky):**
```bash
sudo dnf install gcc gcc-c++ cmake openmpi-devel glpk-devel python3-devel git
```

**macOS:**
```bash
brew install gcc cmake open-mpi glpk python git
```

Also install [Miniforge](https://github.com/conda-forge/miniforge) or Anaconda for conda.

### Step-by-step Installation

1. **Clone and build Chapel 2.7.0**

   ```bash
   git clone https://github.com/chapel-lang/chapel.git ~/chapel-2.7.0
   cd ~/chapel-2.7.0
   git fetch --tags origin
   git checkout tags/2.7.0 --force

   source ./util/setchplenv.bash
   export CHPL_GMP=bundled
   export CHPL_HWLOC=bundled
   export CHPL_RE2=bundled
   export CHPL_LLVM=bundled
   export CHPL_TARGET_MEM=jemalloc
   # Required on RHEL 9.x with vm.overcommit_memory=2 to prevent std::bad_alloc:
   export CHPL_HOST_MEM=mimalloc
   make -j $(nproc)
   ```

   For multilocale (distributed-memory) builds, also set before `make`:
   ```bash
   export CHPL_COMM=gasnet
   export CHPL_COMM_SUBSTRATE=udp   # use ibv on InfiniBand clusters
   export CHPL_GASNET_SEGMENT=fast
   ```
   See the [Chapel multilocale docs](https://chapel-lang.org/docs/usingchapel/multilocale.html) for details.

2. **Clone Arkouda v2026.02.27**

   ```bash
   git clone https://github.com/Bears-R-Us/arkouda.git ~/arkouda
   cd ~/arkouda
   git fetch --tags origin
   git checkout tags/v2026.02.27 --force
   ```

3. **Create the conda environment**

   ```bash
   conda env create -f ~/arkouda/arkouda-env-dev.yml
   conda activate arkouda-dev
   pip install --no-cache-dir "setuptools==69.5.1"
   cd ~/chapel-2.7.0
   make chapel-py-venv
   ```

4. **Configure Arkouda dependency paths**

   Create `~/arkouda/Makefile.paths` with the path to your conda environment:
   ```makefile
   $(eval $(call add-path,/home/YOUR_USERNAME/.conda/envs/arkouda-dev))
   ```

5. **Clone arkouda-njit**

   ```bash
   git clone https://github.com/Bears-R-Us/arkouda-njit.git ~/arkouda-njit
   cd ~/arkouda-njit
   git checkout cm
   ```

6. **Build constrained-clustering**

   ```bash
   cd ~/arkouda-njit/arachne/server/external_libs
   git clone https://github.com/MinhyukPark/constrained-clustering.git
   cd constrained-clustering
   # Pin to igraph 1.0.0 and libleidenalg 0.12 (required for cmake compatibility)
   # Edit setup.sh: change igraph checkout to tags/1.0.0 and leiden to tags/0.12
   # Edit CMakeLists.txt: find_package(igraph 1.0.0 ...) and find_package(libleidenalg 0.12 ...)
   ./setup.sh
   ./easy_build_and_compile.sh
   ```

7. **Compile viecut_helpers**

   ```bash
   cd ~/arkouda-njit/arachne/server/viecut_helpers/
   source compileLogger.sh -f logger.cpp -o logger.cpp.o
   gcc -c -fPIC \
       -I../external_libs/constrained-clustering/external_libs/VieCut/lib/ \
       -I../external_libs/constrained-clustering/external_libs/VieCut/extlib/tlx/ \
       computeMinCut.cpp -o computeMinCut.o
   cd ~/arkouda-njit/
   ```

8. **Build igraph and libleidenalg**

   ```bash
   cd ~/arkouda-njit/
   source igraph_and_leiden_setup.sh
   ```
   > **Note:** `igraph_and_leiden_setup.sh` must be sourced (not executed) every time you open a new terminal before building or running the server, because it sets `LD_LIBRARY_PATH` and `CPATH`.

9. **Build arkouda_server**

   ```bash
   cd ~/arkouda-njit/
   python module_configuration.py \
       --ak_loc=~/arkouda/ \
       --pkg_path=~/arkouda-njit/arachne/ | bash
   ```

10. **Install Python packages**

    ```bash
    pip3 install -e ~/arkouda-njit/arachne/client/
    pip3 install -e ~/arkouda/
    ```

## Building Arachne
Building Arachne is performed through executing the `module_configuration.py` file. The complete path to the location of `arkouda` must be specified through `ak_loc` and the complete path to the location of `arachne` should be specified through `pkg_path`.

```bash
python module_configuration.py --ak_loc=/complete/path/to/arkouda/ --pkg_path=/complete/path/to/arkouda-njit/arachne/ | bash
```

For usage instructions of `module_configuration.py`:
```bash
python module_configuration.py --help
```

### Building Development Arachne
If you are interested in installing the development version of Arachne, please follow the same instructions as above, but for `pkg_path` include `/complete/path/to/arkouda-njit/arachne_development/`.

## Starting the Arachne and Arkouda Server
Navigate to your Arkouda directory where the `arkouda_server` executable lives.

**Shared memory (single node):**
```bash
./arkouda_server
```

**Distributed memory (multi-node, `-nl` specifies number of locales):**
```bash
./arkouda_server -nl 4
```

The output should look like:
```
*************************************************************************************
*                                                                                   *
*              server listening on tcp://n0077:5555                                 *
*                        arkouda server version = v2026.02.27                      *
*                           built with chapel version 2.7.0                        *
*                            memory limit = 1099511627776                          *
*                              bytes of memory used = 0                            *
*                                                                                   *
*************************************************************************************
```

To run the testing harness via `pytest` please proceed to the [Arachne](arachne/) directory for those instructions.

## Usage Notes
```python
import arkouda as ak
import arachne as ar
# code using arachne and arkouda below
```

## Common Issues

* **Issue**: `std::bad_alloc` during Chapel compilation (resolve/cull phase).
  **Fix**: Export `CHPL_HOST_MEM=mimalloc` **before** running `make` in the Chapel source directory. This is required on RHEL 9.x systems with strict memory overcommit settings (`vm.overcommit_memory=2`).

* **Issue**: `libglpk.so.40: No such file or directory` when linking igraph.
  **Fix**: GLPK must be available at link time. On Wulver: `module load GLPK`. On other systems: `sudo apt install libglpk-dev` or equivalent.

* **Issue**: `symbol lookup error: ... undefined symbol: OPENSSL_3.0.1` when starting `arkouda_server`.
  **Fix**: The conda-forge OpenSSL (3.6.x) is missing the `OPENSSL_3.0.1` versioned ABI symbol that the system OpenSSL requires. Remove conda's copies so the dynamic linker falls through to the system library:
  ```bash
  rm -f ~/.conda/envs/arkouda-dev/lib/libcrypto.so.3
  rm -f ~/.conda/envs/arkouda-dev/lib/libssl.so.3
  rm -f ~/.conda/envs/arkouda-dev/lib/libcrypto.so
  rm -f ~/.conda/envs/arkouda-dev/lib/libssl.so
  ```

* **Issue**: `libleidenalgConfigVersion.cmake` version mismatch after running `setup.sh`.
  **Fix**: After `./setup.sh` completes, patch the generated cmake version file:
  ```bash
  find arachne/server/external_libs/constrained-clustering/external_libs \
      -name "libleidenalgConfigVersion.cmake" \
      -exec sed -i 's/set(PACKAGE_VERSION "[^"]*")/set(PACKAGE_VERSION "0.12")/' {} \;
  ```

* **Issue**: Unrecognized HDF5, Apache Arrow, etc. installations.
  **Fix**: Ensure `Makefile.paths` was properly added to the base Arkouda directory. More information can be found in the [Arkouda build instructions](https://github.com/Bears-R-Us/arkouda#building-arkouda-toc).

* **Issue**: Arkouda or Arachne functions are not recognized when executing scripts.
  **Fix**: Make sure to run `pip3 install -e .` at both `/complete/path/to/arkouda-njit/arachne/client/.` and `/complete/path/to/arkouda/.`