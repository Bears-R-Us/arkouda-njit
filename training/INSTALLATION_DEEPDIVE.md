# Introduction
[Arachne](https://github.com/Bears-R-Us/arkouda-njit) is a scalable framework for exploratory graph analytics tailored to Python data scientists.  It builds on [Arkouda](https://github.com/Bears-R-Us/arkouda), a parallel and distributed array-processing library designed to support array and dataframe-like computations at scale.  
While Arkouda offers functionality analogous to [NumPy](https://numpy.org) and [Pandas](https://pandas.pydata.org), Arachne extends this model to graph analytics with an interface similar to [NetworkX](https://networkx.org).  This guide serves both new and existing developers, providing insight into the design rationale and internal structure of the codebase.  It includes detailed instructions for environment setup, code compilation, and running unit tests using [PyTest](https://pytest.org).  This document is a verbose version of the Arachne installation steps found on [GitHub](https://github.com/Bears-R-Us/arkouda-njit).

# Setting Up Prerequisites
In general, the prerequisite setup process should be straightforward for users familiar with installing software on Linux systems.  To install the required dependencies listed below, you may use your distribution's package manager (e.g., `apt`, `yum`, `pacman`), or load the packages via environment modules if working on a high-performance computing (HPC) cluster.  The following versions have been confirmed to work end-to-end on Wulver (RHEL 9.5):

1. [GCC](https://gcc.gnu.org) 14.2.0 (via `foss/2025a`); **14.2.0 or any GCC ≥ 11.2.0 should work**
2. [CMake](https://cmake.org) 3.31.3; **3.26.3 or later**
3. [OpenMPI](https://www.open-mpi.org) 5.0.7 (provided by `foss`); **4.1.4 or later**
4. [Miniforge3](https://github.com/conda-forge/miniforge) 24.11.3-0 or any recent Anaconda/Miniforge distribution
5. [GLPK](https://www.gnu.org/software/glpk/) 5.0 — required at link time when building igraph
6. [jq](https://stedolan.github.io/jq) 1.6, a command-line JSON processor

These prerequisites are common for software built from source.  [GCC](https://gcc.gnu.org) provides compilers for C and C++ code.  [CMake](https://cmake.org) is a build system generator that facilitates the compilation process.  [OpenMPI](https://www.open-mpi.org) is used by CMake to enable parallel compilation tasks.  Miniforge (or Anaconda) serves as the Python environment manager and also installs key dependencies for Arachne and Arkouda, including [ZeroMQ](https://zeromq.org).  [GLPK](https://www.gnu.org/software/glpk/) is the GNU Linear Programming Kit, which igraph links against.  [jq](https://stedolan.github.io/jq) is employed during the build process of the [VieCut](https://github.com/VieCut/VieCut) library to construct a logging component required by Arachne's well-connectedness routines.

**Not required:** Intel oneAPI compiler and Intel MKL are not needed for this build.  The `foss` toolchain (GCC + OpenMPI + OpenBLAS + FFTW) covers all requirements.

## Setting Up Your Terminals
It is recommended to launch an interactive terminal with `srun` during the installation process on Wulver, as the login nodes have very limited resources.  An automated setup script is available at `training/wulver_setup.sh` (distributed memory) and `training/wulver_setup_shared.sh` (shared memory) in this repository.  However, it is recommended to do it manually for developers to become familiar with all the steps and be able to help with debugging user installations.  To launch an interactive terminal you can use the following command:

```bash
srun -p general -N 1 -n 1 --cpus-per-task=32 --qos=standard --account=bader --time=4:00:00 --mem=128G --exclusive --pty bash
```

Use at least `--mem=128G`.  Chapel's compilation resolve phase can use up to ~10 GB of memory, and on Wulver (RHEL 9.5, `vm.overcommit_memory=2`) the build will crash with `std::bad_alloc` if physical memory is insufficient.

## Installing Chapel
Both Arkouda and Arachne are primarily implemented in the [Chapel](https://chapel-lang.org) programming language, with supplemental functionality written in C and C++ as needed.  Chapel supports two primary build configurations: with and without inter-locale communication.  A *locale* in Chapel represents a computational unit—typically a compute node with its own memory and processing cores—used to enable parallel and distributed execution.

Currently, most algorithms in Arachne achieve the best performance when compiled in shared-memory mode (i.e., without communication across locales).  However, several key routines—including breadth-first search, graph attribute queries, and well-connected components—have distributed-memory implementations optimized for multi-locale execution.  While all Arachne functionality can technically be run in multi-locale mode, performance may degrade compared to single-locale execution due to the added communication overhead inherent in distributed systems.

The Chapel environment is primarily defined by a system of environment variables that must be set before compilation to build the Chapel runtime ready to run code in the defined environment.  All of the environment variables follow a similar format as this environment variable `CHPL_TARGET_PLATFORM` that specifies the targeted platform, which if running on Linux could be `linux64`.  Now we list each environment variable and provide a short description of it.  Most of these are set automatically by the Chapel environment set-up script found at `$CHPL_HOME/util/setchplenv.bash` or the equivalent version for the type of shell you are using.

1. `CHPL_HOME`: Holds the absolute path to where the Chapel installation lives. Usually does not need to be set manually as it is set by the environment set-up script within Chapel. It must be set to allow the utilization of the `printchplenv` command that is useful for debugging.
2. `CHPL_TARGET_PLATFORM`: Specifies the platform or operating system Chapel is being compiled to run on (e.g., `linux64`, `darwin`). This variable is typically auto-detected but can be overridden when cross-compiling.
3. `CHPL_TARGET_COMPILER`: Determines which C compiler Chapel should use to compile generated C code (e.g., `gnu`, `llvm`). This affects both correctness and performance, especially in multi-locale settings.
4. `CHPL_TARGET_ARCH`: Indicates the target CPU architecture, such as `x86_64`, `arm`, or `native`. When set to `native`, Chapel attempts to optimize for the host's specific microarchitecture.
5. `CHPL_TARGET_CPU`: Provides fine-grained control over CPU-specific optimizations. Unlike `CHPL_TARGET_ARCH`, this may be set to microarchitecture families like `skylake`, `zen2`, or left as `none` to disable such tuning.
6. `CHPL_LOCALE_MODEL`: Defines how Chapel represents and maps computation locales. Common settings include `flat` and `numa`, which can affect data placement and affinity for performance tuning.
7. `CHPL_COMM`: Specifies the communication layer used for inter-locale communication (e.g., `none`, `gasnet`). Multi-locale executions require a communication layer like `gasnet` to coordinate distributed data structures.
8. `CHPL_COMM_SUBSTRATE`: Sets the specific network substrate used by GASNet (e.g., `udp`, `ibv`, `ofi`). This is critical when targeting high-performance networks like InfiniBand.
9. `CHPL_GASNET_SEGMENT`: Determines the memory segment model used by GASNet. Valid options include `fast`, `everything`, and `large`, which trade off memory registration and performance.
10. `CHPL_TASKS`: Chooses the tasking layer responsible for parallel task management (e.g., `qthreads` or `fifo`). This setting influences concurrency, scalability, and memory overhead.
11. `CHPL_LAUNCHER`: Specifies the method used to launch multi-locale executions. Options include system launchers like `slurm-gasnetrun_ibv` or simpler ones like `gasnetrun_ibv` depending on the deployment environment.
12. `CHPL_TIMERS`: Determines the timing mechanism used for performance measurements. The only current option is `generic`.
13. `CHPL_UNWIND`: Enables or disables support for stack unwinding in error handling. Typical values include `none` or `gdb`, and enabling unwinding can assist with debugging.
14. `CHPL_TARGET_MEM`: Sets the memory management strategy used by the runtime (e.g., `jemalloc`, `cstdlib`). This influences allocation performance and fragmentation in large-scale applications. **Previously named `CHPL_MEM`; that name is deprecated.**
15. `CHPL_HOST_MEM`: Sets the memory allocator used by the Chapel compiler itself during compilation (e.g., `mimalloc`, `cstdlib`). **On RHEL 9.x systems with strict memory overcommit (`vm.overcommit_memory=2`), this must be set to `mimalloc` before running `make`, otherwise the build crashes with `std::bad_alloc` during the resolve phase.**
16. `CHPL_ATOMICS`: Configures the implementation strategy for atomic operations (e.g., `cstdlib`, `locks`). The selection affects correctness and performance in concurrent code.
17. `CHPL_NETWORK_ATOMICS`: Specifies how atomic operations should be performed across locales, if at all (e.g., `none`, `native`, `portable`). Relevant primarily when using `CHPL_COMM = gasnet`.
18. `CHPL_GMP`: Selects whether to use the GNU Multiple Precision library and how it is linked (e.g., `bundled`, `none`, `system`). This is necessary for high-precision arithmetic in Chapel programs.
19. `CHPL_HWLOC`: Configures whether and how to use hwloc for querying system hardware topology (e.g., `bundled`, `system`, `none`). Useful for optimizing locality-aware computations.
20. `CHPL_RE2`: Controls the use of the RE2 regular expression library. Options include `bundled`, `none`, or `system`, and enabling it enhances regex performance and compatibility.
21. `CHPL_LLVM`: Specifies whether to use LLVM for Chapel's back-end code generation. When enabled (`bundled` or `system`), it allows Chapel to support features like LLVM-based optimizations and GPU codegen.
22. `CHPL_AUX_FILESYS`: Indicates support for auxiliary filesystem functionality, like interacting with Lustre or other non-POSIX systems. Defaults to `none`, but can be extended to optimize I/O on specialized systems.

### Recommended Chapel Settings on Wulver

The recommended settings for Chapel on the NJIT HPC system Wulver are below.  These settings must be set when building Chapel from source, which is the **recommended approach**.  Building from source lets you run the server interactively and monitor its output directly, which is essential for development and debugging.

To load the modules needed before building:

```bash
module load foss
module load CMake
module load Miniforge3
module load GLPK
```

> **Note:** Do not pin `foss` to a specific version (e.g. `foss/2023b`).  Loading `foss` without a version picks up the current default, which is `foss/2025a` at time of writing.  Older versions such as `foss/2023b` are also available but have not been tested with Chapel 2.7.0.

Then clone and build Chapel 2.7.0:

```bash
git clone https://github.com/chapel-lang/chapel.git ~/chapel-2.7.0
cd ~/chapel-2.7.0
git fetch --tags origin
git checkout tags/2.7.0 --force

export CHPL_HOME=~/chapel-2.7.0/
source $CHPL_HOME/util/setchplenv.bash

# Set these BEFORE running make:
export CHPL_GMP=bundled
export CHPL_HWLOC=bundled
export CHPL_RE2=bundled
export CHPL_LLVM=bundled
export CHPL_TARGET_CPU=native
export CHPL_TARGET_MEM=jemalloc
export CHPL_HOST_MEM=mimalloc        # required on Wulver RHEL 9.5

# Distributed-memory only — omit these for shared-memory builds:
export CHPL_COMM=gasnet
export CHPL_LAUNCHER=slurm-gasnetrun_ibv
export CHPL_COMM_SUBSTRATE=ibv
export CHPL_GASNET_SEGMENT=fast
export GASNET_MAX_SEGSIZE=64G
export GASNET_PHYSMEM_MAX=0.9
export CHPL_LAUNCHER_ACCOUNT=bader
export CHPL_LAUNCHER_PARTITION=general

make -j $(nproc)
```

#### Table: Recommended Environment Variable Values on Wulver
| Shared-Memory (Single Locale) Chapel         | Distributed-Memory (Multilocale) Chapel        |
|----------------------------------------------|------------------------------------------------|
| `CHPL_TARGET_PLATFORM`: linux64              | `CHPL_TARGET_PLATFORM`: linux64                |
| `CHPL_TARGET_COMPILER`: llvm                 | `CHPL_TARGET_COMPILER`: llvm                   |
| `CHPL_TARGET_ARCH`: x86_64                   | `CHPL_TARGET_ARCH`: x86_64                     |
| `CHPL_TARGET_CPU`: native                    | `CHPL_TARGET_CPU`: native                      |
| `CHPL_LOCALE_MODEL`: flat                    | `CHPL_LOCALE_MODEL`: flat                      |
| `CHPL_COMM`: none                            | `CHPL_COMM`: gasnet                            |
|                                              | `CHPL_COMM_SUBSTRATE`: ibv                     |
|                                              | `CHPL_GASNET_SEGMENT`: fast                    |
| `CHPL_TASKS`: qthreads                       | `CHPL_TASKS`: qthreads                         |
| `CHPL_LAUNCHER`: none                        | `CHPL_LAUNCHER`: slurm-gasnetrun_ibv           |
| `CHPL_TIMERS`: generic                       | `CHPL_TIMERS`: generic                         |
| `CHPL_UNWIND`: none                          | `CHPL_UNWIND`: none                            |
| `CHPL_TARGET_MEM`: jemalloc                  | `CHPL_TARGET_MEM`: jemalloc                    |
| `CHPL_HOST_MEM`: mimalloc *(Wulver only)*    | `CHPL_HOST_MEM`: mimalloc *(Wulver only)*      |
| `CHPL_ATOMICS`: cstdlib                      | `CHPL_ATOMICS`: cstdlib                        |
|                                              | `CHPL_NETWORK_ATOMICS`: none                   |
| `CHPL_GMP`: bundled                          | `CHPL_GMP`: bundled                            |
| `CHPL_HWLOC`: bundled                        | `CHPL_HWLOC`: bundled                          |
| `CHPL_RE2`: bundled                          | `CHPL_RE2`: bundled                            |
| `CHPL_LLVM`: bundled                         | `CHPL_LLVM`: bundled                           |
| `CHPL_AUX_FILESYS`: none                     | `CHPL_AUX_FILESYS`: none                       |

---

### Sourcing the Environment Script
Rather than setting variables manually each time, source the pre-made script from this repository.  Copy it to your HOME directory once so the path in the script resolves correctly:

```bash
cp ~/arkouda-njit/training/chpl_wulver_executor.sh ~/chpl_wulver_executor.sh
```

Then each new session:

```bash
# Distributed memory:
source ~/arkouda-njit/training/setDistributedMemoryArachneEnvironment_2.7.0

# Shared memory:
source ~/arkouda-njit/training/setSharedMemoryArachneEnvironment_2.7.0
```

### Arkouda

Setting up Arkouda requires you to clone the repository, check out the corresponding tagged version, and then create the conda environment from the dev environment file.

```bash
git clone https://github.com/Bears-R-Us/arkouda.git ~/arkouda
cd ~/arkouda
git fetch --tags origin
git checkout tags/v2026.02.27 --force

conda env create -f arkouda-env-dev.yml
conda activate arkouda-dev
pip install --no-cache-dir "setuptools==69.5.1"
```

> **Note:** Use `arkouda-env-dev.yml`, not `arkouda-env.yml`.  The dev file includes additional packages required by the build process.  Pinning `setuptools==69.5.1` is required; later versions break the build.

Once that completes, ensure Arkouda knows where your environment lives by creating the `Makefile.paths` file in your Arkouda directory:

```bash
echo '$(eval $(call add-path,'"$HOME"'/.conda/envs/arkouda-dev))' > ~/arkouda/Makefile.paths
```

### Other Dependencies
The external C/C++ libraries required are igraph 1.0.0, libleidenalg 0.12, and VieCut (via constrained-clustering 1.2.0).  GLPK must be loaded (`module load GLPK` on Wulver, or `apt install libglpk-dev` elsewhere) before building igraph, as igraph links against it.

Full build instructions for these are in the main `README.md`.  On Wulver, the `training/wulver_setup.sh` script handles all of this automatically.

## Building Arachne
At this point, only the Arkouda server with Arachne functionality needs to be compiled.  To do this, navigate to the `arkouda-njit` directory, source the igraph/leiden paths, and execute the module configuration script:

```bash
cd ~/arkouda-njit
source igraph_and_leiden_setup.sh
python module_configuration.py --ak_loc=~/arkouda/ --pkg_path=~/arkouda-njit/arachne/ | bash
```

**Note:** Use absolute paths (or `~/`) for both directories.  `igraph_and_leiden_setup.sh` must be sourced (not executed) because it exports `LD_LIBRARY_PATH` and `CPATH` into the current shell.

This script automatically generates the `chpl` command required to compile all necessary modules. The files `ServerModules.cfg` from both Arkouda and Arachne are read during this process to determine which modules to compile.

After building, install the Python packages in editable mode:

```bash
pip3 install -e ~/arkouda-njit/arachne/client/
pip3 install -e ~/arkouda/
```

### OpenSSL Fix (Wulver-specific)
On Wulver, conda-forge's `libcrypto.so.3` (version 3.6.x) is missing the `OPENSSL_3.0.1` versioned ABI symbol that EasyBuild's `libssl.so.3` requires.  The server will refuse to start with a `symbol lookup error` until you remove conda's copies and let the dynamic linker fall through to the system library:

```bash
rm -f ~/.conda/envs/arkouda-dev/lib/libcrypto.so.3
rm -f ~/.conda/envs/arkouda-dev/lib/libssl.so.3
rm -f ~/.conda/envs/arkouda-dev/lib/libcrypto.so
rm -f ~/.conda/envs/arkouda-dev/lib/libssl.so
```

This is a one-time fix that persists until the conda environment is rebuilt or updated.

## Running Arachne and Arkouda (and Other Chapel Programs)
Once the `arkouda_server` executable has been built, navigate to your Arkouda directory and run it.

**Shared memory (single node):**
```bash
cd ~/arkouda
source ~/arkouda-njit/training/setSharedMemoryArachneEnvironment_2.7.0
./arkouda_server
```

**Distributed memory (multi-node), from an interactive node:**
```bash
cd ~/arkouda
source ~/arkouda-njit/training/setDistributedMemoryArachneEnvironment_2.7.0
source ~/chpl_wulver_executor.sh
chpl_wulver_executor --filename=arkouda_server -nl 4 \
    --partition=general --qos=standard --time=2:00:00
```

This will launch a server instance with output similar to:

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

Then, in a new terminal (ideally another interactive session with fewer cores via `srun`), you can run a Python script to connect to this server.  Alternatively, you can start a Jupyter Notebook—either in VSCode or a web browser—that connects to the running Arkouda server.  The notebook just needs access to the `arkouda-dev` conda environment.

### Running in Multilocale Mode
For multilocale execution it is **recommended to use a self-built Chapel** built from source with the GASNet settings above.  Building from source lets you run the server interactively and monitor its output directly, which is essential for development and debugging.  The `chpl_wulver_executor` function (in `training/chpl_wulver_executor.sh`) is the standard way to launch on Wulver.  It uses Chapel's `--dry-run` flag to extract the `salloc` command that the Chapel launcher would normally execute, augments it with the correct Slurm parameters, and runs it interactively:

```bash
function chpl_wulver_executor() {
    local filename=""
    local nl=1
    local partition="general"
    local qos="standard"
    local time="24:00:00"
    local cpus=32

    while [[ $# -gt 0 ]]; do
        case "$1" in
            --filename=*) filename="${1#*=}"; shift ;;
            -nl)          nl="$2"; shift 2 ;;
            --partition=*) partition="${1#*=}"; shift ;;
            --qos=*)      qos="${1#*=}"; shift ;;
            --time=*)     time="${1#*=}"; shift ;;
            --cpus=*)     cpus="${1#*=}"; shift ;;
            *) echo "Unknown option: $1"; shift ;;
        esac
    done

    if [ -z "$filename" ]; then echo "Error: --filename is required"; return 1; fi

    local cmd_output
    cmd_output=$("./$filename" -nl "$nl" --dry-run)
    local modified_cmd
    modified_cmd=$(echo "$cmd_output" | sed \
        "s/--account=${CHPL_LAUNCHER_ACCOUNT}/--account=${CHPL_LAUNCHER_ACCOUNT} --partition=$partition --qos=$qos --time=$time --cpus-per-task=$cpus/")

    echo "Executing: $modified_cmd"
    export CHPL_RT_NUM_THREADS_PER_LOCALE=$cpus
    eval "$modified_cmd --memTrack --memLeaks"
}
```

Everything mentioned here about running in interactive mode is **only** intended for debugging and development purposes.  For benchmarking, you should launch both the Arkouda server and your Python script using an `sbatch` file.

### Running Benchmarks
To be completed.

## Testing Framework via PyTest
The Arachne testing harness is built on **PyTest**.  Only the Python API needs to be tested because all Chapel code is invoked through it. If the Python interface works, then the underlying Chapel code is also assumed correct.  Tests are located in the directory `arkouda-njit/arachne/tests`.

There **must** be a running Arkouda server before you execute the tests.  To run the tests, navigate to `arkouda-njit/arachne/` and execute:

```bash
pytest --server-host=hostname --server-port=port
```

Tests should always yield deterministic results.  For algorithms involving randomness, use a fixed seed and a simple input that guarantees predictable output.

## Repository Set-Up

```text
arachne/
    |-- benchmarks/            # (Possibly outdated) benchmarking scripts.
    |-- client/                # Python API for Arachne.
        |-- arachne/
            |-- __init__.py
            |-- digraphclass.py
            |-- generators.py
            |-- graphclass.py
            |-- methods.py
            |-- propgraphclass.py
        |-- README.md
        |-- setup.py
    |-- data/                  # Sample input data for testing.
        |-- wcc/
            |-- test_clustering_simple_1.tsv
            |-- test_clustering.tsv
            |-- test_network_simple_1.tsv
            |-- test_network.tsv
        |-- karate.mtx
    |-- examples/              # (Possibly outdated) example notebooks and scripts.
    |-- output/                # Default location for Arachne output (not git-tracked).
        |-- README.md
    |-- server/                # All the source code for Arachne.
        |-- external_libs/     # Any external libraries are cloned here.
            |-- README.md
        |-- viecut_helpers/    # Helper C/C++ functions for calling VieCut.
            |-- compileLogger.sh
            |-- computeMinCut.cpp
            |-- computeMinCut.h
        |-- leiden_helpers/    # Helper C/C++ functions for calling Leiden.
            |-- computeLeiden.cpp
            |-- computeLeiden.h
        |-- Aggregators.chpl
        |-- BreadthFirstSearch.chpl
        |-- BreadthFirstSearchMsg.chpl
        |-- BuildGraph.chpl
        |-- BuildGraphMsg.chpl
        |-- BuildPropertyGraph.chpl
        |-- BuildPropertyGraphMsg.chpl
        |-- ConnectedComponents.chpl
        |-- ConnectedComponentsMsg.chpl
        |-- Diameter.chpl
        |-- DiameterMsg.chpl
        |-- GraphArray.chpl
        |-- GraphInfoMsg.chpl
        |-- ServerModules.cfg
        |-- SquareCount.chpl
        |-- SquareCountMsg.chpl
        |-- SubgraphSearch.chpl
        |-- SubgraphSearchMsg.chpl
        |-- TriangleCentrality.chpl
        |-- TriangleCentralityMsg.chpl
        |-- TriangleCount.chpl
        |-- TriangleCountMsg.chpl
        |-- TrussMsg.chpl
        |-- Utils.chpl
        |-- WellConnectedness.chpl
        |-- WellConnectednessMsg.chpl
    |-- tests/                 # PyTest test scripts.
        |-- algorithm_test.py
        |-- base_test.py
        |-- class_test.py
        |-- conftest.py
        |-- deterministic_generators_test.py
        |-- prop_graph_test.py
        |-- random_generators_test.py
    |-- pytest.ini
    |-- README.md
arachne_development/           # Deprecated/older versions of Arachne functionality.
.gitignore
LICENSE
module_configuration.py
README.md
```