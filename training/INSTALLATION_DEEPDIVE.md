# Introduction
[Arachne](https://github.com/Bears-R-Us/arkouda-njit) is a scalable framework for exploratory graph analytics tailored to Python data scientists.  It builds on [Arkouda](https://github.com/Bears-R-Us/arkouda), a parallel and distributed array-processing library designed to support array and dataframe-like computations at scale.  
While Arkouda offers functionality analogous to [NumPy](https://numpy.org) and [Pandas](https://pandas.pydata.org), Arachne extends this model to graph analytics with an interface similar to [NetworkX](https://networkx.org).  This guide serves both new and existing developers, providing insight into the design rationale and internal structure of the codebase.  It includes detailed instructions for environment setup, code compilation, and running unit tests using [PyTest](https://pytest.org).  This document is a verbose version of the Arachne installation steps found on [GitHub](https://github.com/Bears-R-Us/arkouda-njit).

# Setting Up Prerequisites
In general, the prerequisite setup process should be straightforward for users familiar with installing software on Linux systems.  To install the required dependencies listed below, you may use your distribution’s package manager (e.g., `apt`, `yum`, `pacman`), or load the packages via environment modules if working on a high-performance computing (HPC) cluster.  At the time of writing, the following versions were confirmed to work:

1. [GCC](https://gcc.gnu.org) 11.2.0 or later  
2. [CMake](https://cmake.org) 3.26.3  
3. [OpenMPI](https://www.open-mpi.org) (GNU) 4.1.4  
4. [Anaconda](https://www.anaconda.com) 2023.09-0  
5. [jq](https://stedolan.github.io/jq) 1.6, a command-line JSON processor

These prerequisites are common for software built from source.  [GCC](https://gcc.gnu.org) provides compilers for C and C++ code.  [CMake](https://cmake.org) is a build system generator that facilitates the compilation process.  [OpenMPI](https://www.open-mpi.org) is used by CMake to enable parallel compilation tasks.  [Anaconda](https://www.anaconda.com) serves as the Python environment manager and also installs key dependencies for Arachne and Arkouda, including [ZeroMQ](https://zeromq.org).  Finally, [jq](https://stedolan.github.io/jq) is employed during the build process of the [VieCut](https://github.com/VieCut/VieCut) library to construct a logging component required by Arachne’s well-connectedness routines.

## Setting Up Your Terminals
It is recommended to launch an interactive terminal with `srun` during the installation process on Wulver as the login nodes have very limited resources.  There is also a script available at `/project/bader/fl28` to run the installation process automatically.  However, it is recommended to do it manually for developers to get used to all the steps of setting up Arkouda and Arachne to be able to help with debugging user installations.  To launch an interactive terminal you can use the following command:

```bash
srun -p general -N 1 -n 1 --cpus-per-task=16 --qos=standard --account=bader --time=2:00:00 --exclusive --pty bash
```

## Installing Chapel
Both Arkouda and Arachne are primarily implemented in the [Chapel](https://chapel-lang.org) programming language, with supplemental functionality written in C and C++ as needed.  Chapel supports two primary build configurations: with and without inter-locale communication.  A *locale* in Chapel represents a computational unit—typically a compute node with its own memory and processing cores—used to enable parallel and distributed execution.

Currently, most algorithms in Arachne achieve the best performance when compiled in shared-memory mode (i.e., without communication across locales).  However, several key routines—including breadth-first search, graph attribute queries, and well-connected components—have distributed-memory implementations optimized for multi-locale execution.  While all Arachne functionality can technically be run in multi-locale mode, performance may degrade compared to single-locale execution due to the added communication overhead inherent in distributed systems.

The Chapel environment is primarily defined by a system of environment variables that must be set before compilation to build the Chapel runtime ready to run code in the defined environment.  All of the environment variables follow a similar format as this environment variable `CHPL_TARGET_PLATFORM` that specifies the targeted platform, which if running on Linux could be `linux64`.  Now we list each environment variable and provide a short description of it.  Most of these are set automatically by the Chapel environment set-up script found at `$CHPL_HOME/util/setchplenv.bash` or the equivalent version for the type of shell you are using.

1. `CHPL_HOME`: Holds the absolute path to where the Chapel installation lives. Usually does not need to be set manually as it is set by the environment set-up script within Chapel. It must be set to allow the utilization of the `printchplenv` command that is useful for debugging.
2. `CHPL_TARGET_PLATFORM`: Specifies the platform or operating system Chapel is being compiled to run on (e.g., `linux64`, `darwin`). This variable is typically auto-detected but can be overridden when cross-compiling.
3. `CHPL_TARGET_COMPILER`: Determines which C compiler Chapel should use to compile generated C code (e.g., `gnu`, `llvm`). This affects both correctness and performance, especially in multi-locale settings.
4. `CHPL_TARGET_ARCH`: Indicates the target CPU architecture, such as `x86_64`, `arm`, or `native`. When set to `native`, Chapel attempts to optimize for the host’s specific microarchitecture.
5. `CHPL_TARGET_CPU`: Provides fine-grained control over CPU-specific optimizations. Unlike `CHPL_TARGET_ARCH`, this may be set to microarchitecture families like `skylake`, `zen2`, or left as `none` to disable such tuning.
6. `CHPL_LOCALE_MODEL`: Defines how Chapel represents and maps computation locales. Common settings include `flat` and `numa`, which can affect data placement and affinity for performance tuning.
7. `CHPL_COMM`: Specifies the communication layer used for inter-locale communication (e.g., `none`, `gasnet`). Multi-locale executions require a communication layer like `gasnet` to coordinate distributed data structures.
8. `CHPL_COMM_SUBSTRATE`: Sets the specific network substrate used by GASNet (e.g., `udp`, `ibv`, `ofi`). This is critical when targeting high-performance networks like InfiniBand.
9. `CHPL_GASNET_SEGMENT`: Determines the memory segment model used by GASNet. Valid options include `fast`, `everything`, and `large`, which trade off memory registration and performance.
10. `CHPL_TASKS`: Chooses the tasking layer responsible for parallel task management (e.g., `qthreads` or `fifo`). This setting influences concurrency, scalability, and memory overhead.
11. `CHPL_LAUNCHER`: Specifies the method used to launch multi-locale executions. Options include system launchers like `slurm-gasnetrun_ibv` or simpler ones like `gasnetrun_ibv` depending on the deployment environment.
12. `CHPL_TIMERS`: Determines the timing mechanism used for performance measurements. The only current option is `generic`.
13. `CHPL_UNWIND`: Enables or disables support for stack unwinding in error handling. Typical values include `none` or `gdb`, and enabling unwinding can assist with debugging.
14. `CHPL_TARGET_MEM`: Sets the memory management strategy used by the runtime (e.g., `jemalloc`, `cstdlib`). This influences allocation performance and fragmentation in large-scale applications. **Used to be named `CHPL_MEM` but that name has been deprecated.**
15. `CHPL_ATOMICS`: Configures the implementation strategy for atomic operations (e.g., `cstdlib`, `locks`). The selection affects correctness and performance in concurrent code.
16. `CHPL_NETWORK_ATOMICS`: Specifies how atomic operations should be performed across locales, if at all (e.g., `none`, `native`, `portable`). Relevant primarily when using `CHPL_COMM = gasnet`.
17. `CHPL_GMP`: Selects whether to use the GNU Multiple Precision library and how it is linked (e.g., `bundled`, `none`, `system`). This is necessary for high-precision arithmetic in Chapel programs.
18. `CHPL_HWLOC`: Configures whether and how to use hwloc for querying system hardware topology (e.g., `bundled`, `system`, `none`). Useful for optimizing locality-aware computations.
19. `CHPL_RE2`: Controls the use of the RE2 regular expression library. Options include `bundled`, `none`, or `system`, and enabling it enhances regex performance and compatibility.
20. `CHPL_LLVM`: Specifies whether to use LLVM for Chapel's back-end code generation. When enabled (`bundled` or `system`), it allows Chapel to support features like LLVM-based optimizations and GPU codegen.
21. `CHPL_AUX_FILESYS`: Indicates support for auxiliary filesystem functionality, like interacting with Lustre or other non-POSIX systems. Defaults to `none`, but can be extended to optimize I/O on specialized systems.

### Recommended Chapel Settings on Wulver

The recommended settings for Chapel on the NJIT HPC system Wulver are below.  These settings must be set when building your own Chapel from source.  There is an updated Chapel module available on Wulver that can be loaded with:

```bash
module load wulver
module load foss/2023b Chapel/2.3.0
```

If you go this route, loading the modules will automatically set these environment variables.  However, this approach requires the research group to coordinate with Wulver administrators to install new Chapel versions as they are released (roughly every three months).  Running multilocale Chapel programs—including the Arachne and Arkouda `arkouda_server` executable—using either the Wulver module or a custom Chapel build requires specialized `sbatch` submission scripts or the `chpl_wulver_executor` function described later in this document.

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
| `CHPL_MEM`: jemalloc                         | `CHPL_MEM`: jemalloc                           |
| `CHPL_ATOMICS`: cstdlib                      | `CHPL_ATOMICS`: cstdlib                        |
|                                              | `CHPL_NETWORK_ATOMICS`: none                   |
| `CHPL_GMP`: bundled                          | `CHPL_GMP`: bundled                            |
| `CHPL_HWLOC`: bundled                        | `CHPL_HWLOC`: bundled                          |
| `CHPL_RE2`: bundled                          | `CHPL_RE2`: bundled                            |
| `CHPL_LLVM`: bundled                         | `CHPL_LLVM`: bundled                           |
| `CHPL_AUX_FILESYS`: none                     | `CHPL_AUX_FILESYS`: none                       |

---

### Building Chapel from Source
To build Chapel manually:
1. Navigate to your `$CHPL_HOME` directory.
2. Compile Chapel using:
   ```bash
   make -j p
   ```
   Replace `p` with the number of processors available to accelerate the build.
3. After compilation, install the Python bindings needed by Arkouda:
   ```bash
   make chapel-py-venv
   ```
If you are using the Wulver modules, you do **not** need to build Chapel or install any bindings manually. However, for developing purposes it is recommended to build your own Chapel from source.
### Arkouda

Setting up Arkouda requires you to clone the repository, check out the corresponding tagged version, and then load the dependencies with Anaconda.  Loading in the dependencies can be done automatically by running:

```bash
conda env create -f arkouda-env.yml
```

Once that completes, ensure Arkouda knows where your environment lives by creating and/or editing the `Makefile.paths` file and adding the path to your Anaconda environment directory.

### Other Dependencies
Other dependencies that need to be built include VieCut, iGraph, and Leiden.  These can be installed by following the steps on their respective GitHub repositories.

## Building Arachne
At this point, only the Arkouda server with Arachne functionality needs to be compiled.  To do this, navigate to the `arkouda-njit` directory and execute the module configuration script:

```bash
python module_configuration.py --ak_loc=/path/to/arkouda/ --pkg_path=/path/to/arkouda-njit/arachne/
```

**Note:** Make sure you are using absolute paths for both directories.

This script automatically generates the `chpl` command required to compile all necessary modules. The files `ServerModules.cfg` from both Arkouda and Arachne are read during this process to determine which modules to compile.

## Running Arachne and Arkouda (and Other Chapel Programs)
Once the `arkouda_server` executable has been built, you can run it.  
If you are in single-locale mode and have allocated an interactive session using `srun`, navigate to the `arkouda-njit` directory and run:

```bash
../arkouda/arkouda_server
```

This will launch a server instance with output similar to:

```
********************************************************************************************************
********************************************************************************************************
*                                                                                                      *
*                          server listening on tcp://n118.cluster.local:5555                           *
*                                 arkouda server version = v2025.01.13                                 *
*                                    built with chapel version2.4.0                                    *
*                                     memory limit = 973796998348                                      *
*                                       bytes of memory used = 0                                       *
*                                                                                                      *
********************************************************************************************************
********************************************************************************************************
```

Then, in a new terminal (ideally another interactive session with fewer cores via `srun`), you can run a Python script to connect to this server.  Alternatively, you can start a Jupyter Notebook—either in VSCode or a web browser—that connects to the running Arkouda server.  The notebook just needs access to the Arkouda Anaconda environment.

### Running in Multilocale Mode
For multilocale execution, it is **recommended to use a self-built Chapel** instead of the Chapel module provided by Wulver. The Wulver Chapel module requires running via `sbatch`, which can make debugging difficult. Using your own Chapel build allows you to interactively monitor the Arkouda server’s output. The best way to run multilocale Arachne and Arkouda is to use the wrapper method below that interactively launches the Arkouda server.

```bash
function chpl_wulver_executor() {
    local filename=""
    local nl=1
    local qos="standard" 
    local time="24:00:00"
    
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --filename=*)
                filename="${1#*=}"
                shift
                ;;
            -nl)
                if [[ $# -gt 1 ]]; then
                    nl="$2"
                    shift 2
                else
                    echo "Error: -nl requires a value"
                    return 1
                fi
                ;;
            --qos=*)
                qos="${1#*=}"
                shift
                ;;
            --time=*)
                time="${1#*=}"
                shift
                ;;
            *)
                echo "Unknown option: $1"
                shift
                ;;
        esac
    done

    if [ -z "$filename" ]; then
        echo "Error: --filename is required"
        return 1
    fi

    local cmd_output=$("$filename" -nl "$nl" --dry-run)
    local modified_cmd=$(echo "$cmd_output" | sed "s/--account=bader/--account=bader --qos=$qos --time=$time/")
    echo "Executing: $modified_cmd"
    eval "$modified_cmd"
}
```
The function utilizes the Chapel command-line argument `--dry-run` to extract the actual command that the Chapel launcher would execute (typically an interactive `salloc`), and it then augments that command to align with Wulver's Slurm configuration.  Everything mentioned here about running in interactive mode is **only** intended for debugging and development purposes.  For benchmarking, you should launch both the Arkouda server and your Python script using an `sbatch` file.  More on this later.

### Running Benchmarks
To be completed.

## Testing Framework via PyTest
The Arachne testing harness is built on **PyTest**.  Only the Python API needs to be tested because all Chapel code is invoked through it. If the Python interface works, then the underlying Chapel code is also assumed correct.  Tests are located in the dirctory `arkouda-njit/arachne/tests`.

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
    |-- examples/              # (Possible outdated) example notebooks and scripts.
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
