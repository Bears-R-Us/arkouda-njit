#!/bin/bash
# wulver_setup_distributed.sh — Full automated setup of Arkouda + Arachne on Wulver HPC
#
# PREREQUISITES:
#   Run this script from an interactive compute node with sufficient memory:
#     srun -p general -N 1 -n 1 --cpus-per-task=32 --qos=standard \
#          --account=bader --time=4:00:00 --mem=128G --exclusive --pty bash
#
# USAGE:
#   source training/wulver_setup_distributed.sh          # run all phases
#   source training/wulver_setup_distributed.sh --help   # show options
#
# Flags to skip phases already completed:
#   --skip-chapel      Skip Chapel clone and build
#   --skip-arkouda     Skip Arkouda clone
#   --skip-conda       Skip conda env creation
#   --skip-njit        Skip arkouda-njit clone
#   --skip-deps        Skip external library builds (constrained-clustering, igraph, leiden)
#   --skip-server      Skip arkouda_server compilation
#   --skip-openssl     Skip conda OpenSSL removal

set -e

# Configuration
CHAPEL_VERSION="2.7.0"
ARKOUDA_VERSION="v2026.02.27"
NJIT_BRANCH="cm"
CONDA_ENV="arkouda-dev"

CHPL_DIR="$HOME/chapel-${CHAPEL_VERSION}"
AK_DIR="$HOME/arkouda"
NJIT_DIR="$HOME/arkouda-njit"

SLURM_ACCOUNT="bader"
SLURM_PARTITION="general"
BUILD_JOBS=$(nproc)

# Argument parsing
SKIP_CHAPEL=false
SKIP_ARKOUDA=false
SKIP_CONDA=false
SKIP_NJIT=false
SKIP_DEPS=false
SKIP_SERVER=false
SKIP_OPENSSL=false

for arg in "$@"; do
    case $arg in
        --skip-chapel)   SKIP_CHAPEL=true ;;
        --skip-arkouda)  SKIP_ARKOUDA=true ;;
        --skip-conda)    SKIP_CONDA=true ;;
        --skip-njit)     SKIP_NJIT=true ;;
        --skip-deps)     SKIP_DEPS=true ;;
        --skip-server)   SKIP_SERVER=true ;;
        --skip-openssl)  SKIP_OPENSSL=true ;;
        --help)
            echo "Usage: source wulver_setup.sh [--skip-chapel] [--skip-arkouda]"
            echo "       [--skip-conda] [--skip-njit] [--skip-deps]"
            echo "       [--skip-server] [--skip-openssl]"
            return 0 2>/dev/null || exit 0
            ;;
    esac
done

# Helpers
info()  { echo "[INFO]  $*"; }
phase() { echo; echo ""---------------""; echo "  $*"; echo ""---------------""; }

# Phase 0: Load modules
phase "Loading Wulver modules"
module load foss
module load CMake
module load Miniforge3
module load GLPK
info "Modules loaded."

# Phase 1: Chapel
if [ "$SKIP_CHAPEL" = false ]; then
    phase "Building Chapel ${CHAPEL_VERSION}"

    if [ -d "$CHPL_DIR" ]; then
        info "Chapel directory already exists at $CHPL_DIR — skipping clone."
    else
        cd "$HOME"
        git clone https://github.com/chapel-lang/chapel.git "chapel-${CHAPEL_VERSION}"
        cd "chapel-${CHAPEL_VERSION}"
        git fetch --tags origin
        git checkout "tags/${CHAPEL_VERSION}" --force
    fi

    cd "$CHPL_DIR"
    source ./util/setchplenv.bash
    export CHPL_GMP=bundled
    export CHPL_HWLOC=bundled
    export CHPL_RE2=bundled
    export CHPL_LLVM=bundled
    export CHPL_COMM=gasnet
    export CHPL_LAUNCHER=slurm-gasnetrun_ibv
    export CHPL_COMM_SUBSTRATE=ibv
    export CHPL_GASNET_SEGMENT=fast
    export GASNET_MAX_SEGSIZE=64G
    export CHPL_TARGET_CPU=native
    export GASNET_PHYSMEM_MAX=0.9
    export CHPL_TARGET_MEM=jemalloc
    # Must be set before make to avoid std::bad_alloc in resolve phase on RHEL 9.5
    export CHPL_HOST_MEM=mimalloc
    export CHPL_LAUNCHER_ACCOUNT="$SLURM_ACCOUNT"
    export CHPL_LAUNCHER_PARTITION="$SLURM_PARTITION"

    info "Building Chapel with $BUILD_JOBS jobs. This takes 30–60 minutes."
    make -j "$BUILD_JOBS"
    info "Chapel build complete."
else
    info "Skipping Chapel build."
    # Still need to set env vars for later phases
    cd "$CHPL_DIR"
    source ./util/setchplenv.bash
    export CHPL_GMP=bundled CHPL_HWLOC=bundled CHPL_RE2=bundled CHPL_LLVM=bundled
    export CHPL_COMM=gasnet CHPL_LAUNCHER=slurm-gasnetrun_ibv
    export CHPL_COMM_SUBSTRATE=ibv CHPL_GASNET_SEGMENT=fast
    export GASNET_MAX_SEGSIZE=64G CHPL_TARGET_CPU=native
    export GASNET_PHYSMEM_MAX=0.9 CHPL_TARGET_MEM=jemalloc
    export CHPL_HOST_MEM=mimalloc
    export CHPL_LAUNCHER_ACCOUNT="$SLURM_ACCOUNT"
    export CHPL_LAUNCHER_PARTITION="$SLURM_PARTITION"
fi

cd "$HOME"

# Phase 2: Arkouda
if [ "$SKIP_ARKOUDA" = false ]; then
    phase "Cloning Arkouda ${ARKOUDA_VERSION}"

    if [ -d "$AK_DIR" ]; then
        info "Arkouda directory already exists at $AK_DIR — skipping clone."
    else
        git clone https://github.com/Bears-R-Us/arkouda.git "$AK_DIR"
        cd "$AK_DIR"
        git fetch --tags origin
        git checkout "tags/${ARKOUDA_VERSION}" --force
    fi
    info "Arkouda ready."
else
    info "Skipping Arkouda clone."
fi

cd "$HOME"

# Phase 3: Conda environment
if [ "$SKIP_CONDA" = false ]; then
    phase "Creating conda environment '${CONDA_ENV}'"

    if conda env list | grep -q "^${CONDA_ENV} "; then
        info "Conda env '${CONDA_ENV}' already exists."
    else
        conda env create -f "$AK_DIR/arkouda-env-dev.yml"
    fi

    conda activate "$CONDA_ENV"
    # Pin setuptools to version known to work with this arkouda build
    pip install --no-cache-dir "setuptools==69.5.1"
    info "Conda env ready."
else
    info "Skipping conda env creation."
    conda activate "$CONDA_ENV"
fi

export CPATH="$CPATH:$HOME/.conda/envs/${CONDA_ENV}/include"
export LD_LIBRARY_PATH="$LD_LIBRARY_PATH:$HOME/.conda/envs/${CONDA_ENV}/lib"
export CHPL_RT_CALL_STACK_SIZE=64M

# Phase 4: Makefile.paths
phase "Writing Arkouda Makefile.paths"
printf '$(eval $(call add-path,%s/.conda/envs/%s))\n' "$HOME" "$CONDA_ENV" \
    > "$AK_DIR/Makefile.paths"
info "Makefile.paths written: $(cat "$AK_DIR/Makefile.paths")"

# Phase 5: arkouda-njit
if [ "$SKIP_NJIT" = false ]; then
    phase "Cloning arkouda-njit (branch: ${NJIT_BRANCH})"

    if [ -d "$NJIT_DIR" ]; then
        info "arkouda-njit already exists at $NJIT_DIR — skipping clone."
    else
        git clone https://github.com/Bears-R-Us/arkouda-njit.git "$NJIT_DIR"
        cd "$NJIT_DIR"
        git checkout "$NJIT_BRANCH"
    fi
    info "arkouda-njit ready."
else
    info "Skipping arkouda-njit clone."
fi

# Phase 6: External libraries
if [ "$SKIP_DEPS" = false ]; then
    phase "Building external dependencies"

    EXT="$NJIT_DIR/arachne/server/external_libs"

    # ── constrained-clustering ──
    info "Setting up constrained-clustering..."
    cd "$EXT"
    if [ ! -d "constrained-clustering" ]; then
        git clone https://github.com/MinhyukPark/constrained-clustering.git
    fi
    cd constrained-clustering

    # Patch setup.sh: pin igraph to 1.0.0 and libleidenalg to 0.12
    # (default checkout versions are incompatible with current cmake configs)
    sed -i 's/git checkout tags\/igraph-[0-9.]* --force/git checkout tags\/1.0.0 --force/' setup.sh
    sed -i '/libleidenalg/{s/git checkout tags\/[0-9.]* --force/git checkout tags\/0.12 --force/}' setup.sh
    # Fallback: ensure any igraph checkout line targets 1.0.0
    sed -i '/igraph/{/git checkout/s/tags\/[^ ]*/tags\/1.0.0/}' setup.sh

    # Patch CMakeLists.txt: update find_package version requirements
    sed -i 's/find_package(igraph [0-9.]* CONFIG REQUIRED)/find_package(igraph 1.0.0 CONFIG REQUIRED)/' CMakeLists.txt
    sed -i 's/find_package(libleidenalg [0-9.]* CONFIG REQUIRED)/find_package(libleidenalg 0.12 CONFIG REQUIRED)/' CMakeLists.txt
    # Add lib64/cmake to CMAKE_PREFIX_PATH so cmake finds libleidenalg
    if ! grep -q 'lib64/cmake' CMakeLists.txt; then
        sed -i 's|set(CMAKE_PREFIX_PATH.*external_libs/lib/cmake.*)|set(CMAKE_PREFIX_PATH "${CMAKE_PREFIX_PATH};${CMAKE_CURRENT_SOURCE_DIR}/external_libs/lib/cmake;${CMAKE_CURRENT_SOURCE_DIR}/external_libs/lib64/cmake")|' CMakeLists.txt
    fi

    info "Running setup.sh for constrained-clustering..."
    ./setup.sh

    # Fix cmake version file: libleidenalg reports 0.11.x but binary is 0.12
    LEIDEN_VER_FILE=$(find "$EXT/constrained-clustering/external_libs" \
        -name "libleidenalgConfigVersion.cmake" 2>/dev/null | head -1)
    if [ -n "$LEIDEN_VER_FILE" ]; then
        sed -i 's/set(PACKAGE_VERSION "[0-9.]*")/set(PACKAGE_VERSION "0.12")/' "$LEIDEN_VER_FILE"
        info "Patched $LEIDEN_VER_FILE to version 0.12."
    fi

    info "Running easy_build_and_compile.sh..."
    ./easy_build_and_compile.sh

    # ── viecut_helpers ──
    info "Compiling viecut_helpers..."
    cd "$NJIT_DIR/arachne/server/viecut_helpers"
    source compileLogger.sh -f logger.cpp -o logger.cpp.o
    gcc -c -fPIC \
        -I"$EXT/constrained-clustering/external_libs/VieCut/lib/" \
        -I"$EXT/constrained-clustering/external_libs/VieCut/extlib/tlx/" \
        computeMinCut.cpp -o computeMinCut.o

    # ── igraph + libleidenalg (for Leiden community detection) ──
    info "Building igraph and libleidenalg via igraph_and_leiden_setup.sh..."
    cd "$NJIT_DIR"
    source igraph_and_leiden_setup.sh

    info "External dependencies built."
else
    info "Skipping external dependency builds."
    # Still need igraph paths for server build
    cd "$NJIT_DIR"
    source igraph_and_leiden_setup.sh
fi

# Phase 7: Build arkouda_server 
if [ "$SKIP_SERVER" = false ]; then
    phase "Building arkouda_server"
    cd "$NJIT_DIR"
    python module_configuration.py \
        --ak_loc="$AK_DIR/" \
        --pkg_path="$NJIT_DIR/arachne/" | bash
    info "arkouda_server built."
else
    info "Skipping arkouda_server build."
fi

# Phase 8: Python packages 
phase "Installing Python packages (editable mode)"
pip3 install -e "$NJIT_DIR/arachne/client/"
pip3 install -e "$AK_DIR/"
info "Python packages installed."

# Phase 9: Fix OpenSSL conflict
if [ "$SKIP_OPENSSL" = false ]; then
    phase "Fixing OpenSSL library conflict"
    # conda-forge's libcrypto.so.3 (3.6.x) skips the OPENSSL_3.0.1 versioned
    # ABI symbol that EasyBuild's libssl.so.3 requires. Removing conda's copies
    # lets the dynamic linker fall through to the system (EasyBuild) OpenSSL.
    CONDA_LIB="$HOME/.conda/envs/${CONDA_ENV}/lib"
    for f in libcrypto.so.3 libssl.so.3 libcrypto.so libssl.so; do
        [ -f "$CONDA_LIB/$f" ] && rm -f "$CONDA_LIB/$f" && info "Removed $CONDA_LIB/$f"
    done
    info "OpenSSL conflict resolved."
else
    info "Skipping OpenSSL fix."
fi

# Done 
phase "Setup complete"
echo ""
echo "To start the server (distributed, multi-node):"
echo "  cd $AK_DIR"
echo "  source $NJIT_DIR/training/setDistributedMemoryArachneEnvironment_2.7.0"
echo "  source $NJIT_DIR/training/chpl_wulver_executor.sh"
echo "  chpl_wulver_executor --filename=arkouda_server -nl 4 \\"
echo "      --partition=general --qos=standard --time=2:00:00"
echo ""
echo "To start the server (shared memory, single node):"
echo "  cd $AK_DIR"
echo "  source $NJIT_DIR/training/setSharedMemoryArachneEnvironment_2.7.0"
echo "  ./arkouda_server"
echo ""