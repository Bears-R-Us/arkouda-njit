#!/bin/bash
#SBATCH --job-name=rmat
#SBATCH --output=output/%x_%j.out
#SBATCH --error=output/%x_%j.err
#SBATCH --partition=general
#SBATCH --qos=standard
#SBATCH --account=bader
#SBATCH --nodes=2
#SBATCH --ntasks-per-node=1
#SBATCH --exclusive
#SBATCH --time=8:00:00

# ---- Input Arguments ----
ARKOUDA_SERVER_PATH=$1     # e.g. /path/to/arkouda_server or ./arkouda_server
PORT=$2                    # e.g. 5555
SCALE=$3                   # e.g. 20
TRIALS=$4                  # e.g. 5
ALGO_FLAG=$5               # e.g. --run_bfs, --run_cc, etc.

if [[ $# -ne 5 ]]; then
    echo "Usage: sbatch rmat.sh <arkouda_server_path> <port> <scale> <trials> <algorithm_flag>"
    echo "Example: sbatch rmat.sh ./arkouda_server 5555 20 5 --run_bfs"
    exit 1
fi

# Extract algorithm name from flag, e.g., "--run_bfs" --> "bfs"
ALGO_NAME=$(echo "$ALGO_FLAG" | sed 's/^--run_//')

# Define log filenames
SERVER_LOG="../output/server_${ALGO_NAME}_scale${SCALE}_trials${TRIALS}.log"
CLIENT_LOG="../output/client_${ALGO_NAME}_scale${SCALE}_trials${TRIALS}.log"

# ---- Load Required Modules ----
source /home/oaa9/setSharedMemoryArachneEnvironment
cd /home/oaa9/arkouda-njit/
source /home/oaa9/arkouda-njit/igraph_and_leiden_setup.sh
cd /home/oaa9/arkouda-njit/arachne/benchmarks/scripts/

# ---- Get Hostnames of Allocated Nodes ----
hostfile=$(generate_pbs_nodefile 2>/dev/null || echo "$SLURM_JOB_NODELIST")
nodes=($(scontrol show hostnames $hostfile))
server_node=${nodes[0]}
client_node=${nodes[1]}

echo "Server node: $server_node"
echo "Client node: $client_node"

# ---- Launch Arkouda Server on First Node ----
echo "Launching Arkouda server..."
srun --nodes=1 --nodelist=$server_node --ntasks=1 --exclusive \
    $ARKOUDA_SERVER_PATH --ServerPort=$PORT > $SERVER_LOG 2>&1 &

# Give Arkouda a moment to start
sleep 5

# ---- Run Python Benchmark Script on Second Node ----
echo "Running Python benchmark script..."
SCRIPT_NAME="../rmat.py"

srun --nodes=1 --nodelist=$client_node --ntasks=1 \
    python $SCRIPT_NAME $server_node $PORT --scale $SCALE --trials $TRIALS $ALGO_FLAG \
    > $CLIENT_LOG 2>&1

# ---- Cleanup ----
wait
