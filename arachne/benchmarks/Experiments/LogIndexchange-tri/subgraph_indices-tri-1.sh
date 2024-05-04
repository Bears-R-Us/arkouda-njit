#!/bin/bash

#SBATCH -N 2                  # Number of nodes
#SBATCH --ntasks-per-node=1   # Number of tasks per node
#SBATCH --array=0-7           # Job array range

# Load modules
module load cmake
module load gcc
module load chapel/1.32.0
module load anaconda3
eval "$(conda shell.bash hook)"
conda activate arkouda-dev

# Configurations for each array job
PROB_ARRAY=(0.0005 0.0005 0.005 0.05 0.05 0.05 0.5 1)
NODES_ARRAY=(100000 50000 15000 500 1000 1400 150 75)

# Define directories and files
ARKOUDA_DIR=/scratch/users/md724/arkouda-2023.11.15
BENCHMARKS_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/Experiments/LogIndexchange-tri/
PYTHON_SCRIPT=subgraph_indices-tri-1.py
SERVER_PORT=5555
LOG_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/Experiments/LogIndexchange-tri/

# Ensure log directory exists
mkdir -p $LOG_DIR

# Function to wait for Arkouda server shutdown
wait_for_server_shutdown() {
    echo "Waiting for Arkouda server to shut down..."
    while pgrep -f "arkouda_server" > /dev/null; do sleep 1; done
}

# Run experiment using SLURM job array index to determine the configuration
run_experiment() {
    local probability=$1
    local nodes=$2
    local trial=$3
    echo "Starting trial $trial with probability $probability and $nodes nodes"

    # Start Arkouda server
    cd $ARKOUDA_DIR
    ./arkouda_server -nl 1 >& ${LOG_DIR}/1_Ak_server_prob_${probability}_nodes_${nodes}_trial_${trial}.txt &
    SERVER_PID=$!

    # Wait a bit for the server to start
    sleep 10

    # Get server node name
    SERVER_NODE=$(hostname)
    echo "SERVER_NODE = $SERVER_NODE"

    # Run the client
    cd $BENCHMARKS_DIR
    python3 $PYTHON_SCRIPT $SERVER_NODE $SERVER_PORT $probability $nodes 1 1 >& ${LOG_DIR}/1_client_prob_${probability}_nodes_${nodes}_trial_${trial}.txt

    # Cleanup
    kill $SERVER_PID
    wait_for_server_shutdown

    echo "Trial $trial completed"
}

# Main execution
echo "Starting experiments..."
PROBABILITY=${PROB_ARRAY[$SLURM_ARRAY_TASK_ID]}
NODES=${NODES_ARRAY[$SLURM_ARRAY_TASK_ID]}
for trial in $(seq 1 2); do  # You can adjust the number of trials if needed
    run_experiment $PROBABILITY $NODES $trial
done
echo "Experiments completed."
