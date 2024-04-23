#!/bin/bash

#SBATCH -N 2 # Requesting 2 nodes, adjust as necessary

# Load modules and set up the environment
module load cmake
module load gcc
module load chapel/1.32.0
module load anaconda3
eval "$(conda shell.bash hook)"
conda activate arkouda-dev

# Define variables
ARKOUDA_DIR=/scratch/users/md724/arkouda-2023.11.15
BENCHMARKS_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/
PYTHON_SCRIPT=subgraph_isomorphism_Hemibrain-6.py
SERVER_PORT=5555
NUM_TRIALS=3
LOG_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/logs-Hemibrain-6/

# Ensure log directory exists
mkdir -p $LOG_DIR

# Function to check Arkouda server readiness
check_server_ready() {
    echo "Checking Arkouda server readiness..."
    for i in {1..30}; do # Wait up to 30 seconds for the server to be ready
        if grep -q "server listening on" "$1"; then
            echo "Arkouda server is ready."
            return 0
        fi
        sleep 1
    done
    echo "Arkouda server failed to start within the expected time."
    return 1
}

# Function to run the server and client
run_experiment() {
    # Start Arkouda server
    cd $ARKOUDA_DIR
    ./arkouda_server -nl 1 >& ${LOG_DIR}arkouda_server_log6.txt &
    SERVER_PID=$!

    # Check server readiness
    if ! check_server_ready "${LOG_DIR}arkouda_server_log6.txt"; then
        echo "Aborting due to Arkouda server startup failure."
        kill $SERVER_PID
        exit 1
    fi

    # Get server node name
    SERVER_NODE=$(hostname)

    # Run the benchmark script
    cd $BENCHMARKS_DIR
    for i in $(seq 1 $NUM_TRIALS); do
        echo "Trial $i: Running benchmark on $SERVER_NODE:$SERVER_PORT"
        python3 $PYTHON_SCRIPT $SERVER_NODE $SERVER_PORT 50000 1 1 >& ${LOG_DIR}benchmark_trial6_${i}.txt
    done

    # Cleanup: Stop the Arkouda server
    kill $SERVER_PID
}

# Main execution
echo "Starting experiments..."
run_experiment
echo "Experiments completed."
