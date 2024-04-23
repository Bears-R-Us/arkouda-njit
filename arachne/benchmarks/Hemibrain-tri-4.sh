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
PYTHON_SCRIPT=Hemibrain-tri-4.py
SERVER_PORT=5555
NUM_TRIALS=10
LOG_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/logs-Hemibrain-tri-4/

# Ensure log directory exists
mkdir -p $LOG_DIR

# Function to wait for Arkouda server to shut down
wait_for_server_shutdown() {
    echo "Waiting for Arkouda server to shut down..."
    while pgrep -f "arkouda_server" > /dev/null; do sleep 1; done
}

# Function to run the server and client
run_experiment() {
    for trial in $(seq 1 $NUM_TRIALS); do
        echo "Starting trial $trial"

        # Start Arkouda server
        cd $ARKOUDA_DIR
        ./arkouda_server -nl 1 >& ${LOG_DIR}/arkouda_server_trial_${trial}.txt &
        SERVER_PID=$!

        # Wait a bit for the server to initialize
        sleep 10
        echo "end of sleep 10"
        # Get server node name
        SERVER_NODE=$(hostname)
        echo "SERVER_NODE = $SERVER_NODE"
        # Run the benchmark script
        cd $BENCHMARKS_DIR
        python3 $PYTHON_SCRIPT $SERVER_NODE $SERVER_PORT 50000 1 1 >& ${LOG_DIR}/benchmark_trial_${trial}.txt

        # Cleanup: Stop the Arkouda server and wait for its shutdown
        kill $SERVER_PID
        wait_for_server_shutdown

        echo "Trial $trial completed"
    done
}

# Main execution
echo "Starting experiments..."
run_experiment
echo "Experiments completed."
