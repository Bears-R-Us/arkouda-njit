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
BENCHMARKS_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/Tests_Parallel_Random/
PYTHON_SCRIPT=Tests_Parallel_Random.py
SERVER_PORT=5555
NUM_TRIALS=3
LOG_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/Tests_Parallel_Random/logs-Parallel/
THREAD_COUNTS=(1 2 4 8 16 32 64 128)

PROBABILITIES=(0.2)
NUM_NODES=(100 200 400 800 1600 3200 6400)

# Ensure log directory exists
mkdir -p $LOG_DIR

# Function to wait for Arkouda server to shut down
wait_for_server_shutdown() {
    echo "Waiting for Arkouda server to shut down..."
    while pgrep -f "arkouda_server" > /dev/null; do sleep 1; done
}

# Function to run the server and client
run_experiment() {
    for num_threads in "${THREAD_COUNTS[@]}"; do
        export CHPL_RT_NUM_THREADS=$num_threads
        
        for probability in "${PROBABILITIES[@]}"; do
            for num_nodes in "${NUM_NODES[@]}"; do
                for trial in $(seq 1 $NUM_TRIALS); do
                    echo "Starting trial $trial with Probability $probability, Nodes $num_nodes, and $num_threads Threads"

                    # Start Arkouda server
                    cd $ARKOUDA_DIR
                    ./arkouda_server -nl 1 >& ${LOG_DIR}/arkouda_server_trial_${trial}_p${probability}_n${num_nodes}_t${num_threads}.txt &
                    SERVER_PID=$!

                    # Wait a bit for the server to initialize
                    sleep 10
                    echo "End of sleep 10"

                    # Get server node name
                    SERVER_NODE=$(hostname)
                    echo "SERVER_NODE = $SERVER_NODE"

                    # Run the benchmark script
                    cd $BENCHMARKS_DIR
                    python3 $PYTHON_SCRIPT $SERVER_NODE $SERVER_PORT $num_nodes 1 1 $probability  >& ${LOG_DIR}/benchmark_trial_${trial}_p${probability}_n${num_nodes}_t${num_threads}.txt

                    # Cleanup: Stop the Arkouda server and wait for its shutdown
                    kill $SERVER_PID
                    wait_for_server_shutdown

                    echo "Trial $trial with Probability $probability, Nodes $num_nodes, and $num_threads Threads completed"
                done
            done
        done
    done
}

# Main execution
echo "Starting experiments..."
run_experiment
echo "Experiments completed."
