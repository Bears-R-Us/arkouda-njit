#!/bin/bash

#SBATCH -N 2 # Requesting 2 nodes
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=1

# Load modules
module load cmake
module load gcc
module load chapel/1.32.0
module load anaconda3
eval "$(conda shell.bash hook)"
conda activate arkouda-dev

# Configurations for each array job
PROB_ARRAY=(0.0005 0.0005)  # Probability values
NODES_ARRAY=(100000 50000)  # Corresponding values of n

# Define directories and files
ARKOUDA_DIR=/scratch/users/md724/arkouda-2023.11.15
BENCHMARKS_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/Experiments/
PYTHON_SCRIPT=subgraph_isomorphism_random-1.py
SERVER_PORT=5555
LOG_DIR=/scratch/users/md724/arkouda-njit/arachne/benchmarks/Experiments/Stack-Random/

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

# Function to wait for Arkouda server shutdown
wait_for_server_shutdown() {
    echo "Waiting for Arkouda server to shut down..."
    while pgrep -f "arkouda_server" > /dev/null; do sleep 1; done
}

# Loop through configurations
for CONFIG_INDEX in ${!PROB_ARRAY[@]}; do
    PROBABILITY=${PROB_ARRAY[$CONFIG_INDEX]}
    NODES=${NODES_ARRAY[$CONFIG_INDEX]}

    # Run each configuration 3 times sequentially
    for TRIAL_INDEX in {1..3}; do
        echo "Starting experiment with probability $PROBABILITY and nodes $NODES, trial $TRIAL_INDEX"
        cd $ARKOUDA_DIR
        ./arkouda_server -nl 1 >& ${LOG_DIR}/server_prob_${PROBABILITY}_nodes_${NODES}_trial_${TRIAL_INDEX}.txt &
        SERVER_PID=$!
        sleep 10  # Allow server to start

        # Check server readiness
        if ! check_server_ready "${LOG_DIR}/server_prob_${PROBABILITY}_nodes_${NODES}_trial_${TRIAL_INDEX}.txt"; then
            echo "Aborting due to Arkouda server startup failure."
            kill $SERVER_PID
            exit 1
        fi

        # Get server node name and run the client
        SERVER_NODE=$(hostname)
        cd $BENCHMARKS_DIR
        python3 $PYTHON_SCRIPT $SERVER_NODE $SERVER_PORT $PROBABILITY $NODES 1 1 >& ${LOG_DIR}/client_prob_${PROBABILITY}_nodes_${NODES}_trial_${TRIAL_INDEX}.txt

        # Cleanup
        kill $SERVER_PID
        wait_for_server_shutdown
        echo "Experiment for trial $TRIAL_INDEX completed."
    done
done
