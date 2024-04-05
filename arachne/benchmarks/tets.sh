#!/bin/bash

# Loop 100 times
for i in {1..100}
do
    echo "Starting test iteration $i"
    
    # Start the Arkouda server in the background
    ../scratch/users/md724/arkouda-2023.11.15/arkouda_server -nl 1 &
    ARKOUDA_PID=$!
    
    sleep 5 # Wait a bit for the server to start up completely

    # Run your Python script and append the output to a file
    python3 subgraph_isomorphism_DotMotif.py n115 5555 1 1 >> test_output_$i.txt

    # Kill the Arkouda server process
    kill $ARKOUDA_PID
    
    sleep 2 # Wait a bit to ensure the server has stopped

    echo "Test iteration $i completed"
done
