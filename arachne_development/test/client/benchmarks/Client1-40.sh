#!/bin/bash

Nodes=$1
PortNum=$((2 + $2))



export CHPL_RT_NUM_THREADS_PER_LOCALE=20
echo "./runclient.sh s.py $Nodes $PortNum"
echo "./runclient.sh cctest.py $Nodes $PortNum"
./runclient.sh cctest.py $Nodes $PortNum

PortNum=$((2 + PortNum))
export CHPL_RT_NUM_THREADS_PER_LOCALE=40
echo "./runclient.sh cctest.py $Nodes $PortNum"
./runclient.sh cctest.py $Nodes $PortNum

N=40  # Change this to your desired value

adj=1
for ((i = 1; i <= N; i *= 2)); do
  export CHPL_RT_NUM_THREADS_PER_LOCALE=$i
  echo $CHPL_RT_NUM_THREADS_PER_LOCALE

  PortNum=$((2 + PortNum))
  numNodes=$1

  echo "./runclient.sh cctest.py $Nodes $PortNum"
  ./runclient.sh cctest.py $Nodes $PortNum
done

