#!/bin/bash

#SBATCH --sockets-per-node=2
#SBATCH --cores-per-socket=10
#SBATCH --threads-per-core=1


PortNum=$2
d=`date +%F-%H-%M-%S`
output="$d-Server-$1-Locales-$PortNum"
# Only argument is number of locales/nodes
if [ "$#" -le 1 ];
then
    echo "usage: ./StartServer   <#locales> <PortNum> "
    exit
fi
numNodes=$1

# Get a list of the nodes allocated to this job
temp=`scontrol show hostname | paste -d, -s`
IFS=',' read -ra NODES <<< "$temp"
echo "+ Running arkouda_server with ${numNodes} locales on the following nodes:" 
for node in "${NODES[@]}"
do
    echo ${node} 
done

# Finally, start arkouda with the specified number of locales
#./arkouda_server -nl ${numNodes} &> server_out.txt


echo "./arkouda_server -nl $1 --ServerConfig.ServerPort=$PortNum &> $output"

#echo "./arkouda_server -nl $1 2>&1 |tee -a $output"
#./arkouda_server -nl $1 2>&1 |tee -a $output &
./arkouda_server -nl $1 --ServerConfig.ServerPort=$PortNum 2>&1|tee -a $output
