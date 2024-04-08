#!/bin/bash
#SBATCH --exclusive
#SBATCH -N 2

PortNum=2005
numNodes=2
d=`date +%F-%H-%M-%S`
output="$d-Server-$1-Locales-$PortNum"
echo $output
#SBATCH -o $output.log-%j-%a

# Get a list of the nodes allocated to this job
temp=`scontrol show hostname | paste -d, -s`
echo $temp
export SSH_SERVERS=$temp
IFS=',' read -ra NODES <<< "$temp"
echo "+ Running arkouda_server with ${numNodes} locales on the following nodes:"
for node in "${NODES[@]}"
do
    echo ${node}
done

#./arkouda_server -nl $numNodes --ServerConfig.ServerPort=$PortNum 2>&1|tee -a $output
export LD_LIBRARY_PATH=$HOME/anaconda3/envs/arkouda-dev/lib:$LD_LIBRARY_PATH
echo $LD_LIBRARY_PATH
./arkouda_server -nl $numNodes --ServerConfig.ServerPort=$PortNum 2>&1

