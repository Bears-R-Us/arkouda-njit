d=`date +%F-%H-%M-%S`
scriptname=$1
nodename=$2
serverport=$3
numberofnodes=$4
output="$d-$scriptname-$nodename-$serverport-$numberofnodes-Locales"
echo "python  $scriptname  $nodename $serverport  2>&1 |tee -a $output-Client" >>$output-Client
cat $scriptname >>$output-Client
python  $scriptname  $nodename $serverport  2>&1 |tee -a $output-Client
#python shutdown.py $nodename  $serverport 
