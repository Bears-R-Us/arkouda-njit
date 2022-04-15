d=`date +%F-%H-%M-%S`
serverport=$4
output="$d-$1-$serverport-$3-$2-Locales"
echo  "python $3  $1 $serverport 2>&1 |tee -a $output-Client"
python $3  $1 $serverport 2>&1 |tee -a $output-Client
#python shutdown.py $1 $serverport 
