#grep "$1" $2 | tr '\n' ' ' | se-e 's/[^0-9.]/ /g' -e 's/^ *//g' -e 's/ *$//g' | tr -s ' ' | sed 's/ /\n/g'
rm tmp1
grep "read file" $1  | cut -d "=" -f2|rev| cut -d "/" -f1 |rev |tee -a tmp1
#grep "read file" $1  | cut -d "/" -f4 
rm tmp2
grep "Number of iterations" $1| cut -d "=" -f2 |tee -a tmp2
rm tmp22
#pr -ts" " --columns $2 tmp2>tmp22
awk 'ORS=NR%8?" ":"\n"' <tmp2 >tmp22
rm tmp3
grep "cc: " $1  | cut -d ":" -f5 |tee -a tmp3 
rm tmp32
#pr -ts" " --columns $2 tmp3>tmp32
awk 'ORS=NR%8?" ":"\n"' <tmp3 >tmp32
d=`date +%F-%H-%M-%S`
outputname="OutPutData-$d.csv"
paste tmp1 tmp22 tmp32 -d " " >$outputname

