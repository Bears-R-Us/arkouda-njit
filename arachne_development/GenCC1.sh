#grep "$1" $2 | tr '\n' ' ' | se-e 's/[^0-9.]/ /g' -e 's/^ *//g' -e 's/ *$//g' | tr -s ' ' | sed 's/ /\n/g'
rm -f tmp1
grep "read file" $1  | cut -d "=" -f2|rev| cut -d "/" -f1 |rev |tee -a tmp1
#grep "read file" $1  | cut -d "/" -f4 
rm -f tmp2
grep "Number of iterations" $1| cut -d "=" -f2 |cut -d " " -f2 |tee -a tmp2
rm -f tmp22
#pr -ts" " --columns $2 tmp2>tmp22
awk 'ORS=NR%7?" ":"\n"' <tmp2 >tmp22
rm -f tmp3
grep "cc: " $1  | cut -d ":" -f5 |cut -d " " -f2 |tee -a tmp3 
rm -f tmp32
#pr -ts" " --columns $2 tmp3>tmp32
awk 'ORS=NR%8?" ":"\n"' <tmp3 >tmp32
d=`date +%F-%H-%M-%S`
outputname="$1-OutPutData-$d.txt"
paste tmp1 tmp22 tmp32 -d " " >$outputname

