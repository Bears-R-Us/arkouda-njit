#grep "$1" $2 | tr '\n' ' ' | se-e 's/[^0-9.]/ /g' -e 's/^ *//g' -e 's/ *$//g' | tr -s ' ' | sed 's/ /\n/g'
rm -f tmp11
grep "read file" $1  | cut -d "=" -f2|rev| cut -d "/" -f1  |cut -d "." -f2|rev |tee -a tmp11
#grep "read file" $1  | cut -d "/" -f4 
rm -f tmp2
grep "Number of iterations" $1| cut -d "=" -f2 |cut -d " " -f2 |tee -a tmp2
rm -f tmp22
#pr -ts" " --columns $2 tmp2>tmp22
awk 'ORS=NR%9?" ":"\n"' <tmp2 >tmp22
rm -f tmp2 tmp3
grep "cc: " $1  | cut -d ":" -f5 |cut -d " " -f2 |tee -a tmp3 
rm -f tmp33 
#pr -ts" " --columns $2 tmp3>tmp32
awk 'ORS=NR%9?" ":"\n"' <tmp3 >tmp33
d=`date +%F-%H-%M-%S`
outputname="$1-OutPutData-$d.txt"
paste tmp11 tmp22 tmp33 -d " " >$outputname
rm tmp11 tmp22 tmp33 tmp1 tmp2 tmp3
