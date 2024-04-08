#grep "$1" $2 | tr '\n' ' ' | se-e 's/[^0-9.]/ /g' -e 's/^ *//g' -e 's/ *$//g' | tr -s ' ' | sed 's/ /\n/g'
rm -f tmp11
grep "read file" $1  | cut -d "=" -f2|rev| cut -d "/" -f1  |cut -d "." -f2|rev |tee -a tmp11
#grep "read file" $1  | cut -d "/" -f4 
rm -f tmp22
grep "The largest diameter " $1| cut -d "=" -f2 |cut -d " " -f2 |tee -a tmp22
#pr -ts" " --columns $2 tmp2>tmp22
rm -f tmp3
grep "Size of the Components" $1| cut -d "=" -f2 |cut -d " " -f2 |tee -a tmp3
#pr -ts" " --columns $2 tmp3>tmp32
awk 'ORS=NR%3?" ":"\n"' <tmp3 >tmp33
d=`date +%F-%H-%M-%S`
outputname="$1-OutPutData-$d.txt"
paste tmp11 tmp22 tmp33 -d " " >$outputname

