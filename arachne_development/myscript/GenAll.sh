for i in `ls 2023-11*`; do
   if [[ ! "$i" =~ "OutPut" ]]; then
      echo "./GenCC1.sh $i"
      ./GenCC1.sh $i
   fi
done
