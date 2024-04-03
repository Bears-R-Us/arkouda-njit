for i in `ls `; do
   if [[ "$i" =~ ^.*\.txt$ && "$i" =~ "OutPut" ]]; then
      echo "rm  $i"
      rm  $i
   fi
done
