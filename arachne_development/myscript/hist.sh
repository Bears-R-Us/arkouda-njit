for i in `ls /rhome/zhihui/Adata/SNAP/*.deg` ; do
    echo $i
    python GenHist.py $i
done
