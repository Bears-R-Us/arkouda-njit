module JCSMsg {

  use Reflection;
  use ServerErrors;
  use Logging;
  use Message;
  use SegmentedString;
  use ServerErrorStrings;
  use ServerConfig;
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use IO;


  use RadixSortLSD;
  use Set;
  use DistributedBag;
  use ArgSortMsg;
  use Time;
  use CommAggregation;
  use Map;
  use DistributedDeque;


  use Atomics;
  use IO.FormattedIO; 
  use GraphArray;
  use GraphMsg;
  use HashedDist;

  use LinearAlgebra;
  use Math;

  private config const logLevel = LogLevel.DEBUG;
  const smLogger = new Logger(logLevel);

  

  // calculate longest common subsequence of two strings
  proc segLCSMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab): MsgTuple throws {
      var repMsg: string;
      var sname1=msgArgs.getValueOf("StrEntry1");
      var sname2=msgArgs.getValueOf("StrEntry2");

      st.checkTable(sname1);
      st.checkTable(sname2);

      writeln("name1=",sname1);
      writeln("name2=",sname2);
      var sstrings1 = getSegString(sname1, st);
      var sstrings2 = getSegString(sname2, st);


      var size1=sstrings1.size;
      var nBytes1 = sstrings1.nBytes;
      var length1=sstrings1.getLengths();
      writeln("Len1=",length1);
      var offsegs1 = (+ scan length1) - length1;

      var size2=sstrings2.size;
      var nBytes2 = sstrings2.nBytes;
      var length2=sstrings2.getLengths();
      writeln("Len2=",length2);
      var offsegs2 = (+ scan length2) - length2;


      const infin:int=9999;
      var m:int=length1[0]-1;
      var n:int=length2[0]-1;
      writeln("m=",m);
      writeln("n=",n);
      if (m>n) {
         m<=>n;
         sstrings1<=>sstrings2;
      }
      var mystring1=sstrings1.values.a[0..m-1];
      var mystring2=sstrings2.values.a[0..n-1];

      writeln("string1=",mystring1);
      writeln("string2=",mystring2);

      proc PeelLCS(lstring1:[?D1] uint(8),lstring2:[?D2] uint(8), retary:[?D3] uint(8) ) :int {
            var localm:int =D1.size;
            var localn:int =D2.size;
            if (localm==0) || (localn==0) {
                return 0;
            }
            if lstring1[localm-1]==lstring2[localn-1] {
                var ary1=lstring1[0..localm-2];
                var ary2=lstring2[0..localn-2];
                var firstpart=PeelLCS(ary1,ary2,retary);
                retary[firstpart]=lstring1[localm-1];
                //writeln("last element ",lstring1[localm-1]," is equal");
                return firstpart+1;
            } else {
                var ary1=lstring1[0..localm-1];
                var ary2=lstring2[0..localn-2];

                var ary3=lstring1[0..localm-2];
                var ary4=lstring2[0..localn-1];

                var part1=PeelLCS(ary1,ary2,retary);
                var tmpary=retary;
                var part2=PeelLCS(ary3,ary4,tmpary);
                //writeln("part1=",part1,"value=", retary[0..part1-1],", part2=",part2," value=",tmpary[0..part2-1]);
                if part1 >part2 {
                     return part1;
                } else {
                     retary[0..part2-1]=tmpary[0..part2-1];
                     return part2;
                }
            }
      }



      /*
      var tmpstrArray:[0..m-1] uint(8);
      var mylen=PeelLCS(mystring1,mystring2,tmpstrArray);
      var strArray: [0..mylen-1] uint(8);
      forall i in 0..tmpstrArray.size-1{
           strArray[i]=tmpstrArray[i]:uint(8);
      }

      writeln("length of lcs=",mylen,",sequential lcs=",strArray);
      */


      ref string1=mystring1;
      ref string2=mystring2;






  var mat:[0..m][0..n] int;

  //Below is for making the adjacency matrix of the graph.
  forall i in 0..m-1{

    forall j in 0..n-1{
      if string1[i]==string2[j]{
        mat[i][j]=1;
      }
    }
  }
  //below is for checking the matrix. It is only for testing and does not have a special roll.
  proc printMatrix(matrix) {
    var nn=matrix.size;
    var mm=matrix[matrix.dim(0).low].size;
    for i in matrix.dim(0).low..matrix.dim(0).high{
      for j in matrix[matrix.dim(0).low].dim(0).low..matrix[matrix.dim(0).low].dim(0).high{
        write(matrix[i][j], " ");
      }
      writeln();
    }
  }
  //Below function finds the prefix sum of its input array.
  proc prefsum(list:[0..n] int){
    var exp: int = 1;
    var expm1, expnot: int;
    while (exp < n+1) {
        expm1 = exp - 1;
        expnot = ~exp;
        forall j in 0..n {
          if (j&exp != 0){
            list[j] = list[j]+list[j&expnot|expm1];
          }
        }
      exp = exp << 1;
    }
    //  writeln(" The prefix sums of the input array for the function prefsum is ",list);
  }
  //All below code is for computing the 0th and the first breakout of each vertex in row number i and store them in dg[i][0] and dg[i][1]
  var jk:[0..m][0..n] int;

  var jkimax:[0..m] int;
  forall i in 0..m{
    var c=mat[i];
    prefsum(c);
    forall j in 0..n{
      if (((j==0)&&(c[0]==1))||((j>0)&&(c[j]!=c[j-1]))){
        jk[i][c[j]-1]=j;
        jkimax[i]=max(jkimax[i],j+1);
      }
    }
  }

  var dgh:[0..m][0..0][0..n] int;
  var dgs:[0..m][0..n][0..0] int;
  forall i in 0..m{
    dgh[i][0][0]=jk[i][0]+1;
    forall j in 1..n{
      if (jk[i][j]>0)&&(jk[i][j-1]<n){
        dgh[i][0][jk[i][j-1]+1]=jk[i][j]-jk[i][j-1];
      }
    }
    prefsum(dgh[i][0]);
    forall j in 0..n{
      if(j>=jkimax[i]){
        dgh[i][0][j]=infin;
      }
    }
  }
  forall i in 0..m{
    forall j in 0..n{
      dgs[i][j][0]=dgh[i][0][j];
    }
  }
  // In rowdg, we save the 0th breakout and first breakout of each vertex.
  var rowdg:[0..2*m][0..n][0..1] int;
  forall i in 0..m{
    forall j in 0..n{
      rowdg[i][j][1]=dgs[i][j][0];
      rowdg[i][j][0]=j;

    }
  }
  forall i in m+1..2*m{
    forall j in 0..n{
      rowdg[i][j][0]=j;
      rowdg[i][j][1]=infin;
    }
  }
  /*
  for i in 0..m{
    writeln("rowdg[i]= ");
    printMatrix(rowdg[i]);
    writeln();
  }*/
  //The below function computes the leftmost vertex we can reach with a path with weight q from vertex "vertex" if the upper part of the path has weight p.

  proc find_cell(dgu,dgl,vertex,p,q){
    if p>q{
      return infin;
    }
    //The combination of D_G(U) and D_G(L) is a k*n matrix such that the minima of column j is the index of the num_bre th breakout

    if ((p<dgu[0].size)&&(dgu[vertex][p]<n) && (q-p<dgl[0].size)&&(q-p>=0)){
        //dgl[dgu[vertex][p]][q-p] is the leftmost vertex in the down row od dgl we can reach by starting from vertex in the first row of dgu and the weight of the path in dgu is p and in dgl is q-p.
        return dgl[dgu[vertex][p]][q-p];
      //  writeln("i== ",i," j== ",j, "  dgu[j][i]=  ",dgu[j][i],  "  dgl[dgu[j][i]][k-i]= ",dgl[dgu[j][i]][k-i]);
    }
    else{
        return infin;
    }
  }

  // Function below finds the index of the minimum element of elements of column "col" between "top" and "bottom" such that "col" is a column of dg.
  proc findMinIndex( dgu,dgl,vertex:int, col: int, top: int, bottom: int) {
    //writeln("dgu =",dgu);
    //writeln("dgl =",dgl);
    var listsize = bottom - top + 1;
    var exp: int = 1;
    var expm1, expnot: int;

    var prefix: [0..listsize-1] int;
    var minIndex: [0..listsize-1] int;

    forall i in 0..listsize-1{
      prefix[i] = find_cell(dgu,dgl,vertex,i+top,col);//matrix[i + top,col];
      minIndex[i] = i;
    }
    //writeln("Input to findMinIndex: ", col," ", top," ", bottom," prefix: ",prefix);

    while (exp < listsize) {
      expm1 = exp - 1;
      expnot = ~exp;
      forall j in 0..listsize-1 {
        if (j&exp != 0){
          // prefix[j] = prefix[j]+prefix[j&expnot|expm1];
          // prefix[j] = min(prefix[j],prefix[j&expnot|expm1]);
          if (prefix[j&expnot|expm1] <= prefix[j]) {
            prefix[j] = prefix[j&expnot|expm1];
            minIndex[j] = minIndex[j&expnot|expm1];
          }
        }
      }
      exp = exp << 1;
  }
    //writeln("prefix: ", prefix," minIndex: ", minIndex);
    return minIndex[listsize-1]+top;
  }
  var mins:[0..4*(n+1)*(m+1)]int;
  //In the function below, we find the index of the minimum of each column of matrix dg and save them in array "mins" recursively. We find the minimum of the middle column, and find the minimum of each 
  //column left of the middle column which is upper than the min index of the middle column, and we find the min index of each column right of the middle column, which is downer than the min index of the middle column.
  proc findColMins(dgu,dgl,vertex:int, left: int, right: int, top: int, bottom: int, mins,firstind:int) {

    var cols = right - left + 1;//it shows the number of columns of the matrix we want to work with.
    if(cols < 1){
      return;
    }
    //writeln("num =",num,"  left= ", left, "right = ",right);
    var midCol = ceil((right+left)/2): int;
    var minIndex = findMinIndex(dgu,dgl,vertex:int, midCol, top, bottom);

    // writeln(" the minima of column ",midCol," is index ",findMinIndex(dgu,dgl,vertex:int, midCol, top, bottom)," but variable MinIndex is ",minIndex );
    mins[firstind+midCol-left] = minIndex;
    //writeln("firstind= ",firstind," midcol= ",midCol," left= ",left," right= ",right," mins index= ",firstind+midCol-left,"  minIndex= ",minIndex," top= ",top," bottom = ",bottom);
    if find_cell(dgu,dgl,vertex,minIndex,midCol)!=infin{

      cobegin{ //Parallel step
        findColMins(dgu,dgl,vertex:int, left, midCol-1, top, minIndex, mins,firstind); //left submatrix
        findColMins(dgu,dgl,vertex:int, midCol+1, right, minIndex, bottom, mins,firstind+midCol-left+1); //right submatrix
      }
    }
    else{
      //It means that all of the cells in this column and right columns of it are infinite. We should only find the minimum of the left columns.
      findColMins(dgu,dgl,vertex:int, left, midCol-1, top, bottom, mins,firstind);
    }
  }

  //Below is the initialization of matrix "javab". In each iteration that we compute matrices dg, we put them in matrix javab. If we
  // have m rows, in the first iteration we have m matrices, in the nex one m/2 matrices, in the next iteration m/4 matrices...etc...
  
  var javab:[0..50][0..n][0..4*m+1] int;
  forall k in 0..logBasePow2(n,1)+1{
    forall i in 0..n{
      forall j in 0..4*m+1{
          javab[k][i][j]=infin;
      }
    }
  }
  forall i in 0..m-1{
    var sot=2*i;
    //printMatrix(rowdg[i]);
    forall j in 0..n{
      javab[0][j][sot]=rowdg[i][j][0];
      javab[0][j][sot+1]=rowdg[i][j][1];

    }
  }

  var nummat=0;
  //lastbre is the first of the word "last breakout".
  var lastbre=-1;
  //writeln("matrix number 0 :");
  //printMatrix(javab[0]);
  // In the below function, in each step, we combine each 2 adjacent matrices(dgu and dgl) to get a dg of them. We do it until 1 matrix remains at last.
  proc computedg(left: int, right: int, top: int, bottom: int, mins){ 
    var x=2;
    var intmat=0;
    while((x)<=2*m-1){
      
      // writeln("x = ",x);
      intmat=intmat+1;
      lastbre=x;
      nummat=intmat;
      var cp:[0..n][0..4*m+1] int ;
      if(intmat>0){
        cp=javab[intmat-1];
      }
      forall f in 0..m/x {
          
        // writeln("n= ",n);
        forall i in 0..n{
          //writeln("i= ",i," x= ",x);
          var dgu:[0..n][0..((x+2)/2)-1] int;
          var dgl:[0..n][0..((x+2)/2)-1] int;
          //for the first step, we define dgu and dgl as 2 matrices rowdg. 
          if(x==2){
            dgu=rowdg[2*f];
            dgl=rowdg[2*f+1];
          }
          else{
          // writeln("x = ",x," f= ",f,"  ",(f*(x+2))+(x+2)/2-1);
            [u in 0..n][v in 0..(x+2)/2-1]dgu[u][v]=cp[u][(f*(x+2))+v];
            [u in 0..n][v in 0..(x+2)/2-1]dgl[u][v]=cp[u][f*(x+2)+(x+2)/2+v]; 
          }
          //  writeln("reached step 1");
          /*  writeln("nummat= ",nummat," i= ",i,"\n"," dgu= ");
          printMatrix(dgu);
          writeln();
          writeln("dgl= ");
          printMatrix(dgl);
          writeln();*/
          // writeln(i);
          findColMins(dgu,dgl,i,0,x,0,x/2,mins,(f*n+i)*(x+1));
          // writeln("first stop x = ",x);
          forall j in 0..x{
          //  writeln("j = ",j," (f*n+i)*(x+1)+j = ",(f*n+i)*(x+1)+j," mins.size= ", mins.size," i = ",i,"   f=  ",f);
            //In the constraint below, we see that if we have computed a cell of the dg matrix before, get the minimum of it and the new amount we have; otherwise, just we replace it with the value we got for it now.
            if dgu[0].size>j{
            // writeln( i, "=i ", j, " = j", " index=  ",(f*n+i)*(x+1)+j);
              javab[intmat][i][f*(x+1)+j]=min(dgu[i][j],min(dgl[i][j],find_cell(dgu,dgl,i,mins[(f*n+i)*(x+1)+j],j)));
              //    writeln("x==",x,"  dgu[j][i] = ",dgu[j][i],"  dgl[j][i]= ",dgl[j][i],"  mins[i][j]= ",mins[i]);
              //    writeln("dgu = ");
              //    printMatrix(dgu);
              //    writeln();
              //    writeln("dgl = ");
                //  printMatrix(dgl);
                
              }
            else{
              javab[intmat][i][f*(x+1)+j]=find_cell(dgu,dgl,i,mins[(f*n+i)*(x+1)+j],j);
            }
          }
        }
      }
     // writeln("x = ",x);
     // printMatrix(javab[intmat]);
      x=x*2;
    }
  }

  var ans:[0..3][0..n-1] int;

  computedg(0,n,0,2,mins);
  // "lastbre" contains the upper bound of the last breakout of the first vertex of the first row.
  lastbre=lastbre/2;

  forall i in 0..n-1{
    // writeln("for vertex i= ",i);
    // writeln();
    findColMins(rowdg[0],rowdg[1],i,0,2,0,1,mins,0);
    // for j in 0..2{
    //  write(mins[i][j]," ");
    // }
    //writeln();
  }
  //The procedure below finds the last breakout for a vertex which is less than infinity. It does it by a binary search.
  proc findlast(){
    var left=0;
    var right=m;
    
    while(1){
      var mid=(left+right)/2;
      //writeln("left = ",left," right= ",right," mid = ",mid);
      if((javab[nummat][0][mid]!=infin)&&((mid==right)||(javab[nummat][0][mid+1]==infin))){
        return mid;
      }
      if(javab[nummat][0][mid]==infin){
        right=mid-1;
      }
      else{
        left=mid+1;
      }
    }
    return left;
  }
  //writeln("findlast = ",findlast());
  var cross:[0..m] int;
  //function below is for computing the cross vertices and store them in "cross". Cross vertices are the first vertices we reach them in their row. Each row has exactly one cross vertex.
  proc cross_finder(leftgr,rightgr,topgr,bottomgr,breakout,mat_num){
    
    if(rightgr-leftgr<breakout){
      return;
    }
    if((leftgr>rightgr)){
      return;
    }
    if((topgr>bottomgr)){
      return;
    }
    if(breakout<0){
      return;
    }
    if topgr==bottomgr{
      cross[topgr]=leftgr;
    //  writeln("kind 0 :  cross[",topgr,"]= ",leftgr);
      return;
    }
    //Below case means that the matrix has only one column.
    if (leftgr==rightgr)||(breakout==0){
      forall i in topgr+1..bottomgr{
        cross[i]=leftgr;
       // writeln("for kind 1:  ,leftgr= ",leftgr, " rightgr= ",rightgr,"  topgr = ",topgr, " ", "bottomgr= ",bottomgr, "  number of breakout= ",breakout," mat_num= ",mat_num," number of col = ",num_of_col);
       // writeln("kind 1 : cross[",i,"]= ",leftgr);
      }
      return;
    }
    //Below case means that the matrix has only one row.
    if (breakout==1)&&(bottomgr-topgr==1){
      cross[topgr]=leftgr;
      cross[bottomgr]=javab[0][leftgr][2*topgr+1];
      //  writeln("kind 2 :cross[",topgr,"] = ",leftgr);
      //  writeln("kind 3 :cross[",bottomgr,"] = ",javab[0][leftgr][2*topgr+1]);
      //if(bottomgr==4 && javab[0][topgr][2*topgr+1]==8){
      //    writeln("for kind 3:  ,leftgr= ",leftgr," leftmat= ",leftmat, " rightgr= ",rightgr," rightmat =  ",rightmat,"  topgr = ",topgr, " topmat= ",topmat," ", "bottomgr= ",bottomgr, " bottommat= ",bottommat,"  number of breakout= ",breakout," mat_num= ",mat_num," number of col = ",num_of_col);
      //}
      return;
    }
  
    var topmat=0;
    var bottommat=n;
    if((bottomgr-topgr==1)&&(breakout>1)){
      return;
    }
    //In different steps, we calculated different matrices. Now, from those matrices, we are finding the path. We should know that which matrix we should use in each step, and divide that to dgu and dgl. The line below is for doing this.
    var the_related_matrix=logBasePow2(bottomgr-topgr-1,1);
    var num_of_col= 1<<(the_related_matrix);
    var u=(topgr)/(num_of_col);
    var leftmat= topgr+u;
    var rightmat=leftmat+num_of_col;

    var midcol=(leftgr+rightgr)/2;
    
    var which=-1;
    var dgu:[topmat..bottommat][leftmat..rightmat] int;
    
    if(mat_num>0){
      [u in topmat..bottommat][v in leftmat..rightmat]dgu[u][v]=javab[the_related_matrix][u][v];
    }
    
    var dgl:[topmat..bottommat][rightmat+1..2*rightmat-leftmat+1]int ;
    if(mat_num>0){
      [u in topmat..bottommat][v in rightmat+1..2*rightmat-leftmat+1]dgl[u][v]=javab[the_related_matrix][u][v];
    }
    
    var a:[0..2*n] int;

    var dif=bottomgr-topgr;


    var lg=-1;
    while(topgr+(1<<(lg+1))<bottomgr){
      lg=lg+1;
    }
    var midrow=topgr+(1<<lg);
    /*if(midrow==11){
      writeln("lg= ",lg);
    }
    if((1<<lg)!=midrow){
      lg=lg+1;
    }
    if(topgr+(1<<lg)<bottomgr){
      midrow=topgr+1<<(lg);
    }*/
    /*writeln("leftgr= ",leftgr," leftmat= ",leftmat, " rightgr= ",rightgr," rightmat =  ",rightmat,"  topgr = ",topgr, " topmat= ",topmat," ", "bottomgr= ",bottomgr, " bottommat= ",bottommat," ", " midcol= ",midcol,"  number of breakout= ",breakout," mat_num= ",mat_num," number of col = ",num_of_col);
    writeln("dgu = ");
    printMatrix(dgu);
    writeln();
    writeln("dgl = ");
    printMatrix(dgl);
    writeln();
    writeln();
    writeln("leftgr= ",leftgr," leftmat= ",leftmat, " rightgr= ",rightgr," rightmat =  ",rightmat,"  topgr = ",topgr, " topmat= ",topmat," ", "bottomgr= ",bottomgr, " bottommat= ",bottommat," ", " midcol= ",midcol,"  number of breakout= ",breakout," mat_num= ",mat_num," number of col = ",num_of_col);*/
    //readLine();
    var f=leftmat+breakout;
    forall i in leftmat..min(rightmat,f) {
      
      if (dgu[leftgr][i]<=n){
          if((f-i+dgl[0].dim(0).low<=dgl[dgu[leftgr][i]].dim(0).high)){
            if((dgl[dgu[leftgr][i]][f-i+dgl[0].dim(0).low]==rightgr)){
              a[i]=i-leftmat;
            // writeln("dgl[dgu[",leftgr,"][",i,"]][",f-i,"]= ",javab[mat_num][leftgr][breakout],")");
          }
        }
      }
    }
    which = max reduce a;
    cross[midrow]=dgu[leftgr][which+leftmat];
    // }
    /*if(midrow==11){
    writeln("kind 4:  cross [",midrow,"]= ",dgu[leftgr][which+leftmat]);
    //readLine();

      writeln("for kind 4:  leftgr= ",leftgr," leftmat= ",leftmat, " rightgr= ",rightgr," rightmat =  ",rightmat,"  topgr = ",topgr, " topmat= ",topmat," ", "bottomgr= ",bottomgr, " bottommat= ",bottommat,"  number of breakout= ",breakout," mat_num= ",mat_num," number of col = ",num_of_col," which= ",which);
      writeln();
      writeln("a = ",a);
      writeln("dgu = ");
      printMatrix(dgu);
      writeln();
      writeln("dgl = ");
      printMatrix(dgl);
      writeln(); 
      //writeln();
    }*/
    cobegin{
      cross_finder(leftgr,dgu[leftgr][which+leftmat],topgr,midrow,which,mat_num-1);
      cross_finder(dgu[leftgr][which+leftmat],rightgr,midrow,bottomgr,breakout-which,mat_num-1);
    }
  }
    //writeln("lastbre= ",lastbre);
  cross_finder(0,javab[nummat][0][findlast()],0,m,findlast(),nummat);
 /* for i in 0..m{
    writeln("cross of line ",i," is ",cross[i]);
  }*/
  var common:[0..m-1] int;
  forall i in 1..m{
    if (cross[i]>0)&&(string1[i-1]==string2[cross[i]-1])&&(cross[i]!=cross[i-1]){
      common[i-1]=1;
    }
  }



      var cur:int=0;
      for i in 0..m-1{
        if(common[i]){
          cur+=1;
        }
      }



      var myoffsegs = makeDistArray(1, int);
      myoffsegs=0;
      var mystrArray= makeDistArray(cur+1, uint(8));

      var mycur:int=0;
      for i in 0..m-1{
        if(common[i]){
          mystrArray[mycur]=string1[i];
          mycur+=1;
        }
      }
      mystrArray[cur]=0:uint(8);
      //writeln("length of lcs=",mylen,",sequential lcs=",strArray);
      writeln("length of lcs=",mystrArray.size,", parallel lcs=",mystrArray);




      var retString = getSegString(myoffsegs, mystrArray, st);

      repMsg = 'created ' + st.attrib(retString.name) + '+created bytes.size %t'.format(retString.nBytes);


      //repMsg = 'created ' + st.attrib(segName) + '+created ' + st.attrib(valName);
      smLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }








    use CommandMap;
    registerFunction("segmentedStrLCS", segLCSMsg,getModuleName());
 }


