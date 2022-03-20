nX[1]=1; nX[2]=2; nX[3]=3; nX[4]=4; nX[5]=5;
nY[1]=4; nY[2]=1; nY[3]=5; nY[4]=3; nY[5]=2;

bDomain=true;
bAllDifferent=true;
for(ni=1;ni<=5;ni++) {
  bDomain &&= (0<nActual[ni] && nActual[ni]<=5);
  for(nj=1;nj<ni;nj++) 
    bAllDifferent &&= (nActual[ni] != nActual[nj]);
}

nX1=0; nX2=0; nY1=0; nY2=0;
for(ni=1;ni<=5;ni++)  {
  nX1 += ite(nX[ni]==nActual[ni],1,0);
  nY1 += ite(nY[ni]==nActual[ni],1,0);
}

for(ni=1;ni<=4;ni++) 
  for(nj=1;nj<=4;nj++) {
     nX2 += ite(nX[ni]==nActual[nj] && nX[ni+1]==nActual[nj+1],1,0);
     nY2 += ite(nY[ni]==nActual[nj] && nY[ni+1]==nActual[nj+1],1,0);
  }

assert_all(bDomain && bAllDifferent && nX1==0 && nX2==0 && nY1==2 && nY2==2);

/*  
janicic@ubuntu:/media/PKBACK# 001/IMOpaper$ ./ursa32 < IMO1963_6.urs -l3

***********************************************
*********  URSA Interpreter (c) 2010  *********
*** Predrag Janicic, University of Belgrade ***
***********************************************

--> Solution 1
nActual[1]=5
nActual[2]=4
nActual[3]=1
nActual[4]=3
nActual[5]=2

[Formula generation: 0.012s; conversion to CNF: 0.004001s; total: 0.016001s]
[Solving time: 0.004s]
[Formula size: 294 variables, 1539 clauses]






