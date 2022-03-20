
b = nA<=256 && nB<=256;
assert_all(b && nA*nA+nB*nB==(nA+nB)*nQ+nR && nR<nA+nB && nQ*nQ+nR==1977);

/*
janicic@ubuntu:/media/PKBACK# 001/IMOpaper$ ./ursa32 < IMO1977_5.urs -l33

***********************************************
*********  URSA Interpreter (c) 2010  *********
*** Predrag Janicic, University of Belgrade ***
***********************************************

--> Solution 1
nA=50
nB=7
nQ=44
nR=41

--> Solution 2
nA=50
nB=37
nQ=44
nR=41

--> Solution 3
nA=37
nB=50
nQ=44
nR=41

--> Solution 4
nA=7
nB=50
nQ=44
nR=41

[Formula generation: 0s; conversion to CNF: 0.184011s; total: 0.184011s]
[Solving time: 1.6161s]
[Formula size: 14260 variables, 49204 clauses]
/
