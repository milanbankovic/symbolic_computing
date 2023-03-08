
assert_all(100*na+10*nb+nc==11*(na*na+nb*nb+nc*nc) && 0<na && na<10 && nb<10 && nc<10);

/*
janicic@ubuntu:/media/PKBACK# 001/IMOpaper$ ./ursa32 < IMO1960_1.urs -l12

***********************************************
*********  URSA Interpreter (c) 2010  *********
*** Predrag Janicic, University of Belgrade ***
***********************************************

--> Solution 1
na=8
nb=0
nc=3

--> Solution 2
na=5
nb=5
nc=0

[Formula generation: 0s; conversion to CNF: 0.032002s; total: 0.032002s]
[Solving time: 0.048003s]
[Formula size: 2861 variables, 10039 clauses]

*/
