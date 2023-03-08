assert_all(nn<=1981 && nm<=1981 && (nn*nn==1+nm*nn+nm*nm || nn*nn+1==nm*nn+nm*nm)); 

/* 
janicic@ubuntu:/media/PKBACK# 001/IMOpaper$ ./ursa32 < IMO1981_3.urs -l24

***********************************************
*********  URSA Interpreter (c) 2010  *********
*** Predrag Janicic, University of Belgrade ***
***********************************************

--> Solution 1
nm=1
nn=0

--> Solution 2
nm=5
nn=8

--> Solution 3
nm=89
nn=144

--> Solution 4
nm=1
nn=2

--> Solution 5
nm=377
nn=610

--> Solution 6
nm=21
nn=34

--> Solution 7
nm=0
nn=1

--> Solution 8
nm=8
nn=13

--> Solution 9
nm=1
nn=1

--> Solution 10
nm=13
nn=21

--> Solution 11
nm=3
nn=5

--> Solution 12
nm=55
nn=89

--> Solution 13
nm=144
nn=233

--> Solution 14
nm=987
nn=1597

--> Solution 15
nm=233
nn=377

--> Solution 16
nm=2
nn=3

--> Solution 17
nm=34
nn=55

--> Solution 18
nm=610
nn=987

[Formula generation: 0s; conversion to CNF: 0.252016s; total: 0.252016s]
[Solving time: 11.1047s]
[Formula size: 17165 variables, 60267 clauses]
*/

