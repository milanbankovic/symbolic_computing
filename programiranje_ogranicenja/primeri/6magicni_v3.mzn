% Primer 6. Magicni kvadrat (treca verzija)

include "globals.mzn";

/* NAPOMENA: Ova verzija je nesto drugacija od prethodne po tome sto se 
   koriste tzv POZIVI GENERATORA.  Poziv generatora ima sledecu sintaksu:
   
   <agr-func>(<lista_generatora>) (<izraz>)
   
   i potpuno je ekvivalentan izrazu:
   
   <agr-func>([<izraz> | <lista_generatora>])
   
   U nekim slucajevima, narocito kada imamo ugnjezdene generatore, ovakva
   sintaksa izgleda preglednije. 
*/

array[1..4,1..4] of var 1..16: x;
constraint forall(i in 1..4)
                   (sum(j in 1..4) (x[i,j]) == 34);
                   
constraint forall(j in 1..4)
                   (sum(i in 1..4) (x[i,j]) == 34);
                   
constraint sum(i in 1..4) (x[i,i]) == 34;
constraint sum (i in 1..4) (x[i, 4 - i + 1]) == 34;
                   
constraint alldifferent([x[i,j] | i,j in 1..4]);

constraint x[1,2] = 12;
constraint x[2,2] = 8;
constraint x[2,3] = 15;
constraint x[3,1] = 7;
constraint x[3,3] = 2;
constraint x[4,1] = 4;
constraint x[4,4] = 11;                                          
                                                 
solve satisfy;

output [show_int(2,x[i,j])++ if j == 4 then "\n" else "   " endif | i, j in 1..4];   