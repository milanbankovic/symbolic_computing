% Primer 13. Golombov lenjir (optimizaciona varijanta)

include "globals.mzn";

int: k;
int: n = k*k;

array [1..k] of var 0..n: x;

var 1..n: N;

% Uslovi poretka
constraint forall(i in 1..k-1) (x[i] < x[i+1]);

% Granicni uslovi
constraint x[k] == N;
constraint x[1] == 0;

% Razbijanje simetrije 
constraint k > 2 -> x[k] - x[k-1] > x[2] - x[1];

% Definisemo predikat koji zahteva da susedne razlike budu sve 
% razlicite medju sobom
predicate diffs_alldiff(array [int] of var int: x) =
   let { array [1..k, 1..k] of var 1..n: y; } in 
      forall(i,j in 1..k where i < j) (y[i,j] == x[j] - x[i]) /\
      alldifferent([y[i,j] | i,j in 1..k where i < j]);

constraint diffs_alldiff(x);

solve minimize N;

