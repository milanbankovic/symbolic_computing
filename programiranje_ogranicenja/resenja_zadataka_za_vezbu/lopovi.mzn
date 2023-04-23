% Primer 42: Lopovi dele pare

int : n; % broj novcanica

enum Lopov = { Prvi, Drugi };

array [1..n] of int: val; % va[i] je vrednost i-te novcanice

array [1..n] of var Lopov: x; % x[i] oznacava kom lopovu ide i-ta novcanica

% Suma novcanica prvog i suma novcanica drugog moraju biti iste
constraint 
   sum(i in 1..n where x[i] == Prvi) (val[i]) == sum(i in 1..n where x[i] == Drugi) (val[i]);
   
solve satisfy;

output["Prvi: "++show([val[i] | i in 1..n where x[i] == Prvi]) ++ "\nDrugi: "++show([val[i] | i in 1..n where x[i] == Drugi])];