% Primer 18. Sudoku

include "globals.mzn";

int: n; % velicina "malog" kvadrata
int: N = n*n;  % velicina "velikog" kvadrata

array [1..N, 1..N] of int: M;  % matrica predefinisanih vrednosti (0 za prazno polje)

array [1..N, 1..N] of var 1..N: x;  % popunjena matrica

constraint forall(i in 1..N) (alldifferent([x[i, j] | j in 1..N]));
constraint forall(j in 1..N) (alldifferent([x[i, j] | i in 1..N]));
constraint forall(k,l in 1..n) (alldifferent([x[(k-1)*n+i, (l-1)*n+j] | i,j in 1..n]));

constraint forall(i,j in 1..N) (M[i,j] != 0 -> M[i,j] == x[i,j]);

solve satisfy;

output [show(x[i,j]) ++ if j == N then "\n" else " " endif | i,j in 1..N];