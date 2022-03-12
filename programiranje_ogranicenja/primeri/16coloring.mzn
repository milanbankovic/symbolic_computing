% Primer 16. Bojenje grafa (optimizaciona varijanta)

int : n; % broj cvorova

% Matrica povezanosti
array [1..n, 1..n] of 0..1 : M;

array [1..n] of var 1..n:  C;

var 1..n: N = max(C);

constraint forall(i, j in 1..n) (M[i,j] == 1 ->  C[i] != C[j]);
 
solve minimize N;

output ["Colors: "++show(N)++": "++show(C)++"\n"];