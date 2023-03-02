% Primer 17. Maksimalna klika

int: n; % broj cvorova

% Matrica povezanosti
array [1..n, 1..n] of 0..1 : M;

var set of 1..n: S;  % skup cvorova koji cine kliku

constraint forall(i,j in 1..n where i < j) (M[i,j] == 0 -> not (i in S  /\ j in S));

 solve maximize card(S);
 
 output ["Pronadjena klika velicine \(card(S)): "++show(S)]; 