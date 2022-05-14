% Primer 39: Polica sa knjigama

int : L; % Duzina police

int: n; % Broj knjiga

array [1..n] of int: D; % debljina knjige u milimetrima

var set of 1..n: S; % izabrane knjige
constraint sum(i in S) (D[i]) == L;
solve satisfy;
output ["Book " ++ show(e) ++ " of width: " ++ show(D[e]) ++ "\n" | e in fix(S)];

%Alternativno
%array [1..n] of var 0..1: x; % x[i] == 1 znaci da je i-ta knjiga izabrana
%constraint sum(i in 1..n) (D[i]*x[i]) == L;
%solve satisfy;
%output ["Book " ++ show(i) ++ " of width: " ++ show(D[i]) ++ "\n" | i in 1..n where fix(x[i]) == 1];
