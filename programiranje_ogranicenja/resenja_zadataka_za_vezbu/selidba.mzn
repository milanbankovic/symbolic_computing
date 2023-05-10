% Primer 40: selidba

int : S; % kapacitet svake torbe

int: n; % broj stvari

array[1..n] of int: V; % velicina svake stvari

constraint assert(forall(i in 1..n)(V[i] <= S), "Predmeti moraju biti velicine najvise S");

array [1..n] of var 1..n: torba;  % torba[i] predstavlja redni broj torbe u koju ide i-ti predmet

% Za svaku torbu, suma svih predmeta koji su rasporedjeni u tu torbu mora biti najvise S
constraint forall(i in 1..n)
    (sum(k in 1..n where torba[k] == i) (V[k]) <= S);

% Za lepsi ispis:
array [1..n] of var set of 1..n: T;

constraint forall(t in 1..n, p in 1..n)
 (p in T[t] <-> torba[p] == t);
 
% Minimizujemo M:
var 1..n: M = max(i in 1..n) (torba[i]); 
solve minimize M;

output ["Number of bags: " ++ show(M) ++ ":\n"] ++ [show(T[i]) ++ "\n" | i in 1..fix(M)];
        