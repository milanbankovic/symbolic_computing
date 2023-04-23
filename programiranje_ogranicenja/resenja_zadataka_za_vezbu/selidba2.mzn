% Primer 40: selidba (verzija 2)

int : S; % kapacitet svake torbe

int: n; % broj stvari

array[1..n] of int: V; % velicina svake stvari

constraint assert(forall(i in 1..n)(V[i] <= S), "Predmeti moraju biti velicine najvise S");

array [1..n] of var set of 1..n: torba;  % torba[i] predstavlja i-tu torbu

% Sadrzaji svake dve torbe moraju biti medjusobno disjunktni
constraint forall(i, j in 1..n where i < j) ((torba[i] intersect torba[j]) = {});

% Unija sadrzaja svih torbi mora biti jednaka celom skupu
constraint array_union(torba) = 1..n;

% Za svaku torbu, suma svih predmeta koji su rasporedjeni u tu torbu mora biti najvise S
constraint forall(i in 1..n)
    (sum(k in torba[i]) (V[k]) <= S);

% M je broj torbi koje se zaista koriste
var 1..n: M = max([ i | i in 1..n where torba[i] != {}]);  
 
                
                 
% Minimizujemo M;
solve minimize M;

output ["Number of bags: " ++ show(M) ++ ":\n"] ++ [show(torba[i]) ++ "\n" | i in 1..fix(M)];
        