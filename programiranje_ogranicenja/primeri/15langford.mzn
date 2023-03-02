% Langfordovi parovi

include "globals.mzn";

int: n; % broj brojeva

array [1..n, 1..2] of var 1..2*n: x;

% svi na razlicitim pozicijama 
constraint alldifferent([x[i,j] | i in 1..n, j in 1..2]);

% uslovi za rastojanja izmedju istih brojeva
constraint forall(i in 1..n) (x[i,2] - x[i,1] == i + 1);

solve satisfy;

% pomocni niz promenljivih za prikaz 
array [1..2*n] of var 1..n: v;

% v[k] je jednako nekom broju akko se ili prva ili druga pojava tog
% broja nalazi na poziciji k
 constraint forall(k in 1..2*n) 
    (x[v[k],1] == k \/ x[v[k],2] == k);

output [show(v)];