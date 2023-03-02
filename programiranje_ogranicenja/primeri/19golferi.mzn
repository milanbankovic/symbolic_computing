% Primer 19: Drustveni golferi

include "globals.mzn";

int: m; % broj ekipa
int: n;  % velicina ekipe
int: p = (m*n - 1) div (n-1); % maksimalni broj nedelja
int: N = m*n;  % ukupan broj igraca

array [1..m, 1..n, 1..p] of var 0..N-1: x; 
var 1..p: P; % broj nedelja

% svake nedelje, svi razliciti
constraint forall(k in 1..P) (alldifferent([x[i,j,k] | i in 1..m, j in 1..n]));

% sortiramo igrace u svakoj fiksiranoj ekipi
constraint forall (i in 1..n, k in 1..P, j in 1..n-1) (x[i,j,k] < x[i,j+1,k]);

% pomocne promenljive
array [1..m, 1..n, 1..n, 1..p] of var 0..N^2 - 1: y;

% fiksiramo pomocne promenljive
constraint forall(i in 1..m, j1 in 1..n, j2 in 1..n, k in 1..P) (y[i,j1,j2,k] == N*x[i,j1,k] + x[i,j2,k]);

% i zahtevamo da sve budu razlicite
constraint alldifferent([y[i,j1,j2,k] | i in 1..m, j1 in 1..n, j2 in 1..n, k in 1..P where j1 < j2]);

% cilj je naci raspored za najveci moguci broj nedelja
solve maximize P;

output ["Num of weeks: \(P): \n"] ++ [show([x[i,j,k] | j in 1..n]) ++ if i == m then "\n" else " | " endif | k in 1..fix(P), i in 1..m];