% Domaci zadatak 43.: Raspored ispita

include "globals.mzn";

int: m; % broj grupa
int: n; % broj ispita
int: N; % trajanje ispitnog roka
int: r; % maksimalni broj ispita po danu

% Matrica koja govori koja grupa polaze koje ispite
array [1..m, 1..n] of bool : E; 

% Raspored: R[j] oznacava dan kada se j-ti ispit odrzava
array [1..n] of var 1..N: R; 

% Ni jedna grupa ne sme polagati dva ili vise ispita istog dana
% (tj. dani u kojima neka grupa polaze svoje ispite moraju biti
%  svi razliciti)
constraint forall(i in 1..m) 
  (alldifferent([R[j] | j in 1..n where E[i,j] == true]));
  
% Predikat oznacava da i-ta grupa ima ispit k-tog dana
predicate group_has_exam_on_day(int : i, int : k) = 
  exists(j in 1..n) (E[i,j] == true /\ R[j] == k);  

% Ogranicenje zahteva da ni jedna grupa nema ispite 
% tri uzastopna dana    
constraint forall(i in 1..m, k in 1..N-2) 
  (not group_has_exam_on_day(i, k) \/
   not group_has_exam_on_day(i, k+1) \/
   not group_has_exam_on_day(i, k+2));
  
% Ogranicenje zahteva da u nizu R, svaka od vrednosti iz 1..N se pojavljuje
% najmanje 0 a najvise r puta. Time se obezbedjuje da ni jednog dana ne
% bude vise od r ispita. 
constraint global_cardinality(R, [k | k in 1..N], [0 | k in 1..N], [r | k in 1..N]);

% Alternativno:
%constraint forall(i in 1..N) (sum([1 | j in 1..n where R[j] = i]) <= r);

solve satisfy;

output [show(R)];