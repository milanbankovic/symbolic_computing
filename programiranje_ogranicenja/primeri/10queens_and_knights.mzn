include "globals.mzn";

int  : n;  % dimenzija table
int : m = n div 2; % broj kraljica (skakaca)

array[1..m] of var 1..n: xq;
array[1..m] of var 1..n: yq;
array[1..m] of var 1..n: xn;
array[1..m] of var 1..n: yn;

% ne smeju dve figure biti na istoj dijagonali
predicate no_diag(var int: x1, var int: y1, var int: x2 ,var int: y2) =
   abs(x1 - x2) != abs(y1 - y2);

% ne smeju dve figure biti u L polozaju
predicate no_L(var int: x1, var int: y1, var int: x2 ,var int: y2) =
  abs((x1 - x2)*(y1 - y2)) != 2;

/* NAPOMENA:  Predikat assert(<logicki_izraz>, <string>)  je ugradjeni predikat 
   koji vraca istu vrednost koju vraca i logicki izraz koji mu predajemo, s tim sto 
   ako je taj izraz netacan ispisuje <string> na izlazu. Koristan je za proveravanje
   statickih uslova nad parametrima (kada se vrednosti parametara fiksiraju 
   u odvojenom dzn fajlu). Zadaje se kao constraint, tako da ce minizinc odmah
   prijaviti gresku ako uslov nije ispunjen. */
   
% uslov: dimenzija table mora biti parna. 
constraint assert(n mod 2 == 0, "Dimenzija mora biti parna");

% da se kraljice ne napadaju
constraint alldifferent(xq);
constraint alldifferent(yq);
constraint forall(i,j in 1..m where i < j) (no_diag(xq[i],yq[i],xq[j],yq[j]));

% da kraljice ne napadaju skakace
constraint forall(i,j in 1..m) (xq[i] != xn[j] /\ yq[i] != yn[j] /\ no_diag(xq[i],yq[i], xn[j], yn[j]));

% da skakaci ne napadaju kraljice
constraint forall(i,j in 1..m) (no_L(xn[i], yn[i], xq[j], yq[j]));

% da se skakaci ne napadaju
constraint forall(i,j in 1..m where i < j) (no_L(xn[i], yn[i], xn[j], yn[j]));


% da su skakaci na razlicitim poljima
constraint forall(i,j in 1..m where i < j) (xn[i] != xn[j] \/ yn[i] != yn[j]);

% razbijanje simetrija
constraint forall(i in 1..m-1) (xq[i] < xq[i + 1]);
constraint forall(i in 1..m-1) (xn[i] < xn[i + 1] \/ (xn[i] == xn[i + 1] /\ yn[i] < yn[i + 1]));

solve satisfy;

% pomocni predikat koji ispituje da li je neka kraljica (ili neki skakac) na polju i,j
predicate on_square(array [int] of var int: x, array [int] of var int: y, int : i, int: j) =
   exists(k in 1..m) (x[k] == i /\ y[k] == j); 

output [if fix(on_square(xq, yq, i, j))  then "K" else  if fix(on_square(xn,yn, i, j)) then "N" else " " endif endif ++ 
             if j == n then " |\n-----------------------\n" else " |" endif |
             i, j in 1..n];
