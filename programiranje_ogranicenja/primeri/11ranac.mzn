int: n; % broj predmeta
int: C;  % kapacitet

% [var|par] set of <domen> : <ime>

set of int: Items = 1..n;  % skup predmeta {1,2,...,n}

array [Items] of int : Values;  % vrednosti predmeta
array [Items] of int : Sizes;    % velicine predmeta

array [Items] of var 0..1: x; % skup predstavljen nizom 0-1 vrednosti

/* NAPOMENA:  Korisnicki definisane funkcije se definisu na sledeci nacin:

function <povratni_tip> <naziv>(<arg1>,...,<argn>) = <izraz>;

Pritom, <povratni_tip> moze biti bilo koja deklaracija tipa koju smo vidjali
i kod deklaracije promenljivih. Takodje, moze biti i deklarisan sa var, sto
implicira da to sto funkcija vraca ne mora biti fiksirana vrednost, vec 
moze predstavljati izraz koji sadrzi domenske promenljive. Za argumente
vaze ista pravila kao kod procedura. <izraz> treba da bude istog tipa 
kao deklarisani povratni tip. 

Funkcije se koriste kada zelimo da uprostimo kompleksne izraze koji
se cesto pojavljuju u modelu. 
*/

% funkcija koja izracunava sumu koeficienata za predmete koji su u rancu
function var int : knapsack_sum(array[int] of var int: x, array[int] of int: c) = 
  sum(i in Items) (x[i] * c[i]);

% suma velicina ne sme da prekoraci kapacitet
constraint knapsack_sum(x, Sizes) <= C;

% cilj je maksimizacija sume vrednosti spakovanih predmeta
solve maximize knapsack_sum(x, Values);

output ["Set: "++show(x)++" with size: "++show(knapsack_sum(x,Sizes))++" and value: "++show(knapsack_sum(x,Values))];