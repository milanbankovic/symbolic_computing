% Zadatak 26. Raporedjivanje poslova

% PARAMETRI 

int: brIzvrsilaca;  % broj izvrsilaca
int: brPoslova;  % broj poslova

% Enumeratorski tip koji predstavlja razlicite resurse
enum Resursi;

/* NAPOMENA:  Enumeratorski tip se definise na sledeci nacin:

enum <naziv_tipa> [ = { <enumerator1>, <enumerator2> , ... }] ;

gde je <naziv_tipa> identifikator koji predstavlja naziv uvedenog tipa, a <enumerator1>,<enumerator2>,...
su identifikatori koji predstavljaju vrednosti tog tipa. Enumeratori se ne moraju navesti na mestu gde se
uvodi sam tip, vec se mogu definisati kasnije (tipicno, u dzn fajlu, sto omogucava da vrednosti enum 
tipa budu zavisne od podataka). 

Enum tip se ponasa slicno kao celobrojni interval -- njegovi enumeratori se mogu uporedjivati (oni 
koji su prvi navedeni su manji od onih koji su navedeni kasnije), a mozemo definisati i intervale, 
npr:

enum Tip = { Prvi, Drugi, Treci, Cetvrti };

sada Prvi..Treci  predstavlja interval {Prvi, Drugi, Treci}. 

Enum tip se moze koristiti kao tip promenljive:

var Tip: x;    % x moze biti Prvi, Drugi, Treci ili Cetvrti
var Prvi..Treci: y;  % y moze biti Prvi, Drugi ili Treci

Takodje, moze se koristiti kao indeksni skup za nizove:

array[Tip] of int x; % imamo x[Prvi], x[Drugi], ...

Broj enumeratora enum tipa se uvek moze dobiti sa card(Tip). 
*/

% Duzine poslova
array [1..brPoslova] of int: duzina;

% Ukupna duzina poslova
int : ukupnaDuzina = sum(duzina);

% Staticki uslov za parametre: sve duzine moraju biti pozitivne
constraint forall(i in 1..brPoslova) (assert(duzina[i] > 0, "Duzina posla mora biti veca od nule"));

% Matrica zavisnosti: zavisiOd[i,j] je true ako i-ti posao zavisi od j-tog
array [1..brPoslova, 1..brPoslova] of bool : zavisiOd; 

% Za svaki resurs imamo njegovu ukupnu kolicinu
array [Resursi] of int: ukupnaKolicina;

% Staticki uslov: kolicine moraju biti pozitivne
constraint forall(r in Resursi) (assert(ukupnaKolicina[r] > 0, "Ukupna kolicina mora biti pozitivna"));

% Matrica potrebnih resursa: potrebnaKolicina[i,r] oznacava koliko resursa r je potrebno i-tom poslu
array [1..brPoslova, Resursi] of int: potrebnaKolicina;

% PROMENLJIVE:

% Glavne promenljive koje oznacavaju u kom casu pocinje svaki od poslova
array [1..brPoslova] of var 1..ukupnaDuzina: vremePocetka;

% Pomocne promenljive logickog tipa: posaoTraje[i,j] oznacava da li je i-ti posao u toku u j-tom casu
array[1..brPoslova, 1..ukupnaDuzina] of var bool: posaoTraje;

% Ukupno vreme za zavrsetak svih poslova koju pokusavamo da minimizujemo
var 1..ukupnaDuzina: D;

% OGRANICENJA:

% Ogranicenje koje definise vrednosti pomocnih promenljivih
constraint forall(i in 1..brPoslova, j in 1..ukupnaDuzina)
   (posaoTraje[i,j] <-> (vremePocetka[i] <= j /\ j < vremePocetka[i] + duzina[i]));
   
   
% Ogranicenje koje zahteva da ukupan broj poslova koji su aktivni u svakom casu ne predje broj izvrsilaca
constraint forall(j in 1..ukupnaDuzina)
  (sum(i in 1..brPoslova) (bool2int(posaoTraje[i,j])) <= brIzvrsilaca);
  
/* NAPOMENA: funkcija bool2int() konvertuje bool vrednost u ceo broj (true u 1, false u 0 */  
  
% Ogranicenje koje za svaki resurs r zahteva da u svakom casu j ukupna kolicina resursa ne predje maksimalnu  
constraint forall(r in Resursi, j in 1..ukupnaDuzina)
  (sum(i in 1..brPoslova) (bool2int(posaoTraje[i,j]) * potrebnaKolicina[i,r]) <= ukupnaKolicina[r]);
 
% Ogranicenje koje za svaka dva razlicita posla zahteva da ako i1 zavisi od i2, tada njegovo vreme
% pocetka mora biti nakon zavrsetka i2. 
constraint forall (i1, i2 in 1..brPoslova where i1 != i2)
  (zavisiOd[i1, i2] -> vremePocetka[i1] >= vremePocetka[i2] + duzina[i2]);
 
% Vreme zavrsetka svih poslova je najvise D
constraint forall(i in 1..brPoslova)
 (vremePocetka[i] + duzina[i] - 1 <= D);
 
% Potrebno je naci najmanje takvo D za koje je sve ovo moguce
solve minimize D;

output [show(vremePocetka[i]) ++ ", " | i in 1..brPoslova];