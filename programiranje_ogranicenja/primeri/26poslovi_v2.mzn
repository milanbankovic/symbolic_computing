% Zadatak 26. Raporedjivanje poslova (druga verzija)

include "globals.mzn";

% PARAMETRI 

int: brIzvrsilaca;  % broj izvrsilaca
int: brPoslova;  % broj poslova

% Enumeratorski tip koji predstavlja razlicite resurse
enum Resursi;



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



% Ukupno vreme za zavrsetak svih poslova koju pokusavamo da minimizujemo
var 1..ukupnaDuzina: D;

% OGRANICENJA:

/* NAPOMENA: Ovde koristimo ogranicenje cumulative() deklarisano u globals.mzn. Ono ocekuje 
    cetiri parametara: prvi je niz promenljivih koje predstavljaju pocetna vremena poslova, 
    drugi je niz koji predstavlja duzine poslova, a treci je niz koji predstavlja potrebne kolicine
    datog resursa za svaki od poslova. Cetvrti parametar je broj koji predstavlja ukupnu raspolozivu
    kolicinu resursa koja ne sme biti prekoracena ni u jednom trenutku */

% Ogranicenje koje zahteva da ukupan broj poslova koji su aktivni u svakom casu ne predje broj izvrsilaca
constraint cumulative(vremePocetka, duzina, [1 | i in 1..brPoslova], brIzvrsilaca);

 % Ogranicenje koje za svaki resurs r zahteva da u svakom casu j ukupna kolicina resursa ne predje maksimalnu     
constraint forall(r in Resursi)
 (cumulative(vremePocetka, duzina, [potrebnaKolicina[i, r] | i in 1..brPoslova], ukupnaKolicina[r]));
   
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