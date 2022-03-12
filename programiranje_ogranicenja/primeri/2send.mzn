% Primer 2: SEND MORE MONEY

/* Nas prvi MiniZinc model */
/* Viselinijski komentari - kao u C-u */
% Jednolinijski komentari -- sve iza % se ignorise

/* MIniZinc modeli se najpre prevode u FlatZinc formu -- u pitanju je pojednostavljena 
   verzija MiniZinc jezika koja dopusta samo mali podskup MiniZinc konstrukcija i 
   ogranicenja koja su direktno podrzana od strane resavaca. Nakon prevodjenja se
   odgovarajuci FlatZinc model predaje resavacu koji onda resava problem i prikazuje
   resenje. 
*/

% Ukljucivanje drugih mzn fajlova, radi lakse organizacije slozenih modela -- include direktiva
% u ovom slucaju, ukljucujemo globals.mzn koji sadrzi deklaracije (ili definicije) globalnih ogranicenja
include "globals.mzn";

/* NAPOMENA: Svako globalno ogranicenje koje se koristi mora biti deklarisano ili definisano. Ako je
    samo deklarisano, tada ce prilikom prevodjenja na FlatZinc ogranicenje ostati takvo kakvo je, tj.
    u neizmenjenom obliku ce biti predato resavacu (ocekuje se da resavac podrzava takvo ogranicenje).
    Ako postoji definicija, tada se prilikom prevodjenja svaka instanca tog ogranicenja u modelu zamenjuje
    definicijom (tj. razlaze se na jednostavnija ogranicenja). 
*/

/* Slede deklaracije promenljivih za SEND MORE MONEY problem */
var 1..9: S;
var 0..9: E;
var 0..9: N;
var 0..9: D;
var 1..9: M;
var 0..9: O;
var 0..9: R;
var 0..9: Y;

/* NAPOMENA: Deklaracija promenljive (u najjednostavnijem obliku) je:

[par|var] <domen>: <id> [=<vrednost>];

Pritom, ako se ne navede ni par ni var, podrazumeva se par. U pitanju su dve razlicite 
vrste promenljivih:

- par: parametri; ovo zapravo nisu promenljive u pravom smislu, vec su u pitanju imenovane
  konstante. Njihova vrednost mora biti fiksirana u fazi prevodjenja na FlatZinc i u FlatZinc
  formi parametri vise ne postoje, vec su zamenjeni konkretnim vrednostima. Parametri daju
  fleksibilnost modelu, jer omogucavaju uniformni model za vise razlicitih instanci istog problema
  (koji je parametrizovan razlicitim parametrima)
- var: varijable: u pitanju su klasicne promenljive koje imaju domen i kojima ce resavac pokusati
  da pridruzi vrednost. Njima se obicno ne zadaje inicijalizacija, a ako se to ipak ucini, smatra se
  da je zadato ogranicenje koje namece tu vrednost toj promenljivoj. U daljem tekstu cemo 
  promenljive deklarisane sa var nazivati DOMENSKE PROMENLJIVE.

<domen> moze biti nesto od sledeceg:

- tip: int, float, enumeratorski tip, bool, string; u tom slucaju je domen ceo skup prirodnih brojeva,
  realnih brojeva, i sl.
- konacan skup vrednosti: npr. {1, 3, 5, 7} ili {0.1, 0.3, 0.5, 0.7}
- opseg vrednosti: 1..10  (isto sto i {1,2,...,10}) ili 0.1..1.0  (realni interval [0.1, 1.0])
- partitivni skup nekog drugog skupa: set of int, set of 1..10 (skup svih podskupova skupa {1,...,10}, i sl.  
*/

constraint alldifferent([S,E,N,D,M,O,R,Y]);

constraint 1000*S + 100*E + 10*N + D 
            + 1000*M + 100*O + 10*R + E
         == 10000*M + 1000*O + 100*N + 10*E + Y;

/* NAPOMENA: 
   Ogranicenja se zadaju iza kljucne reci constraint. Ogranicenje moze biti bilo koji logicki izraz koji se dobija bilo 
   primenom relacionih operatora na aritmeticke izraze, bilo primenom nekih posebnih predikata (npr. za 
   globalna ogranicenja, agregatne funkcije i sl).          
*/
   
/* NAPOMENA: 
Aritmeticki izrazi u MiniZinc-u se grade pomocu operatora, koji su nalik onima u C-u:
- aritmeticki +, -, *, / (realno deljenje), ^ (stepen)
- celobrojno deljenje i ostatak: div, mod
- relacioni: ==, !=, <=, >=, <, >
- logicki: /\, \/, ->, <-, <->, not

Takodje, u izrazima se mogu koristiti i ugradjene funkcije, poput: abs, pow, sin, cos, ln, ...
*/                                                                                                                                                                                                                                                                                                                                                                    
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      
solve satisfy;

/* NAPOMENA: 
solve stavka je obavezna i jedinstvena u svakom modelu. Njom se navodi cilj resavanja. Postoje tri opcije:

solve satisfy;  trazi bilo koje resenje
solve minimize <izraz>;  trazi resenje koje minimizuje izraz
solve maximize <izraz>; trazi resenje koje maksimizuje izraz
*/  

output ["\(S)\(E)\(N)\(D) + \(M)\(O)\(R)\(E) = \(M)\(O)\(N)\(E)\(Y)"];

/* NAPOMENA: Na kraju svakog modela ide output stavka. Njome se formatira ispis rezultata.
    Ako se ne navede, tada ce resavac ispisati vrednosti svih domenskih promenljivih, svaku 
    u posebnom redu. 
    
    Iza output stavke se navodi lista (u [] zagradama) stringova razdvojenih zarezima. U svakom
    od stringova moze se supstituisati vrednost promenljive ili izraza sintaksom \(<izraz>). 
    
    Alternativno, moze se koristiti show(x) funkcija koja vrednost promenljive x konvertuje u string.
    Stringovi se mogu nadovezivati operatorom ++.
*/ 

