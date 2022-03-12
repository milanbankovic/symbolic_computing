% Primer 7: Latinski kvadrat
include "globals.mzn";

/* NAPOMENA: U ovom primeru demonstriramo razdvajanje podataka od modela. 
    Podaci se cuvaju u odvojenom fajlu sa ekstenzijom dzn. U tom fajlu su dozvoljene
    samo dodele vrednosti promenljivama (kojima nije dodeljena vrednost u mzn 
    fajlu). Sada se parametri u mzn fajlu ostavljaju neinicijalizovani, cime se isti
    model koristiti u sprezi sa razlicitim podacima u vise razlicitih dzn fajlova. 
*/

int : n;  % dimenzija latinskog kvadrata (parametar koji biramo u dzn fajlu)

set of int: DOM = 1..n;  % DOM je parametar skupovnog tipa, cija je vrednost {1,2,...,n}

/* NAPOMENA: Skupovne promenljive se definisu na sledeci nacin:

[par|var] set of <domen>: <id> [=<inicijalizator>]; 

par i var imaju isti smisao kao i ranije (ako se izostavi, par se podrazumeva). 

<domen> moze biti int, float, enumeratorski tip, kao i opseg celih ili realnih brojeva ili
enumeratora.  

Domen promenljive bice skup svih podskupova skupa <domen>. Ako je <domen> 
konacan, tada ce i domen promenljive <id> biti konacan. 

Inicijalizator je skupovna konstanta: ili oblika {v1,v2,...,vn} ili interval a..b. 

Ukoliko koristimo var (tj. hocemo domensku skupovnu promenljivu), tada <domen>
moze biti samo opseg int-ova ili enumeratorski tip (vise o enumeratorskim 
tipovima kasnije).  Dakle, domenske promenljive skupovnog tipa moraju imati 
konacan domen.

Parametri skupovnog tipa koji su inicijalizovani celobrojnim opsegom mogu se
koristiti kao indeksni skupovi u nizovima. 

Nad skupovima su definisani operatori:

x in S   % x je element skupa S
S1 subset S2  % S1 je podskup od S2
S1 union S2  % unija
S1 intersect S2 % razlika
S1 diff S2 % razlika S1 \ S2
S1 symdiff S2 % simetricna razlika
card(S) % vraca kardinalnost skupa S

*/

array[DOM, DOM] of var DOM : x;  % matrica domenskih promenljivih x[i,j] gde su domeni i skupovi indeksa jednaki {1,2,...,n}

array[DOM,DOM] of int: p;  % parametar p je matrica predefinisanih (datih) vrednosti (0 ako vrednost nije data)

% Slede alldiff ogranicenja po kolonama i po vrstama. Indeksi iteriraju kroz skup DOM.
constraint forall(i in DOM) 
                  (alldifferent([x[i,j] | j in DOM]));
constraint forall(j in DOM)
                  (alldifferent([x[i,j] | i in DOM]));

% Uslov: ako je vrednost p[i,j] data (tj. nije 0), tada promenljiva x[i,j] mora uzeti tu vrednost.
% Ovde koristimo implikaciju ->
constraint  forall(i,j in DOM) (p[i,j] != 0 -> x[i,j] == p[i,j]);                                  
                                                                                                            
solve satisfy;

output [show(x[i,j]) ++ if j == n then "\n" else "  " endif | i,j in DOM];                 
         