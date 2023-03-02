% Primer 22. Raspored casova

include "globals.mzn";

int : brOdeljenja; % broj odeljenja
int : casovaDnevno; % broj slotova po danu
int : brDana;  % broj dana
int : ukupnoCasova = casovaDnevno*brDana; % ukupan broj slotova
int : brNastavnika;  % broj nastavnika

% podelaNastave predstavlja matricu parametara koja svakom odeljenju i svakom 
% casu tog odeljenja pridruzuje redni broj nastavnika koji drzi taj cas
array [1..brOdeljenja, 1..ukupnoCasova] of int : podelaNastave;

% sledeciUBloku je matrica parametara koja svakom odeljenju i svakom casu tog odeljenja
% pridruzuje redni broj casa koji za tim casom sledi u bloku (0 ako je to poslednji cas u bloku
% ili ako je samostalan cas, tj. nije deo bloka). 
array [1..brOdeljenja, 1..ukupnoCasova] of int : sledeciUBloku;

% Promenljiva raspored je trodimenziona matrica promenljivih pri cemu raspored[i,j,k] predstavlja 
% redni broj termina u kome i-ti nastavnik drzi k-ti cas j-tom odeljenju (u slucaju da i-ti nastavnik
% ne drzi k-ti cas j-tom odeljenju prema podeli nastave, tada vrednost ove promenljive nije bitna)
array [1..brNastavnika, 1..brOdeljenja, 1..ukupnoCasova] of var 1..ukupnoCasova : raspored;

% za svakog nastavnika, svi njegovi casovi moraju biti u razlicitim terminima (uslov u where je neophodan,
% da bismo izostavili promenljive raspored[i,j,k] za koje i-ti nastavnik ne drzi k-ti cas j-tom odeljenju)
constraint forall(i in 1..brNastavnika) 
 (alldifferent([raspored[i, j, k] | j in 1..brOdeljenja, k in 1..ukupnoCasova where podelaNastave[j,k] == i]));

% za svako odeljenje, svi njegovi casovi moraju biti u razlicitim terminima (isti komentar za uslov u where-u)
constraint forall(j in 1..brOdeljenja)
  (alldifferent([raspored[i,j,k] | i in 1..brNastavnika, k in 1..ukupnoCasova where podelaNastave[j,k] == i]));

% Uslovi za blokove: za svako odeljenje i svaki cas, ako za taj cas postoji sledeci u bloku (tj. nije poslednji
% u bloku i nije samostalan cas), taj cas ne sme biti poslednji u danu i njemu sledeci cas mora biti 
% rasporedjen da ide odmah u sledecem terminu
constraint forall(j in 1..brOdeljenja, k in 1..ukupnoCasova)
 (let { int : ks = sledeciUBloku[j,k]; } in 
            ks != 0 -> let { int : i = podelaNastave[j,k]; int : is = podelaNastave[j,ks];} in
                                     raspored[i,j,k] mod casovaDnevno != 0 /\ 
                                     raspored[is,j,ks] == raspored[i,j,k] + 1);

% matrica pomocnih promenljivih, gde rbrCasaUDanu[i,j,k]  casu raspored[i,j,k] pridruzuje redni broj 
% casa u danu
array[1..brNastavnika, 1..brOdeljenja, 1..ukupnoCasova] of var 1..casovaDnevno : rbrCasaUDanu;

% Uslov kojim se promenljiva rbrCasaUDanu[i,j,k] vezuje za raspored[i,j,k] (if naredba je zbog specijalnog
% slucaja, kada je poslednji cas u danu, tada je raspored[i,j,k] mod casovaDnevno == 0, a treba da bude
% jednako casovaDnevno). 
constraint forall(i in 1..brNastavnika, j in 1..brOdeljenja, k in 1..ukupnoCasova) 
 (rbrCasaUDanu[i,j,k] == (raspored[i,j,k] - 1) mod casovaDnevno + 1);

% Uslov kojim se zadaje da za svakog nastavnika, najvise dve promenljive u matrici rbrCasaUDanu za tog
% fiksiranog nastavnika mogu imati vrednost 1 (tj. najvise dva casa koja on drzi mogu biti prvi casovi)
constraint forall(i in 1..brNastavnika)
   (atmost(2, [rbrCasaUDanu[i,j,k] | j in 1..brOdeljenja, k in 1..ukupnoCasova where podelaNastave[j,k] == i], 1));

% matrica pomocnih promenljivih, gde rbrDana[i,j,k] casu raspored[i,j,k] pridruzuje broj dana kada se odrzava
array[1..brNastavnika, 1..brOdeljenja, 1..ukupnoCasova] of var 1..brDana: rbrDana;

% Uslovi kojim se postize da rbrDana[i,j,k] bude jednak rednom broju dana kada se odrzava k-to cas j-tom 
% odeljenju (koji drzi i-ti nastavnik)
constraint forall(i in 1..brNastavnika, j in 1..brOdeljenja, k in 1..ukupnoCasova)
  (rbrDana[i,j,k] == (raspored[i,j,k] - 1) div casovaDnevno + 1);

% Za svakog nastavnika, zadajemo ogranicenje global_cardinality, gde zahtevamo da svaku od vrednosti {1,2,3,4,...,brDana}
% uzme bar jedna (a najvise casovaDnevno) promenljiva. Kao prvi argument zadajemo niz promenljivih 
% (sve promenljive rbrDana[i,j,k] za to fiksirano i, pri cemu upravo taj nastavnik drzi k-ti cas j-tom odeljenju)
% drugi argument je niz vrednosti {1,2,3,...,brDana}, treci je niz donjih granica za te vrednosti {1,1,1,...,1}, a 
% poslednji je niz gornjih granica {casovaDnevno, casovaDnevno,...}.
constraint forall(i in 1..brNastavnika) 
     (global_cardinality([rbrDana[i,j,k] | j in 1..brOdeljenja, k in 1..ukupnoCasova where podelaNastave[j,k] == i], 
                                  [j | j in 1..brDana], [1 | j in 1..brDana], [casovaDnevno | j in 1..brDana])); 

% Matrica rasporedPregledno sluzi za pregledniji prikaz dobijenog resenja. Vrednost rasporedPregledno[j,t,s] predstavlja
% redni broj casa j-tog odeljenja koji je rasporedjen s-tog casa t-tog dana. 
array [1..brOdeljenja, 1..brDana, 1..casovaDnevno] of var 1..ukupnoCasova : rasporedPregledno;

% Uslov kojim se zadaje vrednost rasporedPregledano[i,j,k]
constraint forall(j in 1..brOdeljenja, t in 1..brDana, s in 1..casovaDnevno) 
 (let { var 1..ukupnoCasova: k; var 1..brNastavnika : i = podelaNastave[j, k];} in rasporedPregledno[j,t,s] == k <-> raspored[i,j,k] == t*casovaDnevno + s);


 solve satisfy;
 
 % Prikazujemo promenljivu rasporedPregledno, za svako odeljenje. Primetimo da se u generatoru trojke (j,s,t) redjaju leksikografski, tj. najbrze se menja t, pa zatim s, a najsporije j. Otuda 
 % ce se prikaz vrsiti najpre za prvo odeljenje i prvi cas (redom po danima), pa onda za drugi cas, i td. pa tek onda za drugo odeljenje, na isti nacin, i td. 
 output [show(rasporedPregledno[j,t,s]) ++ if t == brDana then if s == casovaDnevno then "\n\n\n" else "\n" endif else " " endif | j in 1..brOdeljenja, s in 1..casovaDnevno, t in 1..brDana];
 
