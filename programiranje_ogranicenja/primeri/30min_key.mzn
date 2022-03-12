% 30. Primer: Minimalni kljuc

/* Ovaj problem potice iz teorije baza podataka: 
   Neka je dat skup atributa neke tabele (oznacimo ih numericki sa 1..n)
   i neka je dat skup funkcionalnih zavisnosti oblika (A,B) gde su A i B
   podskupovi skupa atributa. Par (A,B) oznacava da je svaki atribut iz
   B funkcionalno zavisan od skupa atributa A.  Dodatno, podrazumevamo 
   da je svaki atribut funkcionalno zavisan od skupa atributa kome i sam
   pripada, kao i da je funkcionalna zavisnost tranzitivna: ako je atribut
   k funkcionalno zavisan od skupa B, a svi atributi iz B su funkcionalno 
   zavisni od  skupa A, tada je i k funkcionalno zavisan od A.
      
   Kljuc je svaki skup atributa K takav da su svi atributi funkcionalno 
   zavisni od K.
      
   Zadatak je odrediti kljuc najmanje moguce kardinalnosti.
   
   Za ovaj problem je dokazano da je NP-tezak.
*/

int : n;  % broj atributa
int : m; % broj zadatih zavisnosti

% skup zavisnosti se modeluje nizom, zato sto u MiniZinc-u elementi 
% skupa mogu biti samo jednostavni tipovi (npr. ne mozemo imati
% skup skupova, skup nizova i sl.). Takodje, kako MiniZinc ne podrzava
% uredjene parove, njih modelujemo nizovima duzine 2. Otuda cemo
% skup zavisnosti modelovati dvodimenzionim nizom, gde ce svaka
% vrsta imati po dva elementa: deps[i,1] i deps[i, 2] koji ce biti 
% podskupovi skupa 1..n. Par (deps[i,1], deps[i,2]) predstavljace
% zadatu funkcionalnu zavisnost
array [1..m, 1..2] of set of 1..n: deps;

% Promenljiva skupovnog tipa koja predstavlja minimalni kljuc
var set of 1..n: min_key;

% Predikat koji ispituje da li je atribut attr zavisan od kljuca key. 
% Ovaj predikat je rekurzivan, jer je potrebno da ili attr pripada
% kljucu key, ili da postoji neka zavisnost (deps[d,1],deps[d,2])
% takva da attr pripada deps[d,2], a sve vrednosti iz deps[d,1]
% su funkcionalno zavisne od kljuca key, sto proveravamo rekurzivno). 
predicate depends_on(int : attr, var set of 1..n: key) =
  attr in key \/ exists(d in 1..m) (attr in deps[d,2] /\ forall (a in deps[d,1]) (depends_on(a, key)));

% Zahtevamo da svi atributi zavise od min_key
constraint forall(attr in 1..n) (depends_on(attr, min_key));

% Cilj je minimizovati kardinalnost od min_key
solve minimize card(min_key);

/* VAZNA NAPOMENA: Ovaj model nece raditi zato sto ne postoji adekvatan
   izlaz iz rekurzije kod depend_on predikata. Naime, MiniZinc ce prilikom
   prevodjenja u FlatZinc pokusati da "raspise" ovaj predikat u okviru zadatog
   ogranicenja. To nece moci da uradi zato sto ce nakon raspisivanja imati
   opet depend_on() predikat koji ce morati dalje da raspisuje i td. 
   Zbog toga ce prilikom prevodjenja on potrositi stek i prijavice gresku.
   
   Na koji nacin se ovo moze prevazici mozete pogledati u drugoj 
   verziji modela: min_key_v2.mzn 
   
 */