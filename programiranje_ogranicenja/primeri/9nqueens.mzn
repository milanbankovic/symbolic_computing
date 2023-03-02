include "globals.mzn";

int  : n;  % dimenzija table

array[1..n] of var 1..n: x;


/* NAPOMENA: U ovom primeru upoznajemo se sa korisnicki definisanim predikatima
   koji predstavljaju mehanizam za definisanje proizvoljnih ogranicenja.
   
   Predikat se deklarise/definise na sledeci nacin:
   
predicate <ime>(<arg1>,...,<argn>) [= <logicki_izraz>];

Ako se inicijalizacija ne zada, tada je u pitanju deklaracija. To znaci da se ogranicenje
moze koristiti u modelu, ali prilikom prevodjenja na FlatZinc, ono ce ostati takvo
kakvo je i ocekuje se od resavaca da ga prepoznaje (u suprotnom, prijavice se greska).
Deklaracije se koriste za globalna ogranicenja koja su poznata resavacima i nalaze se
u globals.mzn. 

Ako se inicijalizacija zada, onda se odgovarajuci logicki izraz koristi kao definicija predikata.
Prilikom prevodjenja na FlatZinc, sve instance ovog predikata u ogranicenjima ce se 
zameniti odgovarajucom instancom logickog izraza (zamenom formalnih argumenata
stvarnim). 

Svaki od argumenata je deklaracija promenljive i ima istu sintaksu (moze ukljucivati i
skupove i nizove). Jedina relaksacija je to sto indeksni skupovi ne moraju biti konacni
intervali celih brojeva, vec moze biti i tip int. Ovim se postize da isti predikat kao 
argument moze da primi nizove sa razlicitim indeksnim skupovima. 
*/

% predikat no_diag(x,i,j) zahteva da elementi x[i] i x[j] nisu na istoj "dijagonali"
predicate no_diag(array [int] of var int: x, int: i, int: j) =
   abs(x[i] - x[j]) != abs(i - j);

constraint alldifferent(x);

constraint forall(i,j in 1..n where i < j) (no_diag(x, i, j));

solve satisfy;

/* NAPOMENA: Ugradjena funkcija fix() vrsi neku vrstu konverzije iz var u par. Zapravo, 
   mesta gde MiniZinc dozvoljava upotrebu domenskih promenljivih (i izraza koji ih
   ukljucuju) je znatno uzi od mesta gde se mogu koristiti parametri (koji se u fazi 
   prevodjenja prevode u konstantne vrednosti). Ponekad ipak mi znamo da promenljiva,
   iako je deklarisana sa var, ima fiksiranu vrednost (npr. prilikom ispisa rezultata, kada
   je resenje vec nadjeno i svim promenljivama vrednosti su vec fiksirane). U takvim 
   situacijama mozemo izraz koji sadrzi domenske promenljive staviti u fix() funkciju.
   Ovo omogucava da model prodje kompilaciju u FlatZinc, ali moze doci do dinamicke
   greske ako se ispostavi da vrednost izraza nije fiksirana u fazi izvrsenja. Zato treba
   oprezno koristiti ovu funkciju.
*/
output [if fix(x[i]) == j then "K" else " " endif ++ 
             if j == n then " |\n-----------------------\n" else " |" endif |
             i, j in 1..n];
