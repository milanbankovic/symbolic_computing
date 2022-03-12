% Primer 6: magicni kvadrat (kraca verzija)

/* NAPOMENA: U ovom primeru demonstriramo opise listi (list comprehension),
    kao i agregatne funkcije koje omogucavaju kompaktno zapisivanje slozenih
    uslova. */

include "globals.mzn";

array[1..4,1..4] of var 1..16: x;

/* NAPOMENA:  Opis liste ima oblik:

[ <izraz> | <lista_generatora> ]

Generatori se razdvajaju zarezima. Svaki generator je oblika:

<id1>,<id2>,...,<idn> in <lista_ili_skup> [where <uslov>]

<lista_ili_skup> je izraz koji se moze izracunati u vreme prevodjenja
(tj. ne sadrzi domenske promenljive) i vrednost mu je lista ili konacan
skup. Promenljive <id1>,<id2>,... redom uzimaju vrednosti iz te
liste ili skupa i formiraju n-torke (u leksikografskom poretku, tj.
poslednja promenljiva najbrze menja vrednost). Ako postoji 
opciona klauza where <uslov>, tada se eliminisu one n-torke koje
ne zadovoljavaju uslov. Uslov je izrazen u terminima promenljivih
<id1>,<id2>,..., a moze koristiti i promenljive uvedene u prethodnim
generatorima u tom opisu liste. 

<izraz> na kraju za svaku n-torku koja ispunjava dati uslov proizvodi
odgovarajucu vrednost. U izrazu mogu figurisati promenljive <id1>,<id2>,...

Ako <izraz> pominje domenske promenljive, tada je rezultujuca lista zapravo
lista domenskih promenljivih. U suprotnom je lista koja se izracunava u fazi
prevodjenja i prevodi se u listu konstanti.  Primeri:

[i + j | i,j in 1..10 where i < j]  % lista zbirova i + j, gde je 1 <= i < j <= 10
[x[j] | j in 1..10 where i mod 2 == 0]  % niz promenljivih x[2], x[4], ..., x[10]
[x[i,j] | i in 1..5, j in 1..10]  % indeksi i i j su iz razlicitih opsega

NAPOMENA: Agregatne funkcije su funkcije koje se primenjuju na niz, a vracaju
skalarnu vrednost. Postoje sledece ugradjene agregatne funkcije:

ARITMETICKE (primenjuju se na nizove brojeva i vracaju broj): 
- sum(), max(), min(), product()

LOGICKE (primenjuju se na liste bool vrednosti i vracaju bool:
- forall(): vraca true ako su svi tacni
- exists(): vraca true ako je bar jedan tacan
- xorall(): vraca true ako je neparno njih tacno
- iffall(): vraca true ako je parno njih tacno

Kada se agregatne funkcije primenjuju na parametre ili konstante (ili izraze 
koji se mogu izracunati u fazi prevodjenja, tj. ne sadrze domenske promenljive),
tada je rezultat konstanta koja se izracunava u fazi prevodjenja. Kada se 
agregatne funkcije primenjuju na izraze koji sadrze domenske promenljive,
tada je rezultat izraz (aritmeticki ili logicki) koji sadrzi domenske promenljive.
Ovo omogucava kreiranje slozenih ogranicenja. Na primer, ako je x niz 
domenskih promenljivih duzine 10, tada izraz: 

forall([x[i] != x[j] | i, j in 1..10, i < j])

kreira konjunkciju razlicitosti po parovima x[i]!=x[j]. Dodavanjem kljucne 
reci constraint ispred ovog izraza zahtevacemo da svi elementi niza budu
medjusobno razliciti. Slicno:

constraint y = sum([x[i] | i in 1..10 where i mod 2 == 0]);

je ekvivalentno sa constraint y = x[2] + x[4] + ... + x[10]; tj. kreira se
izraz koji se izjednacava sa y. 
*/


constraint forall([sum( [x[i,j] | j in 1..4] ) == 34 | i in 1..4]);
constraint forall([sum( [x[i,j] | i in 1..4] ) == 34 | j in 1..4]);                   
constraint sum([x[i,i] | i in 1..4]) == 34;
constraint sum([x[i, 4 - i + 1] | i in 1..4]) == 34;                 
constraint alldifferent([x[i,j] | i,j in 1..4]);

constraint x[1,2] = 12;
constraint x[2,2] = 8;
constraint x[2,3] = 15;
constraint x[3,1] = 7;
constraint x[3,3] = 2;
constraint x[4,1] = 4;
constraint x[4,4] = 11;                                          
                                                 
solve satisfy;

/* NAPOMENA: Uslovni izraz ima sledecu sintaksu:

   if <uslov> then <izraz1> else <izraz2> endif 
   
Ako je <uslov> logicki tacan, tada ceo uslovni izraz ima vrednost 
izraza1, a u suprotnom ima vrednost izraza2. Slicno kao i ranije,
ako izrazi sadrze domenske promenljive, tada se ovaj izraz 
transformise u ogranicenja, dok se u suprotnom izraz izracunava
i zamenjuje konstantom u fazi prevodjenja. 
*/

/* NAPOMENA: Funkcija show_int(n,x) je formatirana verzija funkcije show() i 
takodje konvertuje vrednost x u string, ali se konstantom n zadaje sirina
zapisa. Poravnanje zavisi od znaka broja n (ako je pozitivan onda desno, 
a u suprotnom levo). */

output [show_int(2,x[i,j])++ if j == 4 then "\n" else "   " endif | i, j in 1..4];   