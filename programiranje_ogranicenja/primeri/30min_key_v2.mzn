% 30. Primer: minimalni kljuc (v2)

/* Napomena: u ovoj verziji modela resavamo problem sa beskonacnom
    rekurzijom iz prethodne verzije (fajl min_key.mzn). Za opis problema
    i znacenje promenljivih pogledati komentare u tom fajlu */

int : n;
int : m;

array [1..m, 1..2] of set of 1..n: deps;

var set of 1..n: min_key;

/* Ovaj predikat proverava da li atribut attr funkcionalno zavisi od skupa atributa key.
   Za razliku od prethodne verzije, ovde imamo dodatni parametar depth koji oznacava
   dubinu do koje razvijamo stablo zavisnosti. Pod STABLOM ZAVISNOSTI atributa attr od 
   nekog skupa atributa key podrazumevamo stablo u cijim se cvorovima nalaze atributi:  
   u korenu je atribut attr, a sinovi svakog cvora su cvorovi u kojima se nalaze atributi od 
   kojih atribut u tom cvoru neposredno zavisi (na osnovu neke od zadatih zavisnosti). 
   U listovima ovog stabla se nalaze atributi iz skupa key. Pod STEPENOM ZAVISNOSTI atributa
   attr od skupa key podrazumevamo minimalnu dubinu nekog stabla zavisnosti attr od key. 
   Moze se dokazati da ako je attr zaista funkcionalno zavisan od skupa key, tada je 
   stepen zavisnosti attr od key najvise m, gde je m broj zadatih neposrednih zavisnosti.
   Za depth=0 proveravamo samo da li je attr u skupu key. Za depth > 0 proveravamo da 
   li je ili attr u skupu key ili postoji zadata zavisnost (deps[d,1], deps[d,2]) takva da je attr u 
   deps[d,2], a svi atributi iz deps[d,1] su funkcionalno zavisni od kljuca key do dubine najvise depth - 1.
   Na ovaj nacin imamo ogranicenu rekurziju koju je moguce raspisati. */ 
predicate depends_on(int : attr, var set of 1..n: key, int : depth)
 = attr in key \/  
       (depth > 0 /\ exists(d in 1..m) (attr in deps[d,2] /\ forall(a in deps[d,1]) (depends_on(a, key, depth-1))));
       
/* Sada zadajemo ogranicenje da je svaki atribut zavisan od min_key do dubine najvise m. Stablo 
   zavisnosti maksimalne dubine m sigurno postoji, ako je attr funkcionalno zavisan od min_key. */
constraint forall(attr in 1..n) (depends_on(attr, min_key, m));

solve minimize card(min_key);

