% Primer 12. Golombov lenjir

include "globals.mzn";

int: k;
int: n;

array [1..k] of var 0..n: x;

% Uslovi poretka
constraint forall(i in 1..k-1) (x[i] < x[i+1]);

% Granicni uslovi
constraint x[k] == n;
constraint x[1] == 0;

% Razbijanje simetrije (sprecava osno simetricna resenja 
% time sto zahteva da prva dva budu na manjem 
% rastojanju od poslednja dva)
constraint k > 2 -> x[k] - x[k-1] > x[2] - x[1];

% Definisemo predikat koji zahteva da susedne razlike budu sve 
% razlicite medju sobom
predicate diffs_alldiff(array [int] of var int: x) =
   let { array [1..k, 1..k] of var 1..n: y; } in 
      forall(i,j in 1..k where i < j) (y[i,j] == x[j] - x[i]) /\
      alldifferent([y[i,j] | i,j in 1..k where i < j]);

/* NAPOMENA: U gornjem predikatu koriste se LOKALNE PROMENLJIVE. One se
    mogu uvesti u bilo kom izrazu i imaju sintaksu:
    
    let { var_decl1; var_decl2; ... } in <expr>
    
    Deklaracije mogu biti proizvoljne, s tim sto se u slucaju parametarskih deklaracija
    zahteva da imaju inicijalizator. Svaka deklaracija moze da koristi vec deklarisane
    lokalne promenljive iz prethodnih deklaratora. Ovako deklarisane promenljive
    mogu se koristiti samo u izrazu <expr>. Ako medju lokalnim promenljivama 
    postoje domenske promenljive, a let izraz je deo nekog ogranicenja, tada se
    te domenske promenljive ponasaju kao i sve druge promenljive, tj. resavac
    pokusava da pronadje vrednosti iz njihovih domena tako da ogranicenje bude
    zadovoljeno. Jedina razlika je sto te promenljive nisu vidljive u ostatku modela
    i nece moci biti prikazane na izlazu. 
*/      
                  
constraint diffs_alldiff(x);

solve satisfy;

  