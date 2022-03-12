include "globals.mzn";

enum Moves = { up, down, left, right };

% PARAMETRI

int : m;  % broj vrsta
int : n;  % broj kolona
int : N; % broj poteza

array [1..m,1..n] of 0..1: wall;  % pozicije zidova
array [1..m,1..n] of 0..1: home; % pozicije odredista
array [1..m,1..n] of 0..1: start; % pocetna pozicija kutija

% pocetne koordinate Sokobana
int: Is;
int: Js;

% PROMENLJIVE

array [0..N, 1..m, 1..n] of var 0..1: box; % pozicije kutija nakon k-tog poteza

% koordinate Sokobana nakon k-tog poteza
array [0..N] of var 1..m: I; 
array [0..N] of var 1..n: J;
  
array [1..N] of var Moves : move;

% USLOVI POCETNOG STANJA

constraint I[0] == Is;
constraint J[0] == Js;
constraint forall(i in 1..m, j in 1..n) (box[0,i,j] == start[i,j]);

% PREDUSLOVI ZA POTEZE

predicate move_up_precondition(int : k) = 
  k > 0 /\ I[k - 1] > 1 /\ wall[I[k-1] - 1, J[k - 1]] == 0 /\
  (box[k-1,I[k-1]-1, J[k-1]]  == 1 -> (I[k-1] > 2 /\ box[k-1,I[k-1]-2,J[k-1]] == 0 /\ wall[I[k-1]-2, J[k-1]] == 0));

constraint forall(k in 1..N) (move[k] == up -> move_up_precondition(k));  

predicate move_down_precondition(int : k) = 
   k > 0 /\ I[k - 1] < m /\ wall[I[k-1]+1, J[k-1]] == 0 /\
   (box[k-1,I[k-1]+1, J[k-1]] == 1 -> (I[k-1] < m - 1 /\ box[k-1, I[k-1]+2,J[k-1]] == 0 /\ wall[I[k-1]+2,J[k-1]] == 0));      

constraint forall(k in 1..N) (move[k] == down -> move_down_precondition(k));

 predicate move_left_precondition(int : k) = 
  k > 0 /\ J[k-1] > 1 /\ wall[I[k-1],J[k-1]-1] == 0 /\
  (box[k-1,I[k-1],J[k-1]-1] == 1 -> (J[k-1] > 2 /\ box[k-1,I[k-1],J[k-1]-2] == 0 /\ wall[I[k-1],J[k-1]-2] == 0));                                                                        
  
constraint forall(k in 1..N) (move[k] == left -> move_left_precondition(k));

predicate move_right_precondition(int: k) = 
   k > 0 /\ J[k-1] < n /\ wall[I[k-1],J[k-1]+1] == 0 /\ 
   (box[k-1,I[k-1],J[k-1]+1] == 1 -> (J[k-1] < n - 1 /\ box[k-1, I[k-1], J[k-1]+2] == 0 /\ wall[I[k-1],J[k-1]+2] == 0));  
  
constraint forall(k in 1..N) (move[k] == right -> move_right_precondition(k));
    
% EFEKTI POTEZA 
  
predicate move_up_effect(int : k) = 
  k > 0 /\ I[k] == I[k-1]-1 /\ J[k] == J[k-1] /\ 
  (box[k-1,I[k-1]-1,J[k-1]] == 0 -> forall(i in 1..m, j in 1..n) (box[k,i,j] == box[k-1,i,j])) /\
  (box[k-1,I[k-1]-1,J[k-1]] == 1 -> forall(i in 1..m, j in 1..n) (box[k,i,j] == if (i != I[k-1] - 1 /\ i != I[k-1] - 2) \/ j != J[k-1] then box[k-1,i,j] else 1 - box[k-1,i,j] endif));

constraint forall(k in 1..N) (move[k] == up -> move_up_effect(k));

predicate move_down_effect(int : k) = 
  k > 0 /\ I[k] == I[k-1]+1 /\ J[k] == J[k-1] /\
  (box[k-1, I[k-1]+1,J[k-1]] == 0 -> forall(i in 1..m, j in 1..n) (box[k,i,j] == box[k-1,i,j])) /\
  (box[k-1, I[k-1]+1,J[k-1]] == 1 -> forall(i in 1..m, j in 1..n) (box[k,i,j] == if (i != I[k-1]+1 /\ i != I[k-1]+2) \/ j != J[k-1] then box[k-1,i,j] else 1 - box[k-1,i,j] endif));

constraint forall(k in 1..N) (move[k] == down -> move_down_effect(k));

predicate move_left_effect(int: k) = 
 k > 0 /\ I[k] == I[k-1] /\ J[k] == J[k-1] - 1 /\
 (box[k-1, I[k-1], J[k-1]-1] == 0 -> forall(i in 1..m, j in 1..n) (box[k,i,j] == box[k-1,i,j])) /\
 (box[k-1, I[k-1], J[k-1]-1] == 1 -> forall(i in 1..m, j in 1..n) (box[k,i,j] == if i != I[k-1] \/ (j != J[k-1]-1 /\ j != J[k-1]-2) then box[k-1,i,j] else 1 - box[k-1,i,j] endif));
 
constraint forall(k in 1..N) (move[k] == left -> move_left_effect(k));

predicate move_right_effect(int: k) =
 k > 0 /\ I[k] == I[k-1] /\ J[k] == J[k-1] + 1 /\
 (box[k-1, I[k-1], J[k-1]+1] == 0 -> forall(i in 1..m, j in 1..n) (box[k,i,j] == box[k-1,i,j])) /\
 (box[k-1, I[k-1], J[k-1]+1] == 1 -> forall(i in 1..m, j in 1..n) (box[k,i,j] == if i != I[k-1] \/ (j != J[k-1]+1 /\ j != J[k-1]+2) then box[k-1,i,j] else 1 - box[k-1,i,j] endif));

constraint forall(k in 1..N) (move[k] == right -> move_right_effect(k));

% ZAVRSNI USLOVI
constraint forall(i in 1..m, j in 1..n) (box[N, i, j] == home[i,j]);

solve satisfy;

output [show(move)];