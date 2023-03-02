% Primer 14. Svi intervali

include "globals.mzn";

array [0..11] of var 0..11: x;

/* NAPOMENA: Kada se domenskoj promenljivoj zada inicijalizacija:

var <tip>: y = <expr>;

to je isto kao da smo rekli:

var <tip>: y;

constraint y == <expr>;

*/

array [1..11] of var 1..11: y = [abs(x[i] - x[i - 1]) | i in 1..11];

constraint alldifferent(x);
constraint alldifferent(y);

solve satisfy;

output [show(x)];