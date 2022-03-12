% Primer 4: Nekonzistentan problem
var 1..2: x;
var 1..2: y;
var 1..2: z;

constraint x != y;
constraint y != z;
constraint x != z;

solve satisfy;
