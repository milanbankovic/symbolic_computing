% Primer 11. Ranac (v2)

/* U ovoj verziji modela skup predmeta koji su spakovani u ranac
   modelujemo upravo skupom -- podskupom skupa svih predmeta. 
   U MiniZinc-u promenljive ciji je domen skup svih podskupova konacnog
   skupa mogu biti i domenske promenljive. To je iskorisceno u ovom
   primeru. 
*/

int: n; % broj predmeta
int: C;  % kapacitet

set of int: Items = 1..n;

array [Items] of int : Values;
array [Items] of int : Sizes;

var set of Items: S; % skup spakovanih predmeta

function var int : knapsack_sum(var set of Items: s, array [Items] of int: c) = 
      sum(i in s) (c[i]);

constraint knapsack_sum(S, Sizes) <= C;

solve maximize knapsack_sum(S, Values);

output ["Set: "++show(S)++" with size: "++show(knapsack_sum(S,Sizes))++" and value: "++show(knapsack_sum(S,Values))];