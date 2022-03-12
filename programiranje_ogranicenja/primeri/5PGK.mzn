% Primer 5: Petao, Gavran i Kukavica

var 1..72: P;
var 1..72: G;
var 1..72: K;

constraint 46 <= P + G + K  /\  P + G + K <= 72;
constraint 2 <= P + G /\ P + G <= 28;
constraint 5 <= G + K /\ G + K <= 31;
constraint 7 <= K + P /\ K + P <= 33;

solve satisfy;

output ["Petao: \(P), Gavran \(G), Kukavica \(K)\n"];
 