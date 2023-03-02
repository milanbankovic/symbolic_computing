% Primer 3: Linearni sistem

/* U ovom modelu su domeni realni brojevi, tj. nije u pitanju problem
   nad konacnim domenima. U takvim situacijama, resavaci poput 
   gecode ili chuffed se ne snalaze, pa treba izabrati COIN-BC (cbc)
   resavac 
*/

var float: x;
var float: y;

constraint 2*x + 3*y == 5;
constraint x - y == 10;

solve satisfy;

output ["x = "++show(x)++", y = "++show(y)++"\n"];
