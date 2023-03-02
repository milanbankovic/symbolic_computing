% Primer 1: Pitagorine trojke

/* NAPOMENA: Ovaj model koristi skup int kao domene, tj. u pitanju su 
   beskonacni domeni. Jedino resavac gecode pronalazi resenje. */

/* Vise informacija o MiniZinc modelima u komentarima u sledecem primeru 2send.mzn */

var int: x;
var int: y;
var int: z;

constraint x > 0;
constraint y > 0;
constraint z > 0;
constraint x^2 + y^2 == z^2;
constraint x < y;

solve satisfy;