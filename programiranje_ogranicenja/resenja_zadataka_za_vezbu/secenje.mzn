% 41. Secenje tepiha

int : W; % sirina rolne u cm

int : n; % broj tepiha

array [1..n] of int: w; % sirine tepiha
array [1..n] of int: l; % duzine tepiha

constraint assert(forall(i in 1..n)(w[i] <= W \/ l[i] <= W),  "Bar jedna dimenzija tepiha mora biti manja od W");
  
int : maxL = sum(i in 1..n) (max([l[i], w[i]]));
            
array [1..n] of var 0..maxL: x;  % x koordinata (po duzini rolne) gde pocinje i-ti tepih
array [1..n] of var 0..W: y; % y koordinata (po sirini rolne) gde pocinje i-ti tepih
array [1..n] of var bool: r; % r[i] oznacava da li je i-ti tepih rotiran (tako da mu je w[i] duzina a l[i] sirina)

var 1..maxL: L;  % duzina rolne

% najdesnja x koordinata tepiha
function var int: right_x(var int: x, var int: y, int: w, int: l, var bool: r) = 
  if(r == false) then x + l else x + w endif; 

% najgornja y koordinata tepiha
function var int: top_y(var int: x, var int: y, int: w, int: l, var bool: r) = 
 if(r == false) then y + w else y + l endif;

% predikat koji izrazava svojstvo da tepih ne "iskace" izvan rolne
predicate fits(var int: x, var int: y, int: w, int: l, var bool: r) = 
 right_x(x,y,w,l,r) <= L /\ top_y(x,y,w,l,r) <= W;
 
% svi tepisi moraju biti u okviru rolne
constraint forall(i in 1..n) (fits(x[i], y[i], w[i], l[i], r[i]));

% prvi tepih je levo od drugog
predicate left(var int: x1, var int: y1, int: w1, int: l1, var bool: r1,
                       var int: x2, var int: y2, int: w2, int: l2, var bool: r2) = 
 right_x(x1,y1,w1,l1,r1) <= x2;
 
% prvi tepih je desno od drugog
predicate right(var int: x1, var int: y1, int: w1, int: l1, var bool: r1,
                         var int: x2, var int: y2, int: w2, int: l2, var bool: r2) =  
 right_x(x2,y2,w2,l2,r2) <= x1;

% prvi tepih je iznad drugog
predicate above(var int: x1, var int: y1, int: w1, int: l1, var bool: r1,
                          var int: x2, var int: y2, int: w2, int: l2, var bool: r2) =   
top_y(x2,y2,w2,l2,r2) <= y1;

% prvi tepih je ispod drugog
predicate below(var int: x1, var int: y1, int: w1, int: l1, var bool: r1,
                           var int: x2, var int: y2, int: w2, int: l2, var bool: r2) =   
top_y(x1,y1,w1,l1,r1) <= y2;

% dva tepiha se ne preklapaju
predicate no_overlap(var int: x1, var int: y1, int: w1, int: l1, var bool: r1,
                                   var int: x2, var int: y2, int: w2, int: l2, var bool: r2) = 
left(x1,y1,w1,l1,r1,x2,y2,w2,l2,r2) \/
right(x1,y1,w1,l1,r1,x2,y2,w2,l2,r2) \/
above(x1,y1,w1,l1,r1,x2,y2,w2,l2,r2) \/
below(x1,y1,w1,l1,r1,x2,y2,w2,l2,r2);

% nikoja dva tepiha se ne smeji preklapati
constraint forall(i,j in 1..n where i < j) (no_overlap(x[i],y[i],w[i],l[i],r[i],x[j],y[j],w[j],l[j],r[j]));

% cilj je minimizovati duzinu rolne
solve minimize L;
