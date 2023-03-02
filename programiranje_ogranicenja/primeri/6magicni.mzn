% Primer 6: magicni kvadrat

include "globals.mzn";

/* NAPOMENA: U ovom primeru po prvi put koristimo nizove promenljivih.

Niz promenljivih u MiniZInc-u moze biti jednodimenzioni i visedimenzioni. 
Deklaracija niza promenljivih ima oblik: 

array[index_set1, index_set2...] of <simple_var_decl>;

gde je <simpl_var_decl> deklaracija promenljive kakvu smo ranije opisali (2send.mzn).
Promenljive u nizu mogu biti parametri ili domenske promenljive, npr:

array [1..10]  of int: x;  % niz od 10 parametara tipa int;
array [1..10] of var 0..1: x;  % niz od 10 domenskih promenljivih sa domenom {0,1}

Parametri se mogu inicijalizovati sintaksom [v1,v2,...,vn] npr:

array [1..10] of int: x = [1,2,3,4,5,6,7,8,9,10];

U slucaju dvodimenzionih nizova (matrica), to mozemo uraditi na sledeci nacin:

array [1..3, 1..4] of int: x = [| 1, 2, 3, 4| 5,6,7,8| 9, 10, 11, 12|]; 

Dakle, vrste se razdvajaju znakom |. Prva dimenzija oznacava vrste (indeksirane 
sa 1,2,3), a druga kolone (indeksirane sa 1,2,3,4). 

U slucaju visedimenzionih nizova, za inicijalizaciju se moze koristiti posebna funkcija:

array [1..2, 1..3, 1..4] of int: x = array3d(1..2,1..3,1..4,[1,2,3,4,5,6,7,8,9,10,11,12,
                                                                                      13,14,15,16,17,18,19,20,
                                                                                      21,22,23,24]);
Dakle, najpre se zadaju dimenzije, a onda se zadaje jednodimenzioni niz inicijalizatora
koji se redom koriste u "trostrukoj petlji" za inicijalizaciju elemenata (poslednji indeks
je najunutrasnjiji brojac petlje). 

Elementima niza se pristupa pomocu indeksa, npr: x[i], ili x[i,j], ili x[i,j,k].

Indeksi mogu biti konacni intervali celih brojeva, ili enumeratori (o tome vise kasnije). Indeksi
ne moraju pocinjati od 1: 

array[-10..10] of int: x;  % elementi su sada x[-10], ..., x[10]

Duzina jednodimenzionog niza se moze dobiti sa length(x), a skup svih indeksa sa
index_set(x).
*/

array[1..4,1..4] of var 1..16: x;

constraint x[1,1] + x[1,2] + x[1,3] + x[1,4] == 34;
constraint x[2,1] + x[2,2] + x[2,3] + x[2,4] == 34;
constraint x[3,1] + x[3,2] + x[3,3] + x[3,4] == 34;
constraint x[4,1] + x[4,2] + x[4,3] + x[4,4] == 34;
constraint x[1,1] + x[2,1] + x[3,1] + x[4,1] == 34;
constraint x[1,2] + x[2,2] + x[3,2] + x[4,2] == 34;
constraint x[1,3] + x[2,3] + x[3,3] + x[4,3] == 34;
constraint x[1,4] + x[2,4] + x[3,4] + x[4,4] == 34;
constraint x[1,1] + x[2,2] + x[3,3] + x[4,4] == 34;
constraint x[1,4] + x[2,3] + x[3,2] + x[4,1] == 34;
constraint alldifferent([x[1,1], x[1,2], x[1,3], x[1,4], 
                                   x[2,1], x[2,2], x[2,3], x[2,4], 
                                   x[3,1], x[3,2], x[3,3], x[3,4], 
                                   x[4,1], x[4,2], x[4,3], x[4,4]]);

constraint x[1,2] = 12;
constraint x[2,2] = 8;
constraint x[2,3] = 15;
constraint x[3,1] = 7;
constraint x[3,3] = 2;
constraint x[4,1] = 4;
constraint x[4,4] = 11;                                          
                                                 
solve satisfy;

output [show_int(2,x[1,1])++"   "++show_int(2,x[1,2])++"   "++show_int(2,x[1,3])++"   "++show_int(2,x[1,4])++"\n"++
            show_int(2,x[2,1])++"   "++show_int(2,x[2,2])++"   "++show_int(2,x[2,3])++"   "++show_int(2,x[2,4])++"\n"++
            show_int(2,x[3,1])++"   "++show_int(2,x[3,2])++"   "++show_int(2,x[3,3])++"   "++show_int(2,x[3,4])++"\n"++
            show_int(2,x[4,1])++"   "++show_int(2,x[4,2])++"   "++show_int(2,x[4,3])++"   "++show_int(2,x[4,4])++"\n"];