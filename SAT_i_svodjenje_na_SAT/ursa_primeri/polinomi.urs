nN = 4;

/* p1(x) = x+1 */
/*
nA[0] = 1;
nA[1] = 1;
nA[2] = 0;
nA[3] = 0;
*/

/* p2(x) = (x+2)*(x+3) = x^2 + 5x + 6 */ 
/*
nB[0] = 6;
nB[1] = 5;
nB[2] = 1;
nB[3] = 0;
*/

for (nI=0; nI<nN; nI++) {
  nP[nI] = 0;
}
for (nI=0; nI<nN; nI++) {
  for (nJ=0; nJ<nN; nJ++) {
    nP[nI+nJ] += nA[nI]*nB[nJ];
  }
}

/*
print nP[0];
print nP[1];
print nP[2];
print nP[3];
*/

b = true;
for (nI=0; nI<nN; nI++) {
  b &&= (nA[nI]<16);
  b &&= (nB[nI]<16);
}

/* moze se dobiti deljenje, ali i faktorizacije */

assert_all (nP[0] == 6 && nP[1] == 11 && nP[2] == 6 && nP[3] == 1 && nA[1] != 0 &&  nA[2] == 0 && nA[3] == 0 && b);
