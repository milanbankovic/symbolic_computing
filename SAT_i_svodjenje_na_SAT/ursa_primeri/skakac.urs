procedure Legal(nDim, nX1, nY1, nX2, nY2, bLegal) {
  bLegal = ((nX2 == nX1+1 && nY2 == nY1+2) ||
            (nX2 == nX1+2 && nY2 == nY1+1) ||
            (nX2 == nX1+1 && nY1 == nY2+2) ||
            (nX2 == nX1+2 && nY1 == nY2+1) ||
            (nX1 == nX2+1 && nY2 == nY1+2) ||
            (nX1 == nX2+2 && nY2 == nY1+1) ||
            (nX1 == nX2+1 && nY1 == nY2+2) ||
            (nX1 == nX2+2 && nY1 == nY2+1));
  bLegal &&= (nX1<nDim && nX2<nDim && nY1<nDim && nY2<nDim);
}

nDim = 5;
nX[0] = 0; 
nY[0] = 0;
nX[nDim*nDim-1] = nDim-1; 
nY[nDim*nDim-1] = nDim-1;
bSolution = true;

for (nI=0; nI <= nDim*nDim-2; nI++) {
  for (nJ=nI+1; nJ <= nDim*nDim-1; nJ++) {
    bSolution &&= !(nX[nI] == nX[nJ] && nY[nI] == nY[nJ]); 
  }
}
for (nI=0; nI <= nDim * nDim-2; nI++) {
  nx1 = nX[nI];   ny1 = nY[nI];
  nx2 = nX[nI+1]; ny2 = nY[nI+1];
  call Legal(nDim, nx1, ny1, nx2, ny2, b);
  bSolution &&= b;
}
assert(bSolution);

