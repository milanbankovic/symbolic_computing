nDim = 5;
bSolution = true;

/* domain */
for (nI=0; nI <= nDim-1; nI++) {
  bSolution &&= (nA[nI] < nDim); 
}

/* all different */
for (nI=0; nI <= nDim-2; nI++) {
  for (nJ=nI+1; nJ <= nDim-1; nJ++) {
    bSolution &&= (nA[nI] != nA[nJ]); 
  }
}

assert_all(bSolution);

