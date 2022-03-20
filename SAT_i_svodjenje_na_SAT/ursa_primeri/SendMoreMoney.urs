bAllDifferent   = (nS!=nE) && (nS!=nN) && (nS!=nD) && (nS!=nM) && (nS!=nO) && (nS!=nR) && (nS!=nY);
bAllDifferent &&= (nE!=nN) && (nE!=nD) && (nE!=nM) && (nE!=nO) && (nE!=nR) && (nE!=nY);
bAllDifferent &&= (nN!=nD) && (nN!=nM) && (nN!=nO) && (nN!=nR) && (nN!=nY);
bAllDifferent &&= (nD!=nM) && (nD!=nO) && (nD!=nR) && (nD!=nY);
bAllDifferent &&= (nM!=nO) && (nM!=nR) && (nM!=nY);
bAllDifferent &&= (nO!=nR) && (nO!=nY);
bAllDifferent &&= (nR!=nY);

bDomain =  (nS<10) && (nE<10) && (nN<10) && (nD<10) && (nM<10) && (nO<10) && (nR<10) && (nY<10);

bNoLeadingZeros = (nM!=0) && (nS!=0);

bSum = (nS*1000+nE*100+nN*10+nD+nM*1000+nO*100+nR*10+nE==nM*10000+nO*1000+nN*100+nE*10+nY);

assert_all(bAllDifferent && bDomain && bNoLeadingZeros && bSum);

