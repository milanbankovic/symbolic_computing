nDim=8;
bDomain = nWKx<nDim && nWKy<nDim && nBKx<nDim && nBKy<nDim && nWRx<nDim && nWRy<nDim;
bDifferent = !(nWKx == nWRx && nWKy == nWRy) && !(nBKx == nWRx && nBKy == nWRy);
bKingsNotAdjacent = (nWKx>nBKx+1 || nBKx>nWKx+1 || nWKy>nBKy+1 || nBKy>nWKy+1);
bBlackKingAttacked = (nBKx == nWRx || nBKy == nWRy);
bWhiteKingBetween = (nBKx == nWKx && nWKx == nWRx && 
                        ((nBKy < nWKy && nWKy < nWRy) || (nBKy > nWKy && nWKy > nWRy)))
                    ||
                    (nBKy == nWKy && nWKy == nWRy && 
                        ((nBKx < nWKx && nWKx < nWRx) || (nBKx > nWKx && nWKx > nWRx)));
assert_all(bDomain && bDifferent && bKingNotAdjacent && 
           (!bBlackKingAttacked || bWhiteKingBetween));

