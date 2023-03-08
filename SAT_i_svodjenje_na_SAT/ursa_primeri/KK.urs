nDim=8;
bDomain = nWKx<8 && nWKy<8 && nBKx<8 && nBKy<8;
bKingsNotAdjacent = (nWKx>nBKx+1 || nBKx>nWKx+1 || nWKy>nBKy+1 || nBKy>nWKy+1);
assert_all(bDomain && bKingsNotAdjacent);

