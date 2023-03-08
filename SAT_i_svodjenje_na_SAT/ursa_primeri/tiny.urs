procedure Encrypt (nv0, nv1, nK0, nK1, nK2, nK3) {
    nDelta = 0x9E3779B9;                     
    nSum = 0;
    for (nI=0; nI<32; nI++) {
        nSum += nDelta;
        nv0 += (((nv1<<4) + nK0) ^ (nv1 + nSum)) ^ ((nv1>>5) + nK1);
        nv1 += (((nv0<<4) + nK2) ^ (nv0 + nSum)) ^ ((nv0>>5) + nK3);
    }                                              
}

nData0 = nInput0;
nData1 = nInput1;
/* nkey0 = nK1; nkey1 = nK2; nkey2 = nK3; nkey3 = nK3; */
nkey0 = 1; nkey1 = 2; nkey2 = 3; nkey3 = nK3; 
call Encrypt(nData0, nData1, nkey0, nkey1, nkey2, nkey3);

assert_all (nData0 == 2032961448 && nData1 == 1747770815 && nInput0==20 && nInput1==22 && nK3<100); 






