/* To be used with number represented by vectors of lenght >2 */
b1 = (nv!=0) && ((nv & (nv-1))==0);

nLen=8;
bOne = false;
bMoreThanOne = false;
for(ni=0; ni<nLen; ni++)  {
  bMoreThanOne ||= bOne && ((nv & 1)!=0);
  bOne ||= ((nv & 1)!=0);
  nv >>= 1;
}
b2 = bOne && !bMoreThanOne;

assert(b1^^b2);
