nx=nseed;
for(ni=1;ni<=100;ni++) {
  nx=nx*1664525+1013904223;  
}
assert_all(nx==2021);


