unsigned int fact(unsigned int n) {
  if (n == 0)
    return 1;
  else
    return n * fact(n - 1);
}

unsigned int fact_loop (unsigned int n) {
  unsigned int i;
  unsigned int r;
  r = 1;
  for (i = 0; i < n; ++ i)
    r = (i+1) * r;
  return r;
}