unsigned int tri_for (int n) {
  unsigned int s;
  int i;
  s = 0;
  for (i = 0; i < n; ++ i)
    s = s + i;
  return s;
}

unsigned int tri_while (int n) {
  unsigned int s;
  s = 0;
  while (n > 0) {
    n = n - 1;
    s = s + n;
  }
  return s;
}
