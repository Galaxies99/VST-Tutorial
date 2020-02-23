int gcd(int n, int m) {
  int r = m % n;
  if (r == 0)
    return n;
  else
    return gcd(r, n);
}