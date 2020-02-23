unsigned int uadd(unsigned int x, unsigned int y) {
  unsigned int z;
  z = x + y;
  return z;
}

int add(int x, int y) {
  int z;
  z = x + y;
  return z;
}

int slow_add(int x, int y) {
  while (x > 0) {
    x = x - 1;
    y = y + 1;
  }
  return y;
}
