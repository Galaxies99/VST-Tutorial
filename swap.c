struct int_pair {
  int a;
  int b;
};

void int_swap (int * px, int * py) {
  int t;
  t = * px;
  * px = * py;
  * py = t;
}

void int_pair_swap (struct int_pair * p) {
  int t;
  t = p -> a;
  p -> a = p -> b;
  p -> b = t;
}

void int_pair_swap2 (struct int_pair * p) {
  int_swap (& (p -> a), & (p -> b));
}

void uint_swap_arith (unsigned int * px, unsigned int * py) {
  * px = * px + * py;
  * py = * px - * py;
  * px = * px - * py;
}

