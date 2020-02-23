#include <stddef.h>

struct list {unsigned head; struct list *tail;};

struct list *reverse (struct list *p) {
  struct list *w, *t, *v;
  w = NULL;
  v = p;
  while (v) {
    t = v->tail;
    v->tail = w;
    w = v;
    v = t;
  }
  return w;
}

