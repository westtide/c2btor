#include <stdint.h>
#include <stdlib.h>

struct MNode
{
  int value;
  struct MNode *next;
};
struct MBuffer
{
  int capacity;
  int32_t *data;
};

int main(void)
{
  int capacity = 3;
  struct MNode *a = malloc(sizeof(*a));
  struct MBuffer *b = malloc(sizeof(*b));
  int32_t *c = malloc(capacity * sizeof(*c));
  struct MNode *d = malloc(sizeof(*d));
  struct MBuffer *e = malloc(sizeof(*e));
  int32_t *f = malloc((capacity + 1) * sizeof(*f));
  int32_t *g = malloc(sizeof(*g));
  __CPROVER_assume(a && b && c && d && e && f && g);
#ifdef NEGATIVE_CONTROL
  __CPROVER_assert((void *)a == (void *)b, "distinct allocation sites");
#else
  __CPROVER_assert(
    (void *)a != (void *)b && (void *)a != (void *)c &&
      (void *)a != (void *)d && (void *)a != (void *)e &&
      (void *)a != (void *)f && (void *)a != (void *)g &&
      (void *)b != (void *)c && (void *)b != (void *)d &&
      (void *)b != (void *)e && (void *)b != (void *)f &&
      (void *)b != (void *)g && (void *)c != (void *)d &&
      (void *)c != (void *)e && (void *)c != (void *)f &&
      (void *)c != (void *)g && (void *)d != (void *)e &&
      (void *)d != (void *)f && (void *)d != (void *)g &&
      (void *)e != (void *)f && (void *)e != (void *)g &&
      (void *)f != (void *)g,
    "distinct allocation sites");
#ifndef IDENTITY_ONLY
  a->value = 17;
  d->value = 23;
  b->capacity = 3;
  e->capacity = 4;
  c[2] = 31;
  f[3] = 41;
  *g = 59;
  __CPROVER_assert(a->value == 17 && d->value == 23, "node storage");
  __CPROVER_assert(b->capacity == 3 && e->capacity == 4, "buffer storage");
  __CPROVER_assert(c[2] == 31 && f[3] == 41 && *g == 59, "integer storage");
  __CPROVER_assert(
    __CPROVER_OBJECT_SIZE(c) == 12 && __CPROVER_OBJECT_SIZE(f) == 16,
    "allocation sizes include arithmetic operands");
#endif
#endif
}
