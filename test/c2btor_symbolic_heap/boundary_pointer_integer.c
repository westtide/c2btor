#include "fixture_types.h"

extern unsigned long long __VERIFIER_nondet_ulonglong(void);

int main(void)
{
  unsigned long long n = __VERIFIER_nondet_ulonglong();
  if(n < 3ULL || n > 2305843009213693951ULL)
    return 0;
  void *p = malloc(8U * (size_t)n);
  if(!p)
    return 0;
  uintptr_t bits = (uintptr_t)p;
  void *q = (void *)bits;
  __CPROVER_assert(
    sizeof(void *) == sizeof(uintptr_t) && q == p,
    "boundary pointer-to-integer needs a faithful C-width serialization");
  return 0;
}
