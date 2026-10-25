#include "fixture_types.h"

extern unsigned long long __VERIFIER_nondet_ulonglong(void);

int main(void)
{
  unsigned long long n = __VERIFIER_nondet_ulonglong();
  if(n < 3ULL || n > 2305843009213693951ULL)
    return 0;
  unsigned long long *p = malloc(sizeof(*p) * (size_t)n);
  if(!p)
    return 0;
  unsigned long long **holder = &p;
  unsigned long long *q = *holder;
  q[0] = 9;
  __CPROVER_assert(
    sizeof(*holder) == sizeof(void *) && p[0] == 9 && q == p,
    "boundary addressable pointer needs a faithful C-layout serialization");
  return 0;
}
