#include "fixture_types.h"

extern unsigned int __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned int n = __VERIFIER_nondet_uint();
  if(n != 536870911U)
    return 0;

  unsigned long long *a = malloc(sizeof(*a) * (size_t)n);
  unsigned long long *b = malloc(sizeof(*b) * (size_t)n);
  if(!a || !b)
    return 0;

  a[0] = 11;
  b[8] = 22;
  __CPROVER_assert(
    a[0] == 11 && b[8] == 22 &&
      __CPROVER_POINTER_OBJECT(a) != __CPROVER_POINTER_OBJECT(b),
    "T2 large allocation events retain distinct objects");
  return 0;
}
