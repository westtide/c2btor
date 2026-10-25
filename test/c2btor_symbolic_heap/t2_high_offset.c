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
  b[0] = 22;
  a[n - 1U] = 31;
  b[n - 1U] = 47;
  __CPROVER_assert(
    a[0] == 11 && b[0] == 22 && a[n - 1U] == 31 && b[n - 1U] == 47 &&
      __CPROVER_POINTER_OBJECT(a) != __CPROVER_POINTER_OBJECT(b) &&
      (size_t)__CPROVER_POINTER_OFFSET(a + n - 1U) ==
        sizeof(*a) * (size_t)(n - 1U),
    "T2 highest legal byte offset does not lose high bits or object identity");
  return 0;
}
