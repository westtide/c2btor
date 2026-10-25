#include "fixture_types.h"

extern unsigned int __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned int n = __VERIFIER_nondet_uint();
  if(n != 3U)
    return 0;
  unsigned long long *p = malloc(sizeof(*p) * (size_t)n);
  if(!p)
    return 0;
  p[n - 1U] = 7;
  unsigned long long *end = p + n;
  __CPROVER_assert(
    p[n - 1U] == 7 && __CPROVER_r_ok(p + n - 1U, sizeof(*p)) &&
      !__CPROVER_r_ok(end, sizeof(*p)) &&
      (size_t)__CPROVER_POINTER_OFFSET(end) == 24U &&
      __CPROVER_POINTER_OBJECT(end) == __CPROVER_POINTER_OBJECT(p),
    "T5 last element is accessible and one-past formation preserves its offset");
  return 0;
}
