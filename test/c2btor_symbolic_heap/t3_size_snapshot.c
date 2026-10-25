#include "fixture_types.h"

extern unsigned int __VERIFIER_nondet_uint(void);
size_t observed_size_before;
size_t observed_size_after;
unsigned long long observed_last_value;

int main(void)
{
  unsigned int n = __VERIFIER_nondet_uint();
  if(n != 3U)
    return 0;

  unsigned long long *p = malloc(sizeof(*p) * (size_t)n);
  if(!p)
    return 0;
  observed_size_before = __CPROVER_OBJECT_SIZE(p);
  n = 1U;
  p[2] = 7;
  observed_size_after = __CPROVER_OBJECT_SIZE(p);
  observed_last_value = p[2];
  __CPROVER_assert(
    n == 1U && observed_size_before == 24U && observed_size_after == 24U &&
      observed_last_value == 7 && __CPROVER_r_ok(p + 2, sizeof(*p)),
    "T3 allocation size is the original 24 byte snapshot");
  return 0;
}
