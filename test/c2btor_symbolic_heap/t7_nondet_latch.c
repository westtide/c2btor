#include "fixture_types.h"

extern unsigned int __VERIFIER_nondet_uint(void);
unsigned int observed_first_n;
unsigned int observed_second_n;
unsigned int observed_delay;
size_t observed_a_size;
size_t observed_b_size;

int main(void)
{
  unsigned int n = __VERIFIER_nondet_uint();
  unsigned int other = __VERIFIER_nondet_uint();
  if(n < 1U || n > 3U)
    return 0;
  observed_first_n = n;
  unsigned long long *a = malloc(sizeof(*a) * (size_t)n);
  observed_delay = other + 1U;
  observed_second_n = n;
  unsigned long long *b = malloc(sizeof(*b) * (size_t)n);
  if(!a || !b)
    return 0;
  observed_a_size = __CPROVER_OBJECT_SIZE(a);
  observed_b_size = __CPROVER_OBJECT_SIZE(b);
  __CPROVER_assert(
    observed_first_n == observed_second_n &&
      observed_a_size == sizeof(*a) * (size_t)observed_first_n &&
      observed_b_size == observed_a_size,
    "T7 one nondet assignment supplies both allocation size expressions");
  return 0;
}
