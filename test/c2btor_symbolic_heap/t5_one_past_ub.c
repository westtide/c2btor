#include "fixture_types.h"

extern unsigned int __VERIFIER_nondet_uint(void);
unsigned long long observed_one_past;
unsigned long long observed_first_after_ub;

int main(void)
{
  unsigned int n = __VERIFIER_nondet_uint();
  if(n != 3U)
    return 0;
  unsigned long long *p = malloc(sizeof(*p) * (size_t)n);
  if(!p)
    return 0;
  p[0] = 11;
  unsigned long long *end = p + n;
  /* Deliberate C UB. Compare observations within the same backend only. */
  *end = 17;
  observed_one_past = *end;
  observed_first_after_ub = p[0];
  __CPROVER_assert(
    !__CPROVER_r_ok(end, sizeof(*end)) &&
      __CPROVER_POINTER_OBJECT(end) == __CPROVER_POINTER_OBJECT(p) &&
      (size_t)__CPROVER_POINTER_OFFSET(end) == 24U,
    "T5 one-past UB retains existing metadata and source-property contract");
  return 0;
}
