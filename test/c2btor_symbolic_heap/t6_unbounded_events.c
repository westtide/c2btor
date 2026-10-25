#include "fixture_types.h"

extern int __VERIFIER_nondet_int(void);

int main(void)
{
  void *p = 0;
  while(__VERIFIER_nondet_int())
    p = malloc(8);
  __CPROVER_assert(
    !p || __CPROVER_POINTER_OFFSET(p) == 0,
    "T6 unbounded event count must be rejected before model emission");
  return 0;
}
