#include "fixture_types.h"

extern unsigned int __VERIFIER_nondet_uint(void);
unsigned char observed_freed_byte;
unsigned long long observed_freed_word;
int observed_live_before;
int observed_live_after;

int main(void)
{
  unsigned int n = __VERIFIER_nondet_uint();
  if(n != 2U)
    return 0;
  unsigned long long *p = malloc(sizeof(*p) * (size_t)n);
  if(!p)
    return 0;
  p[0] = 0x1122334455667788ULL;
  unsigned long long *q = p;
  unsigned char *bytes = (unsigned char *)q;
  observed_live_before = __CPROVER_r_ok(q, sizeof(*q));
  free(p);
  observed_live_after = __CPROVER_r_ok(q, sizeof(*q));
  /* Deliberate C UB. Existing reads/writes are not gated by live. */
  observed_freed_byte = bytes[0];
  bytes[1] = 0xCD;
  observed_freed_word = q[0];
  __CPROVER_assert(
    observed_live_before && !observed_live_after &&
      __CPROVER_OBJECT_SIZE(q) == 16U &&
      __CPROVER_POINTER_OBJECT(q) == __CPROVER_POINTER_OBJECT(p),
    "T8 free changes liveness while pointer and size metadata persist");
  return 0;
}
