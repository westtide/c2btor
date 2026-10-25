#define C2BTOR_FIXTURE_UNSIGNED_MALLOC
#include "fixture_types.h"

/* Match nsqm-iff's actual function parameter; do not include stdlib.h. */
void *malloc(unsigned int size);
extern size_t __VERIFIER_nondet_size_t(void);
size_t observed_wide_bytes;
unsigned int observed_parameter_bytes;
size_t observed_object_size;

int main(void)
{
  size_t n = __VERIFIER_nondet_size_t();
  if(n != (size_t)536870913ULL)
    return 0;
  observed_wide_bytes = sizeof(unsigned long long) * n;
  observed_parameter_bytes = (unsigned int)observed_wide_bytes;
  void *p = malloc(observed_wide_bytes);
  if(!p)
    return 0;
  observed_object_size = __CPROVER_OBJECT_SIZE(p);
  __CPROVER_assert(
    observed_wide_bytes == (sizeof(size_t) == 4 ? 8ULL : 4294967304ULL) &&
      observed_parameter_bytes == 8U && observed_object_size == 8U,
    "T9 malloc receives its actual unsigned-int parameter conversion");
  return 0;
}
