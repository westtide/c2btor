#include "fixture_types.h"

extern size_t __VERIFIER_nondet_size_t(void);
size_t observed_bytes;
size_t observed_object_size;

int main(void)
{
  size_t n = __VERIFIER_nondet_size_t();
  if(n != (size_t)536870913ULL)
    return 0;
  observed_bytes = sizeof(unsigned long long) * n;
  void *p = malloc(observed_bytes);
  if(!p)
    return 0;
  observed_object_size = __CPROVER_OBJECT_SIZE(p);
  __CPROVER_assert(
    sizeof(void *) == sizeof(size_t) &&
      observed_bytes == (sizeof(size_t) == 4 ? 8ULL : 4294967304ULL) &&
      observed_object_size == observed_bytes,
    "T9 size_t multiplication uses the configured target width");
  return 0;
}
