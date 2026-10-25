#include "fixture_types.h"

extern size_t __VERIFIER_nondet_size_t(void);
size_t observed_wide_bytes;
unsigned int observed_parameter_bytes;
size_t observed_object_size;

static void *allocate_u32(unsigned int bytes)
{
  observed_parameter_bytes = bytes;
  return malloc((size_t)bytes);
}

int main(void)
{
  size_t n = __VERIFIER_nondet_size_t();
  if(n != (size_t)536870913ULL)
    return 0;
  observed_wide_bytes = sizeof(unsigned long long) * n;
  void *p = allocate_u32(observed_wide_bytes);
  if(!p)
    return 0;
  observed_object_size = __CPROVER_OBJECT_SIZE(p);
  __CPROVER_assert(
    observed_wide_bytes == (sizeof(size_t) == 4 ? 8ULL : 4294967304ULL) &&
      observed_parameter_bytes == 8U && observed_object_size == 8U,
    "T9 unsigned-int function parameter conversion precedes size_t malloc");
  return 0;
}
