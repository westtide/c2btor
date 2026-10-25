#include "fixture_types.h"

void *calloc(size_t nmemb, size_t size);
extern unsigned int __VERIFIER_nondet_uint(void);
unsigned long long observed_calloc_first_before;
unsigned long long observed_calloc_last_before;
unsigned long long observed_calloc_last_after;
size_t observed_calloc_size;

int main(void)
{
  unsigned int n = __VERIFIER_nondet_uint();
  if(n < 2U || n > 3U)
    return 0;
  unsigned long long *p = calloc((size_t)n, sizeof(*p));
  if(!p)
    return 0;

  observed_calloc_first_before = p[0];
  observed_calloc_last_before = p[n - 1U];
  p[0] = 9;
  observed_calloc_last_after = p[n - 1U];
  observed_calloc_size = __CPROVER_OBJECT_SIZE(p);
  __CPROVER_assert(
    observed_calloc_first_before == 0 && observed_calloc_last_before == 0 &&
      observed_calloc_last_after == 0 && p[0] == 9 &&
      observed_calloc_size == sizeof(*p) * (size_t)n &&
      sizeof(*p) == 8U && sizeof(void *) == sizeof(size_t),
    "T8 symbolic calloc zeroes untouched cells independently of arbitrary array seeds");
  return 0;
}
