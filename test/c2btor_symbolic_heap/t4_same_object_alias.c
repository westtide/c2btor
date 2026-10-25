#include "fixture_types.h"

int main(void)
{
  unsigned long long *p = malloc(16);
  if(!p)
    return 0;
  unsigned long long *q = p;
  q[0] = 9;
  __CPROVER_assert(
    p[0] == 9 && q[0] == 9 &&
      __CPROVER_POINTER_OBJECT(p) == __CPROVER_POINTER_OBJECT(q) &&
      __CPROVER_POINTER_OFFSET(q) == 0,
    "T4 copied pointers share the same byte storage");
  return 0;
}
