#include "fixture_types.h"

extern unsigned int __VERIFIER_nondet_uint(void);

union lanes
{
  unsigned long long wide;
  unsigned int ints[2];
  unsigned short shorts[4];
  unsigned char bytes[8];
};

int main(void)
{
  unsigned int n = __VERIFIER_nondet_uint();
  if(n != 2U)
    return 0;
  union lanes *p = malloc(sizeof(*p) * (size_t)n);
  if(!p)
    return 0;
  p[0].wide = 0x1122334455667788ULL;
  unsigned char *bytes = (unsigned char *)p;
  bytes[1] = 0xAB;
  union lanes *q = p;
  __CPROVER_assert(
    q[0].wide == 0x112233445566AB88ULL && bytes[1] == 0xAB &&
      q[0].shorts[0] == 0xAB88 && q[0].ints[0] == 0x5566AB88U &&
      __CPROVER_POINTER_OBJECT(bytes) == __CPROVER_POINTER_OBJECT(p),
    "T8 little-endian mixed-width aliases share byte lanes");
  return 0;
}
