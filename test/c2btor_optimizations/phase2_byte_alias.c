extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned a[2] = {0U, 6U};
  unsigned char *bytes = (unsigned char *)&a[0];
  bytes[i] = 42U;
  __CPROVER_assert(bytes[i] == 42U && a[0] != 0U, "check byte alias mutation");
  __CPROVER_assert(a[1] == 6U, "check byte alias frame");
  __CPROVER_assert(0, "optimization-reached");
}
