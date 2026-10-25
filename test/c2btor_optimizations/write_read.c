extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned a[3] = {1U, 2U, 3U};
  unsigned *p = &a[0];
  p[i] = 40U;
  a[i] = a[i] + 2U;
  __CPROVER_assert(p[i] == 42U && a[i] == 42U, "check write then read");
  __CPROVER_assert(a[0] == 1U && a[2] == 3U, "check untouched elements");
  __CPROVER_assert(0, "optimization-reached");
}
