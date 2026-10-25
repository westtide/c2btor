extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned value = __VERIFIER_nondet_uint();
  unsigned a[3] = {1U, 2U, 3U};
  a[i] = value;
  a[i] = a[i] + 1U;
  a[i] = a[i] + 1U;
  __CPROVER_assert(a[i] == 101U, "check latest element store");
  __CPROVER_assert(a[0] == 1U && a[2] == 3U, "check latest store frame");
  __CPROVER_assert(0, "optimization-reached");
}
