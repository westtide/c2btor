extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned n = __VERIFIER_nondet_uint();
  __CPROVER_assume(n == 4U);
  unsigned a[n];
  n = 2U;
  a[3] = 99U;
  a[0] = 11U;
  __CPROVER_assert(n == 2U && a[3] == 99U && a[0] == 11U,
                  "check DECL-latched VLA dimension");
  __CPROVER_assert(0, "optimization-reached");
}
