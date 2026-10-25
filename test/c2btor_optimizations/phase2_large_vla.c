extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned n = __VERIFIER_nondet_uint();
  __CPROVER_assume(n == 100000000U);
  unsigned a[n];
  a[0] = 11U;
  a[n - 1U] = 77U;
  __CPROVER_assert(a[0] == 11U && a[n - 1U] == 77U,
                  "check used VLA exceeds byte-offset capacity");
  __CPROVER_assert(0, "optimization-reached");
}
