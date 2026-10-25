extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned n = __VERIFIER_nondet_uint();
  __CPROVER_assume(n == 2U);
  unsigned a[2][n];
  a[0][0] = 0U;
  a[0][1] = 0U;
  a[1][0] = 7U;
  a[1][1] = 9U;
  n = 1U;
  a[1][1] += 1U;
  __CPROVER_assert(a[0][0] == 0U && a[0][1] == 0U &&
                    a[1][0] == 7U && a[1][1] == 10U && n == 1U,
                  "check DECL captured stride after scalar change");
  __CPROVER_assert(0, "optimization-reached");
}
