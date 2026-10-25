extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned a[4] = {11U, 22U};
  __CPROVER_assert(a[0] == 11U && a[1] == 22U && a[i] == 0U,
                  "check automatic partial initializer");
  a[i] = 77U;
  __CPROVER_assert(a[i] == 77U && a[0] == 11U, "check partial initializer write");
  __CPROVER_assert(0, "optimization-reached");
}
