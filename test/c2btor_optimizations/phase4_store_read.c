extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned j = __VERIFIER_nondet_uint();
  __CPROVER_assume(i < 3U && j < 3U);
  unsigned a[3] = {0U, 0U, 0U};
  a[i] = 7U;
  unsigned observed = a[j];
  __CPROVER_assert(observed == (i == j ? 7U : 0U), "check current store read");
  __CPROVER_assert(0, "optimization-reached");
}
