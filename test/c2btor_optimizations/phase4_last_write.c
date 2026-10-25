extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned index = __VERIFIER_nondet_uint();
  unsigned first = __VERIFIER_nondet_uint();
  unsigned second = __VERIFIER_nondet_uint();
  __CPROVER_assume(index < 2U);
  unsigned a[2] = {0U, 0U};
  a[index] = first;
  a[index] = second;
  unsigned observed = a[index];
  __CPROVER_assert(observed == second, "check last write current version");
  __CPROVER_assert(0, "optimization-reached");
}
