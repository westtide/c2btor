extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned index = __VERIFIER_nondet_uint();
  __CPROVER_assume(index < 2U);
  unsigned a[2] = {0U, 0U};
  a[index] = 7U;
  __CPROVER_assert(a[index] == 7U, "check first assertion store snapshot");
  a[index] = 9U;
  __CPROVER_assert(a[index] == 9U, "check second assertion store snapshot");
  __CPROVER_assert(0, "optimization-reached");
}
