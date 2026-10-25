extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned x = __VERIFIER_nondet_uint();
  __CPROVER_assert(x != 7U, "optimization-prefix-failure");
  __CPROVER_assume(x != 7U);
  __CPROVER_assert(0, "optimization-unreachable");
}
