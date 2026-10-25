extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned value = __VERIFIER_nondet_uint();
  unsigned computed = value + 1U;
  __CPROVER_assert(computed != 8U, "optimization-prefix-failure");
  __CPROVER_assume(computed == 99U);
  __CPROVER_assert(0, "optimization-unreachable");
}
