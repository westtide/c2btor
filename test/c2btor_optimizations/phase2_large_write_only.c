extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned n = __VERIFIER_nondet_uint();
  __CPROVER_assume(n == 100000000U);
  unsigned unused[n];
  unused[0] = __VERIFIER_nondet_uint();
  unsigned other = 9U;
  unsigned long pointer_bits = (unsigned long)&other;
  __CPROVER_assert(pointer_bits != 0UL && other == 9U,
                  "check unrelated addressable object");
  __CPROVER_assert(0, "optimization-reached");
}
