extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned a = __VERIFIER_nondet_uint();
  unsigned b = __VERIFIER_nondet_uint();
  __CPROVER_assert(a == 5U && b == 9U, "check independent calls");
  __CPROVER_assert(a != b, "check separate input identities");
  __CPROVER_assert(0, "optimization-reached");
}
