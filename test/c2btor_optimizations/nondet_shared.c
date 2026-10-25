extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned a = __VERIFIER_nondet_uint();
  unsigned b = a, c = a;
  b = b + 2U;
  c = c + 2U;
  __CPROVER_assert(b == c && b == 7U, "check shared call result");
  __CPROVER_assert(0, "optimization-reached");
}
