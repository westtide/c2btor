extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned choose = __VERIFIER_nondet_uint();
  unsigned a = 3U, b = 4U;
  unsigned *p = choose ? &a : &b;
  unsigned *q = p;
  *p = 41U;
  *q = *q + 1U;
  __CPROVER_assert(*p == 42U && *q == 42U, "check alias reads");
  __CPROVER_assert(a == (choose ? 42U : 3U), "check direct a view");
  __CPROVER_assert(b == (choose ? 4U : 42U), "check direct b view");
  __CPROVER_assert(0, "optimization-reached");
}
