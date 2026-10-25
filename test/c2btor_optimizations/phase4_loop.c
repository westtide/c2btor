extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned limit = __VERIFIER_nondet_uint();
  __CPROVER_assume(limit == 70U);
  unsigned a[1] = {0U};
  unsigned i = 0U;
  while(i < limit)
  {
    unsigned old = a[0];
    a[0] = old + i + 1U;
    unsigned current = a[0];
    __CPROVER_assert(current == old + i + 1U, "check loop latest read after write");
    i += 1U;
  }
  __CPROVER_assert(i == 70U && a[0] == 2485U, "check array loop backedge");
  __CPROVER_assert(0, "optimization-reached");
}
