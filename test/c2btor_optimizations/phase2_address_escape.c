extern unsigned __VERIFIER_nondet_uint(void);

static void set_element(unsigned *p)
{
  *p = 77U;
}

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned a[3] = {1U, 2U, 3U};
  unsigned *p = &a[i];
  set_element(p);
  __CPROVER_assert(a[i] == 77U && *p == 77U, "check escaped element mutation");
  __CPROVER_assert(a[0] == 1U && a[2] == 3U, "check escaped store frame");
  __CPROVER_assert(0, "optimization-reached");
}
