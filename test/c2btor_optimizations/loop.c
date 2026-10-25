extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned n = __VERIFIER_nondet_uint();
  unsigned i = 0, sum = 0;
  while(i < n)
  {
    sum = sum + i;
    i = i + 1U;
  }
  __CPROVER_assert(i == 4U && sum == 6U, "check loop exit");
  __CPROVER_assert(0, "optimization-reached");
}
