extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned flag = __VERIFIER_nondet_uint();
  unsigned value = __VERIFIER_nondet_uint();
  unsigned result;
  if(flag)
  {
    result = value + 1U;
    __CPROVER_assert(0, "optimization-skipped-assertion");
  }
  else
    result = value + 2U;
  __CPROVER_assert(result == 7U, "check selected diamond path");
  __CPROVER_assert(0, "optimization-reached");
}
