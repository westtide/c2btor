extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned flag = __VERIFIER_nondet_uint();
  unsigned value = __VERIFIER_nondet_uint();
  unsigned result;
  if(flag)
    result = (value + 1U) * 7U;
  else
    result = (value + 2U) * 7U;
  __CPROVER_assert(result == (flag ? 42U : 49U),
                  "check both arithmetic diamond arms");
  __CPROVER_assert(0, "optimization-reached");
}
