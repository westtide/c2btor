extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned flag = __VERIFIER_nondet_uint();
  unsigned a[2] = {1U, 2U};
  if(flag)
  {
    a[0] = 7U;
    a[1] = 11U;
  }
  else
  {
    a[0] = 3U;
    a[1] = 9U;
  }
  unsigned observed = a[0] + a[1];
  __CPROVER_assert(observed == (flag ? 18U : 12U), "check guarded array join");
  __CPROVER_assert(0, "optimization-reached");
}
