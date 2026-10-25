extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned choice = __VERIFIER_nondet_uint();
  unsigned x = __VERIFIER_nondet_uint();
  unsigned y;
  if(choice)
  {
    x = x + 3U;
    y = x * 2U;
  }
  else
  {
    x = x + 4U;
    y = x * 3U;
  }
  __CPROVER_assert(x == (choice ? 8U : 9U), "check branch state");
  __CPROVER_assert(y == (choice ? 16U : 27U), "check branch merge");
  __CPROVER_assert(0, "optimization-reached");
}
