extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned value = __VERIFIER_nondet_uint();
  unsigned block_temp = value + 1U;
  unsigned result = block_temp * 7U;
  __CPROVER_assert(result == 42U, "check block-local temporary");
  __CPROVER_assert(0, "optimization-reached");
}
