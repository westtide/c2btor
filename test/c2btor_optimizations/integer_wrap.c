extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned a = __VERIFIER_nondet_uint();
  unsigned wrapped = a + 1U;
  unsigned char byte = (unsigned char)(a + 2U);
  unsigned short half = (unsigned short)(a + 3U);
  __CPROVER_assert(wrapped == 0U, "check unsigned wrap");
  __CPROVER_assert(byte == 1U && half == 2U, "check truncation");
  __CPROVER_assert(0, "optimization-reached");
}
