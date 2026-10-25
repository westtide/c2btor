extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned value = __VERIFIER_nondet_uint();
  unsigned wrapped = value + 2U;
  unsigned char narrowed = (unsigned char)wrapped;
  signed char signed_narrowed = (signed char)255U;
  int signed_value = -127;
  signed_value += 2;
  unsigned computed = narrowed * 7U;
  __CPROVER_assert(wrapped == 1U && narrowed == 1U && computed == 7U &&
                    signed_narrowed == -1 && signed_value == -125,
                  "check scalar wrap narrowing and signed arithmetic");
  __CPROVER_assert(0, "optimization-reached");
}
