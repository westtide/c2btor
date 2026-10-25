extern float __VERIFIER_nondet_float(void);

int main(void)
{
  unsigned other = 9U;
  unsigned *alias = &other;
  float input = __VERIFIER_nondet_float();
  int discarded = (int)input;
  __CPROVER_assert(*alias == 9U, "check unrelated addressable object");
  __CPROVER_assert(0, "optimization-reached");
}
