extern unsigned __VERIFIER_nondet_uint(void);
static unsigned static_values[3] = {11U, 22U, 33U};
static unsigned static_zero[3];

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned local_values[3] = {4U, 5U, 6U};
  __CPROVER_assert(static_values[i] == 22U, "check static initializer");
  __CPROVER_assert(static_zero[i] == 0U, "check static zero initializer");
  __CPROVER_assert(local_values[i] == 5U, "check local initializer");
  __CPROVER_assert(0, "optimization-reached");
}
