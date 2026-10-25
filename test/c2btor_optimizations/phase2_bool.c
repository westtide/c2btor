extern unsigned __VERIFIER_nondet_uint(void);
static _Bool static_flags[3] = {0, 2, -1};

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned raw = __VERIFIER_nondet_uint();
  _Bool automatic_flags[4] = {2};
  __CPROVER_assert((unsigned)static_flags[0] == 0U &&
                    (unsigned)static_flags[i] == 1U,
                  "check Boolean static normalization");
  __CPROVER_assert((unsigned)automatic_flags[0] == 1U &&
                    (unsigned)automatic_flags[i] == 0U,
                  "check Boolean automatic partial initialization");
  automatic_flags[i] = raw;
  __CPROVER_assert((unsigned)automatic_flags[i] == 1U,
                  "check Boolean nonzero store normalization");
  automatic_flags[i] = 0U;
  __CPROVER_assert((unsigned)automatic_flags[i] == 0U,
                  "check Boolean zero store normalization");
  __CPROVER_assert(0, "optimization-reached");
}
