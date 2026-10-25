extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned initial = __VERIFIER_nondet_uint();
  __CPROVER_assume(initial == 2U);
  unsigned n = initial;
  for(unsigned iteration = 0U; iteration < 2U; ++iteration)
  {
    n = initial + iteration;
    unsigned a[2][n];
    a[0][0] = 0U;
    a[0][1] = 0U;
    if(iteration)
      a[0][2] = 4U;
    a[1][0] = iteration + 7U;
    a[1][1] = iteration + 9U;
    n = 1U;
    a[1][1] += 1U;
    __CPROVER_assert(a[0][0] == 0U && a[0][1] == 0U &&
                      a[1][0] == iteration + 7U && a[1][1] == iteration + 10U &&
                      (!iteration || a[0][2] == 4U),
                    "check loop DECL recapture and fresh stores");
  }
  __CPROVER_assert(n == 1U, "check last dimension variable value");
  __CPROVER_assert(0, "optimization-reached");
}
