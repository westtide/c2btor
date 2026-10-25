extern unsigned __VERIFIER_nondet_uint(void);
static unsigned static_total = 7U;

int main(void)
{
  unsigned limit = __VERIFIER_nondet_uint();
  unsigned i = 0U;
  unsigned total = 0U;
  while(i < limit)
  {
    unsigned step = i + 1U;
    unsigned contribution = step * 3U;
    total += contribution;
    static_total += 1U;
    i += 1U;
  }
  __CPROVER_assert(i == 70U && total == 7455U && static_total == 77U,
                  "check loop body backedge and static accumulator");
  __CPROVER_assert(0, "optimization-reached");
}
