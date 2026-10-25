extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned index = __VERIFIER_nondet_uint();
  __CPROVER_assume(index < 2U);
  unsigned a[2] = {1U, 2U};
  unsigned b[2] = {3U, 4U};
  unsigned indices[1] = {0U};
  indices[0] = index;
  a[indices[0]] = 7U;
  b[index] = 9U;
  unsigned observed = a[index] * 10U + b[index];
  __CPROVER_assert(observed == 79U && a[1U - index] == (index ? 1U : 2U) &&
                    b[1U - index] == (index ? 3U : 4U),
                  "check distinct array versions");
  __CPROVER_assert(0, "optimization-reached");
}
