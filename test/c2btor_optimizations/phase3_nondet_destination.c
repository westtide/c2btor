extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned current = __VERIFIER_nondet_uint();
  unsigned first = current;
  current = __VERIFIER_nondet_uint();
  unsigned second = current;
  __CPROVER_assert(first == 5U && second == 9U && first != second,
                  "check independent calls sharing user destination");
  __CPROVER_assert(0, "optimization-reached");
}
