extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned unused_array[3] = {1U, 2U, 3U};
  unsigned logical_before_object[2] = {4U, 5U};
  unsigned other = 9U;
  unsigned long pointer_bits = (unsigned long)&other;
  __CPROVER_assert(logical_before_object[i] == 5U,
                  "check logical array before addressable object");
  __CPROVER_assert(pointer_bits != 0UL && other == 9U,
                  "check object identity integer cast");
  __CPROVER_assert(0, "optimization-reached");
}
