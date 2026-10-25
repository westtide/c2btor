extern void *__VERIFIER_nondet_pointer(void);
extern unsigned __VERIFIER_nondet_uint(void);

static unsigned long pointer_integer(unsigned *pointer)
{
  return (unsigned long)pointer;
}

int main(void)
{
  void *generic = __VERIFIER_nondet_pointer();
  unsigned i = __VERIFIER_nondet_uint();
  unsigned unused_array[3] = {1U, 2U, 3U};
  unsigned fallback_array[2] = {4U, 5U};
  unsigned other = 9U;
  unsigned long pointer_bits = pointer_integer(&other);
  if(generic)
    *(unsigned *)generic = 77U;
  __CPROVER_assert(fallback_array[i] == 5U && other == 9U,
                  "check fixed-null generic pointer leaves object bytes intact");
  __CPROVER_assert(pointer_bits != 0UL && other == 9U,
                  "check generic-alias object identity integer cast");
  __CPROVER_assert(0, "optimization-reached");
}
