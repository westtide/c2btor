extern unsigned __VERIFIER_nondet_uint(void);
extern void reach_error(void);

int main(void)
{
  unsigned first = __VERIFIER_nondet_uint();
  unsigned second = __VERIFIER_nondet_uint();
  unsigned first_copy = first;
  unsigned second_copy = second;
  unsigned final_copy = first_copy;
  if(final_copy == 5U && second_copy == 9U)
    reach_error();
}
