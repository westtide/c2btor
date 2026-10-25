extern unsigned __VERIFIER_nondet_uint(void);
extern void reach_error(void);

int main(void)
{
  unsigned current = __VERIFIER_nondet_uint();
  unsigned first = current;
  current = __VERIFIER_nondet_uint();
  unsigned sum = first + current;
  if(sum == 14U && first == 5U && current == 9U)
    reach_error();
}
