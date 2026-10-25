extern unsigned __VERIFIER_nondet_uint(void);
extern void reach_error(void);

int main(void)
{
  unsigned first = __VERIFIER_nondet_uint();
  unsigned second = __VERIFIER_nondet_uint();
  unsigned values[2] = {0U, 0U};
  values[0] = first;
  values[1] = second;
  unsigned copied = values[first & 1U];
  if(copied == 9U && values[0] == 5U)
    reach_error();
}
