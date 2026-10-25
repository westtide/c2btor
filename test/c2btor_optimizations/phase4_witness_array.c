extern unsigned __VERIFIER_nondet_uint(void);
extern void reach_error(void);

int main(void)
{
  unsigned first = __VERIFIER_nondet_uint();
  unsigned second = __VERIFIER_nondet_uint();
  unsigned a[2] = {0U, 0U};
  a[0] = first;
  a[1] = second;
  unsigned copied = a[1];
  if(a[0] + copied == 14U && a[0] == 5U && copied == 9U)
    reach_error();
}
