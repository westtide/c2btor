extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned i = __VERIFIER_nondet_uint();
  unsigned char a[4];
  unsigned char before = a[i];
  a[(i + 1U) & 3U] = 19U;
  unsigned char after = a[i];
  __CPROVER_assert(before == after, "check stable unwritten byte contract");
  __CPROVER_assert(a[(i + 1U) & 3U] == 19U, "check neighboring byte write");
  __CPROVER_assert(0, "optimization-reached");
}
