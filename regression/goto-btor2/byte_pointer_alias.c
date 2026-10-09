int main(void)
{
  signed char a[2] = {-1, -128};
  unsigned char b[2] = {128, 255};
  _Bool choice;
  unsigned char *p = choice ? (unsigned char *)a : b;
  signed char *q = choice ? (signed char *)b : a;
  __CPROVER_assert(p[1] == (choice ? 128 : 255), "byte read preserves bits");
  q[0] = -2;
#ifdef NEGATIVE
  __CPROVER_assert(p[1] == 0, "negative byte read control");
#else
  __CPROVER_assert(
    choice ? b[0] == 254 : a[0] == -2, "byte write preserves bits");
#endif
}
