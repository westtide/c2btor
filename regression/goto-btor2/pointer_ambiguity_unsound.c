// Test Problem 1: Flow-insensitive pointer unsoundness
// Before fix: *p always writes to the LAST registered target (b),
//   so 'a' never gets 0xBAD → false negative (assertion wrongly holds).
// After fix:  pointer 'p' is detected as ambiguous; the write *p=0xBAD
//   is applied to ALL known targets, so 'a' correctly gets 0xBAD.
// Expected: assertion a==0 is VIOLATED (a == 0xBAD != 0).
int main()
{
  int a = 0;
  int b = 0;
  int *p;
  int i = 0;

  while(i < 2)
  {
    if(i == 0)
      p = &a;
    else
      p = &b;
    *p = 0xBAD;
    i++;
  }

  // Real behavior: a == 0xBAD, so this assertion is violated.
  __CPROVER_assert(a == 0, "a must be 0");
  return 0;
}
