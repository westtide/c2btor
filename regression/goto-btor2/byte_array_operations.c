#include <string.h>

int main(void)
{
  unsigned char a[4] = {1, 2, 3, 4};
  unsigned char b[6] = {9, 9, 9, 9, 9, 9};
  __CPROVER_array_replace(b, a);
  __CPROVER_array_set(a, 7);
  __CPROVER_assert(
    b[0] == 1 && b[3] == 4 && b[4] == 9, "replace copies prefix only");
  __CPROVER_array_copy(a, b);
#ifdef NEGATIVE
  __CPROVER_assert(a[2] == 9, "negative copy control");
#else
  __CPROVER_assert(
    a[0] == 1 && a[2] == 3 && a[3] == 4, "copy uses destination extent");
#endif
  memset(b + 1, 5, 3);
  __CPROVER_assert(
    b[0] == 1 && b[1] == 5 && b[3] == 5 && b[4] == 9, "partial memset");
  memcpy(a, b, 4);
  __CPROVER_assert(a[0] == 1 && a[3] == 5, "memcpy bytes");
}
