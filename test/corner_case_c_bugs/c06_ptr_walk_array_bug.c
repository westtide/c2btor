#include <assert.h>

int main(void)
{
  int a[3] = {0, 0, 0};
  int *p = &a[0];
  *p = 1;
  p = p + 1;
  *p = 2;
  p = p + 1;
  *p = 3;
  assert(a[0] == 1);
  assert(a[1] == 2);
  assert(a[2] == 4);
  return 0;
}
