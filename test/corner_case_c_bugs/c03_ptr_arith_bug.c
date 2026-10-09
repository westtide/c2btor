#include <assert.h>

int main(void)
{
  int a[2] = {0, 0};
  a[0] = 10;
  a[1] = 20;
  int *p = &a[0];
  int v0 = *p;
  int v1 = *(p + 1);
  assert(v0 == 10);
  assert(v1 == 21);
  return 0;
}
