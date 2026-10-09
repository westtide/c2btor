#include <assert.h>

int main(void)
{
  int x = 5;
  int *p = &x;
  int **pp = &p;
  **pp = 10;
  assert(x == 10);
  assert(*p == 10);
  assert(**pp == 11);
  return 0;
}
