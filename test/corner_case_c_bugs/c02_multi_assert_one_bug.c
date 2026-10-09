#include <assert.h>

int main(void)
{
  int a = 1;
  int b = 2;
  int c = a + b;
  int d = c - a;
  assert(c == 3);
  assert(d == 1);
  assert(a == 2);
  return 0;
}
