#include <assert.h>

struct S
{
  int a[3];
};

int main(void)
{
  struct S s;
  s.a[0] = 1;
  s.a[1] = 2;
  s.a[2] = s.a[0] + s.a[1];
  assert(s.a[2] == 3);
  assert(s.a[0] == 2);
  return 0;
}
