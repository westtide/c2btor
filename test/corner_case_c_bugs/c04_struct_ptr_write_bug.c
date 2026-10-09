#include <assert.h>

struct S
{
  int x;
  int y;
};

int main(void)
{
  struct S s = {0, 0};
  s.x = 5;
  s.y = 10;
  struct S *p = &s;
  p->x = p->x + p->y;
  assert(s.x == 15);
  assert(s.y == 11);
  return 0;
}
