#include <assert.h>

struct Outer
{
  struct Inner
  {
    int x;
    int y;
  } inner;
  int z;
};

int main(void)
{
  struct Outer o;
  o.inner.x = 1;
  o.inner.y = 2;
  o.z = o.inner.x + o.inner.y;
  assert(o.z == 3);
  assert(o.inner.x == 2);
  return 0;
}
