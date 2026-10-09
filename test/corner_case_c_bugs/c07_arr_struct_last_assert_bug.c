#include <assert.h>

struct Pair
{
  int a;
  int b;
};

int main(void)
{
  struct Pair arr[2];
  arr[0].a = 1;
  arr[0].b = 2;
  arr[1].a = arr[0].a + arr[0].b;
  arr[1].b = arr[1].a + arr[0].b;
  assert(arr[0].a == 1);
  assert(arr[0].b == 2);
  assert(arr[1].a == 3);
  assert(arr[1].b == 6);
  assert(arr[0].a == 2);
  return 0;
}
