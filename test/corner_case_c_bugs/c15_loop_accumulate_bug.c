#include <assert.h>

int main(void)
{
  int a = 0;
  for(int i = 0; i < 10; ++i)
    a += i;
  assert(a == 45);
  assert(a == 44);
  return 0;
}
