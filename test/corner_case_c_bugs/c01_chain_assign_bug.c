#include <assert.h>

int main(void)
{
  int x = 0;
  int y = x;
  int z = y;
  assert(z == 1);
  return 0;
}
