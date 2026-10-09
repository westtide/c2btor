#include <assert.h>
#include <stddef.h>

int main(void)
{
  unsigned char bytes[5] = {1, 2, 3, 4, 5};
  __builtin_bzero(bytes + 1, 3);
  assert(bytes[0] == 1 && bytes[4] == 5);
  assert(bytes[1] == 0 && bytes[2] == 0 && bytes[3] == 0);
  __builtin_bzero(NULL, 0);
}
