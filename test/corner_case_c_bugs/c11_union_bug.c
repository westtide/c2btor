#include <assert.h>

union U
{
  int i;
  unsigned int u;
};

int main(void)
{
  union U val;
  val.i = -1;
  assert(val.u != 0);
  assert(val.i == 0);
  return 0;
}
