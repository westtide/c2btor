#include <assert.h>

int main(void)
{
  int a = 1, b = 2;
  _Bool choose_a;
  int *p = choose_a ? &a : &b;
  *p = 3;
  assert(choose_a ? a == 3 : b == 3);
  assert(choose_a ? b == 2 : a == 1);
}
