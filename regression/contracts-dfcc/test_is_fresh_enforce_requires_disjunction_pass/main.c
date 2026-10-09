#include <stdlib.h>
void foo(int *x, int *y)
  // clang-format off
  __CPROVER_requires(
    (__CPROVER_is_fresh(x, sizeof(*x)) && y == NULL) ||
    (x == NULL && __CPROVER_is_fresh(y, sizeof(*y)))
  )
  __CPROVER_assigns(y == NULL: *x)
  __CPROVER_assigns(x == NULL: *y)
// clang-format on
{
  if(y == NULL)
  {
    assert(0);
    *x = 0;
  }
  else
  {
    assert(0);
    assert(x == NULL);
    *y = 0;
  }
}

void main()
{
  int *x;
  int *y;
  foo(x, y);
}
