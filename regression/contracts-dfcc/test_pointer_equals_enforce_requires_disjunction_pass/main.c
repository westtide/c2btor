#include <stdlib.h>
void foo(int *a, int *x, int *y)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(a, sizeof(int)))
  __CPROVER_requires(
    (__CPROVER_pointer_equals(x,a) && y == NULL) ||
    (x == NULL && __CPROVER_pointer_equals(y,a))
  )
  __CPROVER_assigns(y == NULL: *x)
  __CPROVER_assigns(x == NULL: *y)
// clang-format on
{
  if(y == NULL)
  {
    assert(0);
    assert(__CPROVER_same_object(a, x));
    *x = 0;
  }
  else
  {
    assert(0);
    assert(x == NULL);
    assert(__CPROVER_same_object(a, y));
    *y = 0;
  }
}

void main()
{
  int *a;
  int *x;
  int *y;
  foo(a, x, y);
}
