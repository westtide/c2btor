#include <stdlib.h>
typedef struct
{
  int *x;
  int *y;
} ret_t;

ret_t foo()
  // clang-format off
  __CPROVER_ensures((
      __CPROVER_is_fresh(__CPROVER_return_value.x, sizeof(int)) &&
      __CPROVER_return_value.y == NULL
    ) || (
      __CPROVER_return_value.x == NULL &&
      __CPROVER_is_fresh(__CPROVER_return_value.y, sizeof(int))
    ))
  // clang-format on
  ;

void bar()
{
  ret_t ret = foo();
  int *x = ret.x;
  int *y = ret.y;
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
  bar();
}
