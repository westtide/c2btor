#include <stdlib.h>
typedef struct
{
  int *a;
  int *x;
  int *y;
} ret_t;

ret_t foo()
  // clang-format off
  __CPROVER_ensures(__CPROVER_is_fresh(__CPROVER_return_value.a, sizeof(int)))
  __CPROVER_ensures((
      __CPROVER_pointer_equals(
        __CPROVER_return_value.x,
        __CPROVER_return_value.a) &&
      __CPROVER_return_value.y == NULL
    ) || (
      __CPROVER_return_value.x == NULL &&
      __CPROVER_pointer_equals(
        __CPROVER_return_value.y,
        __CPROVER_return_value.a)))
  // clang-format on
  ;

void bar()
{
  ret_t ret = foo();
  int *a = ret.a;
  int *x = ret.x;
  int *y = ret.y;
  if(y == NULL)
  {
    assert(0);
    assert(__CPROVER_same_object(x, a));
    *x = 0;
  }
  else
  {
    assert(0);
    assert(x == NULL);
    assert(__CPROVER_same_object(y, a));
    *y = 0;
  }
}

void main()
{
  bar();
}
