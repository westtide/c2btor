void foo(int *x, int *y)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)))
  __CPROVER_requires(__CPROVER_pointer_equals(y, x) || 1)
  __CPROVER_assigns(*y)
// clang-format on
{
  *y = 0;
}

void main()
{
  int *x;
  int *y;
  foo(x, y);
}
