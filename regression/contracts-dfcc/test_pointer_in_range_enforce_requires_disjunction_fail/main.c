void foo(int *x, int *y)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(x, 8*sizeof(int)))
  __CPROVER_requires(__CPROVER_pointer_in_range_dfcc(x, y, x+7) || 1)
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
