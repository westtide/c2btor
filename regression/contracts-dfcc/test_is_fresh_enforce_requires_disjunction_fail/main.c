void foo(int *x)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)) || 1)
  __CPROVER_assigns(*x)
// clang-format on
{
  *x = 0;
}

void main()
{
  int *x;
  foo(x);
}
