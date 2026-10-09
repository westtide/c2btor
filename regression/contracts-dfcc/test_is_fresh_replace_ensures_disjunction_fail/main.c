int *foo()
  // clang-format off
  __CPROVER_ensures(
    __CPROVER_is_fresh(__CPROVER_return_value, sizeof(int)) || 1);
// clang-format on

void bar()
{
  int *x = foo();
  *x = 0; //expected to fail
}
void main()
{
  bar();
}
