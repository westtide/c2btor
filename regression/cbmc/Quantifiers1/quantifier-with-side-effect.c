int main()
{
  int j = 0;
  // clang-format off
  // no side effects!
  assert(__CPROVER_forall { int i; ({ j = 1; j; }) });
  // clang-format on

  return 0;
}
