int main(void)
{
  unsigned unused[100000000];
  unsigned x = 9U;
  __CPROVER_assert(x == 9U, "check computed value");
  __CPROVER_assert(0, "optimization-reached");
}
