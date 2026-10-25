int main(void)
{
  unsigned n = 2U;
  unsigned a[n++];
  unsigned other = 9U;
  __CPROVER_assert(n == 3U && &other != 0,
                  "check frontend-lowered VLA dimension side effect");
  __CPROVER_assert(0, "optimization-reached");
}
