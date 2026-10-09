int recur(int n)
{
  return n == 0 ? 0 : recur(n - 1) + 1;
}
int main(void)
{
  __CPROVER_assert(recur(2) == 2, "real recursive call remains unsupported");
}
