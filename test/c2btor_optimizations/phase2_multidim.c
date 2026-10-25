extern unsigned __VERIFIER_nondet_uint(void);

int main(void)
{
  unsigned r = __VERIFIER_nondet_uint();
  unsigned c = __VERIFIER_nondet_uint();
  unsigned a[2][3] = {{1U, 2U, 3U}, {4U, 5U, 6U}};
  a[r][c] = 40U;
  a[r][c] = a[r][c] + 2U;
  __CPROVER_assert(a[r][c] == 42U, "check multidimensional element");
  __CPROVER_assert(a[0][0] == 1U && a[1][2] == 6U, "check untouched rows");
  __CPROVER_assert(0, "optimization-reached");
}
