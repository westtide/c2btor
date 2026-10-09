#include <assert.h>

static int fib(int n)
{
  if(n <= 1)
    return n;
  int a = 0;
  int b = 1;
  for(int i = 2; i <= n; ++i)
  {
    int tmp = a + b;
    a = b;
    b = tmp;
  }
  return b;
}

int main(void)
{
  assert(fib(0) == 0);
  assert(fib(1) == 1);
  assert(fib(5) == 5);
  assert(fib(6) == 9);
  return 0;
}
