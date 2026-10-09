// Darwin C names and assembler names occupy different namespaces.
#ifdef __APPLE__
#  define ASM_NAME "_connect"
#else
#  define ASM_NAME "connect"
#endif
int system_connect(int, int, int) __asm__(ASM_NAME);
int connect(int a, int b, int c)
{
  return a + b + c;
}
static int _connect(int a, int b, int c, int d)
{
  return system_connect(a, b, c) + d;
}
int main(void)
{
#ifdef NEGATIVE_CONTROL
  __CPROVER_assert(_connect(1, 2, 3, 4) == 11, "distinct connect functions");
#else
  __CPROVER_assert(_connect(1, 2, 3, 4) == 10, "distinct connect functions");
#endif
}
