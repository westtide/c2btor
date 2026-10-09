// Differential storage regressions. Both representations share the C program,
// target, properties and lifetime rules. COMPLETE checks reachability, not SAFE.
extern int __VERIFIER_nondet_int(void);
extern void *malloc(__CPROVER_size_t);
extern void free(void *);
extern void *memcpy(void *, const void *, __CPROVER_size_t);
extern void *memmove(void *, const void *, __CPROVER_size_t);
extern void *memset(void *, int, __CPROVER_size_t);
static int zero_array[3];
static char text[5] = "abc";
struct item { signed char tag; int value; int values[2]; };
int main(void)
{
#if CASE == 1
  int a[3] = {3, 5, 7};
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(i >= 0 && i < 3);
  a[i] = 11;
#ifdef BUG
  __CPROVER_assert(a[i] == 12, "deliberate-source-bug");
#else
  __CPROVER_assert(a[i] == 11 && a[(i+1)%3] == 3+2*((i+1)%3), "symbolic-read-write");
#endif
#elif CASE == 2
  int partial[4] = {9};
  int designated[4] = {[2] = 17};
  __CPROVER_assert(zero_array[2] == 0 && text[3] == 0 && text[4] == 0 &&
                  partial[0] == 9 && partial[3] == 0 &&
                  designated[0] == 0 && designated[2] == 17, "initialization");
#elif CASE == 3
  signed char c[2] = {-7, 3};
  unsigned short s[2] = {65535, 1};
  unsigned long long w[2] = {0x123456789abcdef0ULL, 0};
  _Bool b[2] = {0, 1};
  float f[2] = {1.5f, -2.0f};
  c[1] = c[0]; s[1] = s[0]; w[1] = w[0]; f[1] = f[0];
  __CPROVER_assert(c[1] == -7 && s[1] == 65535 &&
                  w[1] == 0x123456789abcdef0ULL && b[0] == 0 && b[1] == 1 &&
                  f[1] == 1.5f, "element-types");
#elif CASE == 4
  int rows[2][3] = {{1, 2, 3}, {4, 5, 6}};
  int (*p)[3] = rows;
  int j = __VERIFIER_nondet_int();
  __CPROVER_assume(j >= 0 && j < 3);
  int *q = &rows[1][0];
  p[1][j] = 19;
  __CPROVER_assert(q[j] == 19 && rows[0][2] == 3 && &q[2]-q == 2, "matrix-alias");
#elif CASE == 5
  int a[2] = {3, 7};
  int *p[2] = {&a[1], &a[0]};
  int **q = p;
  *q[0] = 23;
  __CPROVER_assert(a[1] == 23 && *p[1] == 3 && p[0] == &a[1], "pointer-elements");
#elif CASE == 6
  struct item a[2] = {{1, 2, {3, 4}}, {5, 6, {7, 8}}};
  struct item b[2];
  b[0] = a[1]; b[1] = a[0];
  a[1].values[1] = 99;
  __CPROVER_assert(b[0].tag == 5 && b[0].values[1] == 8 &&
                  b[1].value == 2 && a[1].values[1] == 99, "aggregate-copy");
#elif CASE == 7
  int n = __VERIFIER_nondet_int();
  __CPROVER_assume(n >= 1 && n <= 4);
  int saved = n;
  int a[n];
  for(int i = 0; i < n; ++i) a[i] = i + 7;
  n = 20;
  __CPROVER_assert(a[saved-1] == saved+6 && sizeof(a) == saved*sizeof(int), "vla-latched-size");
#elif CASE == 8
  unsigned char a[4] = {1, 2, 3, 4};
  unsigned char b[4];
  memmove(a + 1, a, 3);
  memcpy(b, a, 4);
  memset(b + 2, 0x123, 2);
  __CPROVER_assert(a[0] == 1 && a[1] == 1 && a[2] == 2 && a[3] == 3 &&
                  b[0] == 1 && b[1] == 1 && b[2] == 0x23 && b[3] == 0x23, "byte-copy-fill");
#elif CASE == 9
  int n = __VERIFIER_nondet_int();
  __CPROVER_assume(n >= 1 && n <= 4);
  int *a = malloc(n * sizeof(int));
  int *p = a + n - 1;
  *p = 37;
  __CPROVER_assert(a[n-1] == 37 && __CPROVER_OBJECT_SIZE(a) == n*sizeof(int), "dynamic-array");
  free(a);
#elif CASE == 10
  int a[2] = {1, 2};
  int x = a[-1];
  __CPROVER_assert(x == 0, "negative-index-must-fault");
#elif CASE == 11
  int a[2] = {1, 2};
  unsigned long long i = 1ULL << 32;
  a[i] = 9;
#elif CASE == 12
  int n = __VERIFIER_nondet_int();
  __CPROVER_assume(n == 5);
  int a[n];
  a[4] = 13;
  __CPROVER_assert(a[4] == 13, "vla-capacity");
#elif CASE == 13
  int *a = malloc(5*sizeof(int));
  a[4] = 13;
  __CPROVER_assert(a[4] == 13, "allocation-capacity");
#elif CASE == 14
  unsigned char a[1] = {1};
  a[256] = 9;
#elif CASE == 15
  int a[2];
  __CPROVER_assert(a[0] == 0, "indeterminate-existing-model-limit");
#elif CASE == 16
  unsigned short a[2] = {0x1122, 0x3344};
  unsigned char *bytes = (unsigned char *)a;
  bytes[0] = 0x55;
#ifdef BIG_ENDIAN
  __CPROVER_assert(a[0] == 0x5522 && a[1] == 0x3344, "big-endian-byte-view");
#else
  __CPROVER_assert(a[0] == 0x1155 && a[1] == 0x3344, "little-endian-byte-view");
#endif
#endif
#ifdef COMPLETE
  __CPROVER_assert(0, "completion");
#endif
  return 0;
}
