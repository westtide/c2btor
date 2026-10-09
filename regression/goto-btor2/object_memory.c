extern int __VERIFIER_nondet_int(void);
extern void *malloc(__CPROVER_size_t);
extern void free(void *);
extern void *memcpy(void *, const void *, __CPROVER_size_t);
extern int memcmp(const void *, const void *, __CPROVER_size_t);
int main(void)
{
#if CASE == 1
  int a[3] = {1, 2, 3}, b[3] = {4, 5, 6};
  int choose = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(i >= 0 && i < 3);
  int *p = choose ? &a[0] : &b[0];
  p[i] = 77;
  __CPROVER_assert(p[i] == 77 && (choose ? b[i] == i+4 : a[i] == i+1), "dispatch-and-frame");
#elif CASE == 2
  union U { unsigned int word; unsigned char bytes[sizeof(unsigned int)]; } u;
  u.word = 0x11223344;
  u.bytes[1] = 0x55;
#ifdef BIG_ENDIAN
  __CPROVER_assert(u.word == 0x11553344, "union-byte-view");
#else
  __CPROVER_assert(u.word == 0x11225544, "union-byte-view");
#endif
#elif CASE == 3
  unsigned char a[3] = {1, 2, 3}, b[3] = {1, 2, 3};
  __CPROVER_assert(memcmp(a, b, 3) == 0, "memcmp-equal");
  b[1] = 4;
  __CPROVER_assert(memcmp(a, b, 3) < 0 && memcmp(b, a, 3) > 0, "memcmp-sign");
#elif CASE == 4
  int *p;
  { int x = 7; p = &x; }
  __CPROVER_assert(*p == 7, "expired-local");
#elif CASE == 5
  int a[3] = {1, 2, 3};
  int *p = a+1, *q = a+3;
  __CPROVER_assert(p < q && q-p == 2 && q-1 == &a[2] && p != q, "pointer-operations");
#elif CASE == 6
  int x = 4;
  __CPROVER_size_t i = (__CPROVER_size_t)&x;
  int *p = (int *)i;
  __CPROVER_assert(*p == 4, "unsupported-integer-pointer");
#elif CASE == 7
  unsigned char *p = malloc(1025);
  p[1024] = 7;
#elif CASE == 8
  for(int i=0; i<2; ++i)
  { int a[1]; a[0]=i; __CPROVER_assert(a[0]==i, "repeated-lifetime"); }
#elif CASE == 9
  int *p = 0;
  *p = 7;
#elif CASE == 10
  int a[3] = {1, 2, 3};
  int b[3] = {4, 5, 6};
  unsigned char *dst = (unsigned char *)b;
  unsigned char *src = (unsigned char *)a;
  memcpy(dst + 1, src + 1, sizeof(a) - 2);
#ifdef BIG_ENDIAN
  __CPROVER_assert(b[0] == 1 && b[1] == 2 && b[2] == 6, "partial-element-copy");
#else
  __CPROVER_assert(b[0] == 4 && b[1] == 2 && b[2] == 3, "partial-element-copy");
#endif
#endif
#ifdef COMPLETE
  __CPROVER_assert(0, "completion");
#endif
}
