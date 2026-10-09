// Memory-rule regressions. CASE selects a semantic boundary, not a container
// special case. COMPLETE makes the terminal point reachable as a bad property
// so a bounded success cannot hide an unreachable program suffix.
extern void *malloc(__CPROVER_size_t);
extern void *calloc(__CPROVER_size_t, __CPROVER_size_t);
extern void *realloc(void *, __CPROVER_size_t);
extern void free(void *);
extern void *memcpy(void *, const void *, __CPROVER_size_t);
extern void *memmove(void *, const void *, __CPROVER_size_t);
extern void *memset(void *, int, __CPROVER_size_t);
struct node { int value; struct node *next; int items[2]; };
struct node global = {17, 0, {23, 31}};
struct flex { int count; int items[]; };
int main(void)
{
#if CASE == 1
  struct node *p = malloc(2 * sizeof(*p));
  p[0].value = 3; p[1].value = 8;
  int *q = &p[1].items[1];
  *q = 11;
  __CPROVER_assert(p[1].items[1] == 11 && p[0].value == 3 && p[1].value == 8, "views");
#elif CASE == 2
  int size = 3;
  int *p = calloc(size, sizeof(int));
  size = 9;
  __CPROVER_assert(p[0] == 0 && p[2] == 0 && __CPROVER_OBJECT_SIZE(p) == 3 * sizeof(int), "calloc-size");
#elif CASE == 3
  struct node *head = 0;
  for(int i = 0; i < 2; ++i)
  {
    struct node *p = malloc(sizeof(*p));
    p->value = i + 10;
    p->next = head;
    head = p;
  }
  __CPROVER_assert(head != head->next && head->value == 11 && head->next->value == 10, "fresh-loop");
#elif CASE == 4
  int *p = malloc(sizeof(int)); *p = 7; free(p);
  __CPROVER_assert(*p == 7, "use-after-free");
#elif CASE == 5
  int *p = malloc(sizeof(int)); free(p); free(p);
#elif CASE == 6
  int *p = malloc(2 * sizeof(int)); free(p + 1);
#elif CASE == 7
  free(0);
#elif CASE == 8
  int x = 5; int *q = &x; *q = 9;
  struct node *p = &global;
  __CPROVER_assert(x == 9 && p->value == 17 && p->items[1] == 31, "static-local-alias");
  const char *s = "abc";
  __CPROVER_assert(s[1] == 'b' && s[3] == 0, "string");
#elif CASE == 9
  unsigned value = 0;
  unsigned char *p = (unsigned char *)&value;
  p[1] = 99;
  __CPROVER_assert(p[1] == 99 && p[0] == 0, "byte-alias");
#elif CASE == 10
  struct flex *p = malloc(sizeof(*p) + 3 * sizeof(int));
  p->count = 3; p->items[2] = 41;
  __CPROVER_assert(p->count == 3 && p->items[2] == 41, "flexible-tail");
#elif CASE == 11
  int rows[2][3] = {{1,2,3}, {4,5,6}};
  int *p[2] = {rows[1], rows[0]};
  int **q = p;
  q[0][1] = 19;
  __CPROVER_assert(rows[1][1] == 19 && q[1][2] == 3 && &rows[1][2] - &rows[1][0] == 2, "multilevel");
#elif CASE == 12
  void *p = calloc((__CPROVER_size_t)-1, 2);
  __CPROVER_assert(p == 0, "calloc-overflow");
#elif CASE == 13
  struct node *p = malloc(sizeof(*p)), *q = malloc(sizeof(*q));
  p->value = 27; p->next = 0; p->items[0] = 2; p->items[1] = 3;
  memcpy(q, p, sizeof(*p));
  __CPROVER_assert(q->value == 27 && q->next == 0 && q->items[1] == 3, "copy-padding");
#elif CASE == 14
  unsigned char bytes[4] = {1,2,3,4};
  memmove(bytes + 1, bytes, 3);
  __CPROVER_assert(bytes[0] == 1 && bytes[1] == 1 && bytes[2] == 2 && bytes[3] == 3, "overlap-snapshot");
#elif CASE == 15
  int *p = malloc(2 * sizeof(int)); p[0] = 13; p[1] = 17;
  int *q = realloc(p, 3 * sizeof(int));
  __CPROVER_assert(q[0] == 13 && q[1] == 17, "realloc-prefix");
#elif CASE == 16
  int *p = malloc(sizeof(int));
  if(!p) return 0;
  *p = 37;
  int *q = realloc(p, 2 * sizeof(int));
  if(q) __CPROVER_assert(*q == 37, "realloc-success");
  else __CPROVER_assert(*p == 37, "realloc-failure");
#elif CASE == 17
  int *p = malloc(sizeof(int));
  int *q = malloc(sizeof(int));
  __CPROVER_assert(p != q, "capacity");
#elif CASE == 18
  int *p = malloc(sizeof(int));
  __CPROVER_assert(*p == 0, "indeterminate");
#elif CASE == 19
  int *p = malloc(sizeof(int)); p[1] = 4;
#elif CASE == 20
  int *p = malloc(sizeof(int)); *p = 3;
  __CPROVER_assert(*p == 4, "source-violation");
#elif CASE == 21
  struct bits { unsigned x : 3; } *p = malloc(sizeof(*p)); p->x = 2;
#elif CASE == 22
  struct node a[2], b[2];
  a[0].value=1; a[0].next=0; a[0].items[0]=2; a[0].items[1]=3;
  a[1].value=4; a[1].next=0; a[1].items[0]=5; a[1].items[1]=6;
  b[0]=a[1]; b[1]=a[0];
  __CPROVER_assert(b[0].value==4 && b[1].items[1]==3, "struct-array-copy");
#elif CASE == 23
  void *p = malloc(0); free(p);
#elif CASE == 24
  unsigned char *p = malloc(5);
  memset(p, 0x123, 5);
  __CPROVER_assert(p[0] == 0x23 && p[4] == 0x23, "fill");
#elif CASE == 25
  char p[3] = {1,2,3}; memcpy(p + 1, p, 2);
#endif
#ifdef COMPLETE
  __CPROVER_assert(0, "completion");
#endif
  return 0;
}
