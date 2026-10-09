extern void *malloc(unsigned long);
extern void free(void *);
extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_error(void);
struct node { int value; struct node *next; };
int main(void) {
  int x = __VERIFIER_nondet_int();
  struct node *p = malloc(sizeof(*p));
  struct node *q = malloc(sizeof(*q));
  if (!p || !q) return 0;
  p->value = x; p->next = 0;
  q->value = 2; q->next = p;
#ifdef USE_AFTER_FREE
  free(p);
#endif
  if (q->next->value == 7)
    __VERIFIER_error();
  return 0;
}
