struct packet { int values[2]; };
extern int nondet_int(void);
int main(void)
{
  struct packet a = {{11, 12}}, b = {{21, 22}};
  _Bool choose = nondet_int();
  struct packet *p = choose ? &a : &b;
  int i = nondet_int();
  __CPROVER_assume(i >= 0 && i < 2);
  __CPROVER_assert(p->values[i] == (choose ? 11 : 21) + i,
                   "runtime member array read");
  p->values[i] = 42;
#ifdef NEGATIVE
  __CPROVER_assert(p->values[i] != 42, "negative runtime member write");
#else
  __CPROVER_assert(p->values[i] == 42, "runtime member array write");
#endif
}
