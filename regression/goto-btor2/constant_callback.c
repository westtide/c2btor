/* Reproducer: unrelated address-taken callbacks have ABI-incompatible args.
 * The real target is carried through a context and two direct calls.
 */
typedef unsigned char byte;
struct backend
{
  int (*prepare)(byte *, int);
  int (*unrelated)(const byte *, int *);
};
struct context
{
  const struct backend *backend;
};
static int prepare(byte *p, int n)
{
  return n + *p;
}
static int unrelated(const byte *p, int *n)
{
  return *n;
}
static int alternate(byte *p, int n)
{
  return n - *p;
}
#ifdef NO_DISTRACTOR
#  define UNRELATED_TARGET 0
#else
#  define UNRELATED_TARGET unrelated
#endif
static const struct backend first = {prepare, UNRELATED_TARGET};
static const struct backend second = {alternate, UNRELATED_TARGET};
extern int nondet_int(void);

static int send(struct context *ctx, byte *p, int n)
{
  return ctx->backend->prepare(p, n);
}
static int reply(struct context *ctx, byte *p)
{
  return send(ctx, p, 7);
}
int main(void)
{
  byte p = 2;
  struct context ctx = {&first};
#ifdef DYNAMIC_TARGET
  int choose_second = nondet_int();
  if(choose_second)
    ctx.backend = &second;
#endif
#ifdef ALIAS_WRITE
  struct context *alias = &ctx;
  alias->backend = &second;
#endif
#ifdef LOOP_TARGET
  for(int i = 0; i < 2; ++i)
    ctx.backend = &second;
#endif
#ifdef UNKNOWN_WRITE
  extern void unknown_write(struct context *);
  unknown_write(&ctx);
#endif
  int result = reply(&ctx, &p);
#if defined(ALIAS_WRITE) || defined(LOOP_TARGET)
  __CPROVER_assert(result == 5, "alias write selects alternate");
#elif defined(DYNAMIC_TARGET)
#  ifdef NEGATIVE_CONTROL
  __CPROVER_assert(result == 9, "alternate must remain reachable");
#  else
  __CPROVER_assert(result == (choose_second ? 5 : 9), "both targets preserved");
#  endif
#else
#  ifdef NEGATIVE_CONTROL
  __CPROVER_assert(result != 9, "known callback negative control");
#  else
  __CPROVER_assert(result == 9, "known callback returns 9");
#  endif
#endif
}
