// Two explicitly named assembler symbols must alias each other, including
// labels which do not start with Darwin's ordinary C-symbol prefix.
int first(int) __asm__("raw_target");
int second(int) __asm__("raw_target");
int second(int x) { return x + 1; }
int raw_target(int x) { return x + 2; }
int main(void)
{
#ifdef __APPLE__
  __CPROVER_assert(first(3) == 4 && raw_target(3) == 5, "raw assembler alias");
#endif
}
