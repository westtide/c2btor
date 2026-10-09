void foo()
{
  // Initialize them with `nondet_int` to avoid them being ignored by DFCC.
  // DFCC ignores variables that are not read/written to outside the loop
  // or in the loop contracts.
  int nondet_var = nondet_int();
  int __VERIFIER_var = nondet_int();
  int __CPROVER_var = nondet_int();
  for(int i = 10; i > 0; i--)
    // clang-format off
  __CPROVER_assigns(i,nondet_var, __VERIFIER_var, __CPROVER_var)
  __CPROVER_loop_invariant(0 <= i && i <= 10)
  __CPROVER_decreases(i)
    // clang-format on
    {
      nondet_var = 0;
      __VERIFIER_var = 0;
      __CPROVER_var = 0;
    }
}

int main()
{
  foo();
  return 0;
}
