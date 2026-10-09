// Test Problem 5: assert-failure control flow
// Before fix: after assert(c) fails, PC continues to loc+1, allowing
//   "zombie paths" to execute post-assert code and trigger spurious
//   bad states.
// After fix:  assert(c) only allows PC to proceed when c holds.
//   If c fails, PC sticks at loc (simulating C's abort-on-fail).
// Expected: the post-assert assertion holds because the failed
//   assert path terminates.
int main()
{
  int x = __VERIFIER_nondet_int();

  __CPROVER_assert(x > 0, "x must be positive");

  // After the assert, x > 0 should hold on all surviving paths.
  __CPROVER_assert(x > 0, "x still positive");
  return 0;
}
