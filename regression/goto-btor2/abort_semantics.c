// Test Problem 4: abort() semantics
// Before fix: abort() generated a global constraint (¬χ_l), which
//   removes the abort location from the reachable set entirely.
//   This makes abort itself unreachable — unsound for reachability.
// After fix:  abort() is encoded as a terminal self-loop (PC sticks
//   at loc). The location is reachable but has no forward transition.
// Expected: the assertion after abort is never reached (it holds
//   vacuously because abort terminates the path).
int main()
{
  int x = __VERIFIER_nondet_int();

  if(x < 0)
  {
    abort();
    // This code is unreachable in C semantics.
    __CPROVER_assert(0, "unreachable after abort");
  }

  // Only reachable if x >= 0.
  __CPROVER_assert(x >= 0, "x must be non-negative here");
  return 0;
}
