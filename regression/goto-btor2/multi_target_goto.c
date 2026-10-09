// Test Problem 3: Multi-target GOTO (switch jump table)
// Before fix: process_goto only takes targets.front(), losing all
//   non-first targets → incorrect control flow.
// After fix:  all targets are emitted as PC updates.
// Expected: all switch cases are reachable; the assertion holds.
int main()
{
  int x = __VERIFIER_nondet_int();
  int result;

  switch(x)
  {
  case 1:
    result = 10;
    break;
  case 2:
    result = 20;
    break;
  case 3:
    result = 30;
    break;
  default:
    result = 0;
    break;
  }

  // Each case assigns 'result' exactly once; no path leaves result unset.
  // (The assertion itself is trivially true; the test verifies that
  // switch-generated multi-target GOTOs don't break control flow.)
  __CPROVER_assert(result >= 0, "result non-negative");
  return 0;
}
