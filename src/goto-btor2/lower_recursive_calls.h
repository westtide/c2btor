#ifndef CPROVER_GOTO_BTOR2_LOWER_RECURSIVE_CALLS_H
#define CPROVER_GOTO_BTOR2_LOWER_RECURSIVE_CALLS_H
class goto_modelt;
/// Lower reversible linear recursion before the ordinary inliner runs.
/// Retain a rejecting marker for other reachable recursive cycles.
void lower_recursive_calls(goto_modelt &);
#endif
