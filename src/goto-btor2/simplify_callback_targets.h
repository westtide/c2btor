#ifndef CPROVER_GOTO_BTOR2_SIMPLIFY_CALLBACK_TARGETS_H
#define CPROVER_GOTO_BTOR2_SIMPLIFY_CALLBACK_TARGETS_H

#include <util/source_location.h>
#include <vector>

class goto_programt;
class symbol_tablet;
class messaget;
/// Fold provably constant dispatch guards after inlining, before BTOR2 lowering.
/// Unknown stores/calls discard facts; joins retain only facts common to all edges.
/// If requested, retain the source locations of assertions and error calls
/// turned into skips by CFG reachability, before those skips are erased.
void simplify_callback_targets(
  goto_programt &,
  const symbol_tablet &,
  messaget &,
  std::vector<source_locationt> *unreachable_assertions = nullptr);

#endif
