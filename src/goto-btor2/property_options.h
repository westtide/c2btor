#ifndef CPROVER_GOTO_BTOR2_PROPERTY_OPTIONS_H
#define CPROVER_GOTO_BTOR2_PROPERTY_OPTIONS_H

#include <util/source_location.h>

#include <string>
#include <vector>

struct btor2_property_optionst
{
  std::string error_function;
  bool reach_only = false;
  bool merge = false;
  // Suppress auxiliary properties while keeping memory-fault halting active.
  bool no_heap_guards = false;
  // These assertions were removed by CFG reachability after constant folding.
  // Their violation predicates are false, rather than missing queries.
  std::vector<source_locationt> unreachable_assertions;
};

#endif
