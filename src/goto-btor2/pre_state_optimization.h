// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_PRE_STATE_OPTIMIZATION_H
#define CPROVER_GOTO_BTOR2_PRE_STATE_OPTIMIZATION_H

#include <util/irep.h>
#include <util/source_location.h>

#include <cstddef>
#include <set>
#include <string>
#include <vector>

class goto_programt;
class namespacet;

/// Storage classification without constructing a heap or planning capacities.
struct pre_state_memory_symbolst
{
  std::set<irep_idt> symbols;
  std::set<irep_idt> addressed_symbols;
  bool arbitrary_pointer_input = false;
};

pre_state_memory_symbolst
scan_pre_state_memory_symbols(const goto_programt &, const namespacet &);

struct pre_state_optimization_reportt
{
  std::size_t before = 0, after = 0;
  std::size_t constants_replaced = 0, folded_guards = 0;
  std::size_t unreachable_instructions = 0;
  std::size_t assignments = 0, declarations = 0, lifetimes = 0;
  std::size_t removed_objects = 0;
  // Without reserving the original object universe, removing even an unused
  // root can change other pointers' tags, offset widths and integer casts.
  std::string skipped_reason;
  std::set<irep_idt> memory_symbols;
  std::set<irep_idt> forced_static_symbols;
  std::vector<source_locationt> unreachable_assertions;
};

/// Simplify typed scalar constants and project unobservable pure storage before
/// any memory capacity/lifetime plan is constructed. GOTO/ASSUME and unknown
/// effects remain observations; ASSERT never supplies an assumption. Removed
/// unreachable ASSERT locations are returned for the existing property map.
/// Pointer/string programs retain the original GOTO/storage universe until
/// identity reservations can preserve their encoded numeric pointer values.
pre_state_optimization_reportt
optimize_before_state(goto_programt &, const namespacet &);

#endif
