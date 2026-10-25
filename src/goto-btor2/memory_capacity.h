// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_MEMORY_CAPACITY_H
#define CPROVER_GOTO_BTOR2_MEMORY_CAPACITY_H

#include <util/expr.h>
#include <util/mp_arith.h>
#include <util/namespace.h>

#include <goto-programs/goto_program.h>

#include <map>
#include <optional>
#include <set>
#include <utility>
#include <vector>

/// Upper bounds at object declarations/allocation sites in the final GotoIR.
/// Analysis does not instrument the program or restrict its input values.
struct memory_capacity_boundst
{
  struct allocation_size_infot
  {
    const goto_programt::instructiont *instruction;
    // This is the already-lowered byte-count expression, including argument
    // conversions. The interval is descriptive; it never restricts execution.
    exprt alloc_size_expr;
    std::optional<std::pair<mp_integer, mp_integer>> interval;
  };
  std::map<irep_idt, mp_integer> objects;
  mp_integer allocation = 0;
  bool allocation_complete = true;
  std::vector<allocation_size_infot> allocation_sizes;
  std::set<const goto_programt::instructiont *> unknown_indirect_writes;
  // Optional expression intervals immediately before conditional branches.
  // Used only by the private counted-loop sizing analysis.
  std::map<
    const goto_programt::instructiont *,
    std::map<exprt, std::pair<mp_integer, mp_integer>>>
    condition_intervals;
};

memory_capacity_boundst infer_memory_capacity(
  const goto_programt &program,
  const namespacet &ns,
  const std::map<irep_idt, exprt> &object_sizes,
  bool collect_condition_intervals = false);

// Analysis-copy annotation; never attached to the emitted GotoIR.
constexpr const char *C2BTOR_ALLOCATION_MULTIPLIER =
  "C_c2btor_allocation_multiplier";
mp_integer allocation_evaluation_weight(const goto_programt::instructiont &);

/// Bound allocation evaluations on any final-CFG path, saturating at budget.
/// An allocation cycle reaches budget. The caller must distinguish saturation
/// from a finite bound; this analysis adds no runtime guards or constraints.
unsigned infer_allocation_slots(const goto_programt &program, unsigned budget);

#endif
