// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_ARRAY_RELATION_PRUNING_H
#define CPROVER_GOTO_BTOR2_ARRAY_RELATION_PRUNING_H

#include <util/irep.h>

#include <cstddef>
#include <set>

class goto_programt;
class namespacet;

/// Propagate must-equality of complete array values established only by
/// c2btor_certified_array_copy instructions. The supplied roots must have the
/// summarizer's closed-use, in-bounds certificate. Rewrite only direct element
/// equality/inequality at identical indices; retain all source properties.
/// Writes and lifetime events kill the affected value's relations, unknown
/// effects clear all facts, and joins intersect predecessor facts.
std::size_t prune_equal_array_comparisons(
  goto_programt &,
  const namespacet &,
  const std::set<irep_idt> &certified_arrays);

/// At the same must-equality fixed point, replace a direct element read by a
/// read from the lexically smallest typed root in its equivalence class. Only
/// assignment RHSs and instruction conditions are rewritten; lvalues and
/// whole-array copy instructions retain their original roots. This is an
/// exact expression substitution, not a loop or assertion abstraction.
std::size_t prune_equal_array_reads(
  goto_programt &,
  const namespacet &,
  const std::set<irep_idt> &certified_arrays);

#endif
