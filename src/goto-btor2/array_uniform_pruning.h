// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_ARRAY_UNIFORM_PRUNING_H
#define CPROVER_GOTO_BTOR2_ARRAY_UNIFORM_PRUNING_H

#include <util/irep.h>

#include <cstddef>
#include <set>

class goto_programt;
class namespacet;

/// Forward must-value analysis for arrays whose entire use closure has already
/// been certified by the loop summarizer. Only reads dominated by a uniform
/// whole-array write on every CFG path are replaced. Other writes/lifetimes
/// invalidate the fact; assertions never supply facts.
std::size_t prune_uniform_array_reads(
  goto_programt &,
  const namespacet &,
  const std::set<irep_idt> &certified_arrays);

#endif
