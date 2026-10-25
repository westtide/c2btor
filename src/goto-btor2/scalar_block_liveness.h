// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_SCALAR_BLOCK_LIVENESS_H
#define CPROVER_GOTO_BTOR2_SCALAR_BLOCK_LIVENESS_H

#include <goto-programs/goto_program.h>

#include <map>
#include <set>
#include <vector>

class namespacet;

struct scalar_block_liveness_reportt
{
  /// These sets partition the supplied, already filtered scalar candidates.
  std::set<irep_idt> persistent_symbols;
  std::set<irep_idt> local_symbols;
  /// All symbol reads at each runtime block entry, including noncandidates.
  std::map<unsigned, std::set<irep_idt>> entry_live;
};

/// Classify values that must cross a runtime block boundary. The caller
/// supplies the converter's complete successor relation, including terminal
/// self-loops; this analysis neither unfolds loops nor infers frontend
/// control-flow rules. Candidate filtering must retain
/// static/volatile/addressable storage and implicit initializer dependencies
/// before calling this helper.
scalar_block_liveness_reportt classify_scalar_block_state(
  const goto_programt &,
  const namespacet &,
  const std::vector<std::vector<unsigned>> &blocks,
  const std::set<irep_idt> &candidate_ids,
  const std::map<unsigned, std::vector<unsigned>> &successors);

#endif
