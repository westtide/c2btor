// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_ARRAY_LOOP_SUMMARY_H
#define CPROVER_GOTO_BTOR2_ARRAY_LOOP_SUMMARY_H

#include <util/irep.h>
#include <util/mp_arith.h>
#include <util/source_location.h>
#include <util/type.h>

#include <cstddef>
#include <set>
#include <string>
#include <vector>

class goto_programt;
class namespacet;

struct array_nondet_callt
{
  irep_idt array;
  mp_integer index_coefficient, index_constant;
  source_locationt source;
  irep_idt function;
  typet type;
  std::size_t order = 0;
};

struct array_nondet_summaryt
{
  std::string id;
  mp_integer initial, iterations;
  std::vector<array_nondet_callt> calls;
  source_locationt loop_source;
};

struct array_loop_summary_reportt
{
  std::size_t candidates = 0, summarized = 0;
  std::size_t fills = 0, copies = 0;
  std::size_t nondet_initializations = 0;
  std::set<irep_idt> certified_arrays;
  std::vector<std::string> diagnostics;
  std::vector<array_nondet_summaryt> nondet_summaries;
};

/// Replace only certified finite constant-fill, independent nondet-fill, or
/// same-index copy loops.
/// Certification includes declaration-time extent snapshots, no machine
/// arithmetic wrap, complete affine tiles, closed aliases, and in-bounds
/// accesses throughout the entire program. ASSERTs are never removed.
/// A rejected candidate leaves the original program unchanged.
/// Copies require equal array types/extents and closed, independent roots
/// (or an exact self-copy). The RHS is the source storage at loop entry;
/// subsequent source writes must not change the copied destination.
/// Independent nondet initialization uses one fresh whole-array input per
/// root; each source sample must have a closed DECL/assign/store/DEAD lifetime.
array_loop_summary_reportt
summarize_array_loops(goto_programt &, const namespacet &);

#endif
