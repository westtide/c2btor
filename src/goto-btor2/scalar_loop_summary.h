// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_SCALAR_LOOP_SUMMARY_H
#define CPROVER_GOTO_BTOR2_SCALAR_LOOP_SUMMARY_H

#include <cstddef>
#include <string>
#include <vector>

class goto_programt;
class namespacet;

struct scalar_loop_summary_reportt
{
  std::size_t candidates = 0, summarized = 0, empty_loops = 0;
  std::vector<std::string> diagnostics;
};

/// Summarize canonical finite integer loops whose body is empty or whose
/// sole body effect is `acc = acc +/- literal`. Counter arithmetic must not
/// wrap. Signed accumulators require a known entry value and a no-overflow
/// certificate; unsigned accumulators retain their defined modular arithmetic. Source
/// assertions, aliases, volatile/atomic storage, calls and all other body
/// effects are rejected, leaving the original loop unchanged. Exit counter
/// values are preserved. This pass does not summarize unknown array folds.
scalar_loop_summary_reportt
summarize_scalar_loops(goto_programt &, const namespacet &);

#endif
