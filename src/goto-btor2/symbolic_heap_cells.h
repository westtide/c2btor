// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_SYMBOLIC_HEAP_CELLS_H
#define CPROVER_GOTO_BTOR2_SYMBOLIC_HEAP_CELLS_H

#include <cstddef>
#include <string>

class goto_programt;
class namespacet;

struct symbolic_heap_cell_certificatet
{
  bool word64 = false;
  std::size_t accesses = 0;
  std::string reason;
};

/// Sufficient, conservative certificate for aligned 64-bit heap cells.
/// The final CFG is analyzed without modifying its operations or properties.
/// Failure selects byte storage; it never rejects conversion or restricts C.
symbolic_heap_cell_certificatet
certify_symbolic_heap_cells(const goto_programt &, const namespacet &);

#endif
