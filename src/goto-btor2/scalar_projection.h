// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_SCALAR_PROJECTION_H
#define CPROVER_GOTO_BTOR2_SCALAR_PROJECTION_H

#include <util/irep.h>

#include <cstddef>
#include <functional>
#include <set>

class goto_programt;
class namespacet;

enum class scalar_projection_modet { NONE, DEAD, LIVENESS };

struct scalar_projection_reportt
{
  std::size_t before = 0, after = 0;
  std::size_t assignments = 0, declarations = 0, lifetimes = 0;
  // Keep implicit initializer evaluation even if its last value use is dead.
  std::set<irep_idt> forced_static_symbols;
};

// Project only scalar values that cannot affect any retained operation. Memory
// objects and their capacity/lifetime plan must already have been collected.
scalar_projection_reportt project_dead_scalars(
  goto_programt &,
  const namespacet &,
  const std::function<bool(const irep_idt &)> &is_memory_symbol,
  scalar_projection_modet mode = scalar_projection_modet::DEAD);

#endif
