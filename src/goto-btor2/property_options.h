// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_PROPERTY_OPTIONS_H
#define CPROVER_GOTO_BTOR2_PROPERTY_OPTIONS_H

#include <util/source_location.h>
#include "source_event_provenance.h"

#include <vector>

struct btor2_property_optionst
{
  bool merge = true;
  // Preserve original property IDs for assertions removed by CFG reachability
  // after constant folding. Their violation predicates are false, and their
  // IDs remain reserved when later lowering introduces new assertions.
  std::vector<source_locationt> unreachable_assertions;
  btor2_source_provenancet source_provenance;
};

#endif
