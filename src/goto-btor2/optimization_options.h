// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_OPTIMIZATION_OPTIONS_H
#define CPROVER_GOTO_BTOR2_OPTIMIZATION_OPTIONS_H

// Independent opt-in stages; storage and source-property options remain
// unchanged. Keeping this separate makes each stage comparable in isolation.
struct btor2_optimization_optionst
{
  bool state_projection = false;
  bool logical_arrays = false;
  bool scalar_blocks = false;
  bool array_blocks = false;
  bool array_loop_summary = false;
  bool scalar_loop_summary = false;
};

#endif
