/*******************************************************************\

Module: Demo BTOR2 Export (simple while-loop subset)

Author: 

\*******************************************************************/

#ifndef CPROVER_CBMC_BTOR2_DEMO_H
#define CPROVER_CBMC_BTOR2_DEMO_H

#include <goto-programs/goto_model.h>
#include <util/message.h>

#include <iosfwd>

/// Export a simple while-loop in main() to a BTOR2 transition system.
/// This is a demo-only exporter that matches a narrow instruction pattern.
bool write_btor2_demo(
  const goto_modelt &goto_model,
  std::ostream &out,
  messaget &log);

#endif // CPROVER_CBMC_BTOR2_DEMO_H
