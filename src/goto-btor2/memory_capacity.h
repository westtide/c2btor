#ifndef CPROVER_GOTO_BTOR2_MEMORY_CAPACITY_H
#define CPROVER_GOTO_BTOR2_MEMORY_CAPACITY_H

#include <util/expr.h>
#include <util/mp_arith.h>
#include <util/namespace.h>

#include <goto-programs/goto_program.h>

#include <map>

/// Upper bounds at object declarations/allocation sites in the final GotoIR.
/// Analysis does not instrument the program or restrict its input values.
struct memory_capacity_boundst
{
  std::map<irep_idt, mp_integer> objects;
  mp_integer allocation = 0;
};

memory_capacity_boundst infer_memory_capacity(
  const goto_programt &program,
  const namespacet &ns,
  const std::map<irep_idt, exprt> &object_sizes);

#endif
