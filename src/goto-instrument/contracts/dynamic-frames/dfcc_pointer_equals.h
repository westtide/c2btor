/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: Jan 2025

\*******************************************************************/

/// \file
/// Instruments occurrences of pointer_equals predicates in programs
/// encoding requires and ensures clauses of contracts.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_POINTER_EQUALS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_POINTER_EQUALS_H

#include <util/message.h>

#include <goto-programs/goto_program.h>

class goto_modelt;
class message_handlert;
class dfcc_libraryt;
class dfcc_cfg_infot;
class exprt;

/// Rewrites `equal_exprt` over pointers into calls
/// to the front-end function `__CPROVER_pointer_equals`,
/// at the expression level. Meant to be Applied before GOTO conversion
/// of function contract clauses, followed by `rewrite_calls`.
void rewrite_equal_exprt_to_pointer_equals(exprt &expr);

/// Rewrites calls to pointer_equals predicates into calls
/// to the library implementation.
class dfcc_pointer_equalst
{
public:
  /// \param library The contracts instrumentation library
  /// \param message_handler Used for messages
  dfcc_pointer_equalst(
    dfcc_libraryt &library,
    message_handlert &message_handler);

  /// Rewrites calls to pointer_equals predicates into calls
  /// to the library implementation in the given program, passing the
  /// given write_set expression as parameter to the library function.
  void rewrite_calls(goto_programt &program, dfcc_cfg_infot cfg_info);

  /// Rewrites calls to pointer_equals predicates into calls
  /// to the library implementation in the given program between
  /// first_instruction (included) and last_instruction (excluded), passing the
  /// given write_set expression as parameter to the library function.
  void rewrite_calls(
    goto_programt &program,
    goto_programt::targett first_instruction,
    const goto_programt::targett &last_instruction,
    dfcc_cfg_infot cfg_info);

protected:
  dfcc_libraryt &library;
  message_handlert &message_handler;
  messaget log;
};

#endif
