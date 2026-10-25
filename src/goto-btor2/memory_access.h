// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_MEMORY_ACCESS_H
#define CPROVER_GOTO_BTOR2_MEMORY_ACCESS_H

#include <util/message.h>

#include <goto-programs/goto_program.h>

#include "heap_model.h"
#include "logical_arrays.h"

#include <optional>
#include <set>

class expr_to_btor2t;
class side_effect_exprt;
class symbolt;

/// Whether values supplied by the program may name C objects without an
/// explicit address-of expression. This controls the storage universe only;
/// it does not restrict the runtime pointer values admitted by the model.
bool has_arbitrary_pointer_input(const goto_programt &, const namespacet &);
/// Source-object eligibility shared by storage closure and capacity analysis.
bool is_c_source_object(const symbolt &, const namespacet &);

/// Normalizes C lvalues into a root identity and a byte offset. No points-to
/// guess may replace the runtime pointer value used by a dereference.
class memory_accesst
{
public:
  memory_accesst(
    btor2_buildert &,
    expr_to_btor2t &,
    const namespacet &,
    messaget &,
    unsigned budget,
    array_encoding_optionst = {},
    bool enable_logical_arrays = false);
  heap_modelt heap;
  logical_arrayst logical_arrays;
  bool failed = false;
  std::set<irep_idt> logical_records;
  void collect(const goto_programt &);
  void create_states();
  void initialize_static();
  void begin(unsigned pc, btor2_nid_t guard);
  void end();
  void finish();
  json_objectt metadata() const;
  bool owns_symbol(const irep_idt &) const;
  bool owns_lvalue(const exprt &) const;
  std::optional<btor2_nid_t> convert(const exprt &);
  bool assign(const exprt &lhs, const exprt &rhs);
  void declaration(const symbol_exprt &, bool dead);
  btor2_nid_t address(const exprt &);
  btor2_nid_t allocation(const side_effect_exprt &);
  void error(const std::string &);

private:
  btor2_buildert &b;
  expr_to_btor2t &expressions;
  const namespacet &ns;
  messaget &log;
  std::set<irep_idt> initializer_symbols;
  std::map<exprt, irep_idt> strings;
  bool promote_unaddressed_objects = false;
  bool logical_failure_reported = false;
  void check_logical_arrays();
  void validate_wide_pointer_representation(const goto_programt &);
  bool check_wide_pointer_expression(const exprt &);
  void collect_expr(const exprt &, bool address_taken = false);
  btor2_nid_t size_value(const typet &);
  btor2_nid_t pointer_integer(const exprt &);
  btor2_nid_t add_bytes(btor2_nid_t, const exprt &);
  struct initial_lvaluet
  {
    unsigned tag;
    mp_integer offset;
  };
  bool assign_at(
    btor2_nid_t,
    const typet &,
    const exprt &,
    bool zero_initialized = false,
    std::optional<initial_lvaluet> initial_location = {});
};
#endif
