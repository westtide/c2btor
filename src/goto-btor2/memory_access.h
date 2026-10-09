#ifndef CPROVER_GOTO_BTOR2_MEMORY_ACCESS_H
#define CPROVER_GOTO_BTOR2_MEMORY_ACCESS_H

#include <util/message.h>

#include <goto-programs/goto_program.h>

#include "heap_model.h"

#include <optional>
#include <set>

class expr_to_btor2t;
class side_effect_exprt;

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
    array_encoding_optionst = {});
  heap_modelt heap;
  bool failed = false;
  std::set<irep_idt> logical_records;
  void collect(const goto_programt &);
  void create_states();
  void initialize_static();
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
  std::map<irep_idt, exprt> const_bindings;
  void collect_const_bindings(const goto_programt &);
  exprt fold_size_expr(const exprt &) const;
  void collect_expr(const exprt &, bool address_taken = false);
  btor2_nid_t size_value(const typet &);
  btor2_nid_t pointer_integer(const exprt &);
  btor2_nid_t add_bytes(btor2_nid_t, const exprt &);
  bool assign_at(
    btor2_nid_t, const typet &, const exprt &, bool zero_initialized = false);
};
#endif
