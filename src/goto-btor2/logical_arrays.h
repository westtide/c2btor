// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_LOGICAL_ARRAYS_H
#define CPROVER_GOTO_BTOR2_LOGICAL_ARRAYS_H

#include <util/json.h>

#include <goto-programs/goto_program.h>

#include "array_encoding.h"
#include "btor2_builder.h"
#include "btor2_type_utils.h"

#include <map>
#include <optional>
#include <set>
#include <string>

class expr_to_btor2t;
class symbol_exprt;

/// Independent element storage for arrays whose complete use closure has no
/// address, byte, pointer, or partial-array view. Whole-storage copies require
/// the loop summarizer's equal-extent, closed-use certificate. Classification
/// precedes byte-memory planning. Declined roots remain in ordinary memory.
class logical_arrayst
{
public:
  logical_arrayst(
    btor2_buildert &,
    expr_to_btor2t &,
    const namespacet &,
    array_encoding_optionst = {},
    bool enabled = false);

  bool failed = false;
  std::string failure_reason;
  void collect(const goto_programt &);
  const std::set<irep_idt> &symbols() const
  {
    return roots;
  }
  bool owns_symbol(const irep_idt &id) const
  {
    return roots.count(id) != 0;
  }
  bool owns_lvalue(const exprt &) const;
  void create_states();
  void initialize_static();
  std::optional<btor2_nid_t> convert(const exprt &);
  /// True also on failure when the lhs belongs to this backend.
  bool assign(const exprt &lhs, const exprt &rhs);
  /// Record the once-converted element value at source width. Whole-array
  /// assignments produce no scalar observation.
  bool assign(const exprt &lhs, const exprt &rhs, btor2_nid_t &assigned_leaf);
  btor2_nid_t last_nondet_input() const
  {
    return nondet_input;
  }
  /// Select the original instruction site without resetting a block's values.
  void set_location(unsigned pc)
  {
    current_pc = pc;
  }
  void declaration(const symbol_exprt &, bool dead);
  void begin(unsigned pc, btor2_nid_t guard);
  void end();
  void finish();
  json_arrayt metadata() const;
  void record_reserved_tag(const irep_idt &, unsigned);

  /// Latest-value environments include both storage and latched dimensions.
  /// bind changes local values; commit merges an exit under its path guard.
  using valuest = std::map<btor2_nid_t, btor2_nid_t>;
  valuest values() const;
  void bind(const valuest &);
  void commit(btor2_nid_t guard, const valuest &);
  const valuest &state_sorts() const
  {
    return sorts;
  }

private:
  struct dimensiont
  {
    exprt size;
    std::size_t width = 0;
    btor2_nid_t state = 0;
    btor2_nid_t constant = 0;
  };
  struct arrayt
  {
    irep_idt id;
    typet type;
    typet leaf;
    exprt initializer;
    bool static_lifetime = false;
    bool boolean = false;
    bool unused = false;
    bool native = true;
    std::size_t element_width = 0;
    std::size_t source_width = 0;
    std::size_t index_width = 0;
    std::size_t packed_width = 0;
    std::optional<mp_integer> upper_elements;
    std::vector<dimensiont> dimensions;
    btor2_nid_t element_sort = 0;
    btor2_nid_t index_sort = 0;
    btor2_nid_t storage_sort = 0;
    btor2_nid_t state = 0;
    unsigned tag = 0;
  };
  struct updatet
  {
    btor2_nid_t sort;
    btor2_nid_t local;
    btor2_nid_t next;
  };
  struct accesst
  {
    irep_idt id;
    std::vector<exprt> indices;
  };
  btor2_buildert &b;
  expr_to_btor2t &expressions;
  const namespacet &ns;
  array_encoding_optionst encoding;
  bool enabled;
  std::set<irep_idt> roots;
  std::map<irep_idt, arrayt> arrays;
  std::map<btor2_nid_t, updatet> updates;
  valuest sorts;
  unsigned current_pc = 0;
  btor2_nid_t current_guard = 0;
  btor2_nid_t nondet_input = 0;

  void error(const std::string &);
  bool
  assign_impl(const exprt &lhs, const exprt &rhs, btor2_nid_t *assigned_leaf);
  static std::optional<accesst> access(const exprt &);
  btor2_nid_t add_state(
    btor2_nid_t sort,
    const std::string &name,
    const std::string &source = "");
  btor2_nid_t local(btor2_nid_t) const;
  void set_local(btor2_nid_t, btor2_nid_t);
  btor2_nid_t
  resize(btor2_nid_t, std::size_t from, std::size_t to, bool sign = false);
  std::pair<btor2_nid_t, btor2_nid_t>
  index(const arrayt &, const std::vector<exprt> &);
  btor2_nid_t element(const arrayt &, const exprt &);
  btor2_nid_t read(const arrayt &, btor2_nid_t storage, btor2_nid_t index);
  btor2_nid_t write(
    const arrayt &,
    btor2_nid_t storage,
    btor2_nid_t index,
    btor2_nid_t value);
  btor2_nid_t fill(const arrayt &, const exprt &);
  btor2_nid_t initializer(
    const arrayt &,
    const exprt &,
    btor2_nid_t storage,
    mp_integer &offset);
};

#endif
