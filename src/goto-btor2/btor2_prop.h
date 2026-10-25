// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_BTOR2_PROP_H
#define CPROVER_GOTO_BTOR2_BTOR2_PROP_H

#include "btor2_builder.h"

#include <solvers/prop/prop.h>
#include <util/invariant.h>

#include <map>
#include <vector>

/// CBMC Boolean circuits mapped to BTOR2 expressions. Unconstrained literals
/// (e.g. CBMC's fallback for an invalid floating rounding mode) are lazy inputs.
/// Relational encodings with clauses are rejected, never added as constraints.
class btor2_propt final : public propt
{
public:
  btor2_propt(btor2_buildert &builder, message_handlert &handler)
    : propt(handler), builder(builder), bool_sort(builder.get_bool_sort())
  {
  }

  bvt unpack(btor2_nid_t value, std::size_t width)
  {
    PRECONDITION(value != 0 && width != 0);
    bvt result;
    result.reserve(width);
    for(std::size_t i = 0; i < width; ++i)
      result.push_back(bind(builder.slice(bool_sort, value, i, i)));
    return result; // CBMC bvt stores the least significant bit first.
  }

  btor2_nid_t pack(const bvt &bits)
  {
    // A relational SAT request invalidates this circuit. Propagate the zero
    // failure sentinel through the expression converter; its conversion-error
    // flag causes goto_to_btor2_convertert to abort before writing a model.
    if(failed)
      return 0;
    PRECONDITION(!bits.empty());
    auto result = node(bits.back());
    for(std::size_t i = bits.size() - 1; i > 0; --i)
      result = builder.concat(
        builder.get_or_create_bitvec_sort(bits.size() - i + 1),
        result,
        node(bits[i - 1]));
    return result;
  }

  literalt land(literalt a, literalt b) override
  {
    if(a.is_false() || b.is_false() || a == !b)
      return const_literal(false);
    if(a.is_true() || a == b)
      return b;
    if(b.is_true())
      return a;
    return bind(builder.land(bool_sort, node(a), node(b)));
  }

  literalt lor(literalt a, literalt b) override
  {
    return !land(!a, !b);
  }

  literalt lxor(literalt a, literalt b) override
  {
    if(a.is_false())
      return b;
    if(b.is_false())
      return a;
    if(a.is_true())
      return !b;
    if(b.is_true())
      return !a;
    if(a == b || a == !b)
      return const_literal(a != b);
    return bind(builder.lxor(bool_sort, node(a), node(b)));
  }

  literalt land(const bvt &bits) override
  {
    auto result = const_literal(true);
    for(const auto bit : bits)
      result = land(result, bit);
    return result;
  }

  literalt lor(const bvt &bits) override
  {
    auto result = const_literal(false);
    for(const auto bit : bits)
      result = lor(result, bit);
    return result;
  }

  literalt lxor(const bvt &bits) override
  {
    auto result = const_literal(false);
    for(const auto bit : bits)
      result = lxor(result, bit);
    return result;
  }

  literalt lnand(literalt a, literalt b) override { return !land(a, b); }
  literalt lnor(literalt a, literalt b) override { return !lor(a, b); }
  literalt lequal(literalt a, literalt b) override { return !lxor(a, b); }
  literalt limplies(literalt a, literalt b) override { return lor(!a, b); }

  literalt lselect(literalt condition, literalt yes, literalt no) override
  {
    if(condition.is_true() || yes == no)
      return yes;
    if(condition.is_false())
      return no;
    if(yes.is_true())
      return lor(condition, no);
    if(yes.is_false())
      return land(!condition, no);
    if(no.is_true())
      return lor(!condition, yes);
    if(no.is_false())
      return land(condition, yes);
    return bind(builder.ite(bool_sort, node(condition), node(yes), node(no)));
  }

  bool has_set_to() const override { return false; }
  bool cnf_handled_well() const override { return false; }

  void set_equal(literalt, literalt) override { unsupported(); }
  void l_set_to(literalt, bool) override { unsupported(); }
  void lcnf(const bvt &) override { unsupported(); }
  literalt new_variable() override
  {
    return bind(0); // Materialize only if a functional expression uses it.
  }

  std::size_t no_variables() const override { return nodes.size(); }
  std::string solver_text() const override { return "BTOR2 circuit builder"; }
  tvt l_get(literalt bit) const override
  {
    return bit.is_constant() ? tvt(bit.is_true()) : tvt::unknown();
  }
  void set_assignment(literalt, bool) override { unsupported(); }
  bool is_in_conflict(literalt) const override { return false; }

protected:
  resultt do_prop_solve(const bvt &) override
  {
    unsupported();
    return resultt::P_ERROR;
  }

private:
  btor2_buildert &builder;
  const btor2_nid_t bool_sort;
  std::vector<btor2_nid_t> nodes;
  std::map<literalt::var_not, btor2_nid_t> negated;
  bool failed = false;

  literalt bind(btor2_nid_t value)
  {
    PRECONDITION(nodes.size() < literalt::unused_var_no());
    const literalt result(static_cast<literalt::var_not>(nodes.size()), false);
    nodes.push_back(value);
    return result;
  }

  btor2_nid_t node(literalt bit)
  {
    if(bit.is_constant())
      return bit.is_true() ? builder.one(bool_sort) : builder.zero(bool_sort);
    auto &value = nodes.at(bit.var_no());
    if(!value)
      value = builder.input(bool_sort, "__cbmc_float_unspecified");
    if(!bit.sign())
      return value;
    auto &inverse = negated[bit.var_no()];
    if(!inverse)
      inverse = builder.lnot(bool_sort, value);
    return inverse;
  }

  void unsupported()
  {
    if(!failed)
      log.error() << "CBMC circuit requested a nonfunctional SAT operation; "
                     "no BTOR2 expression emitted"
                  << messaget::eom;
    failed = true;
  }
};

#endif
