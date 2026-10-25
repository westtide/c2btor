// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "scalar_projection.h"

#include "btor2_type_utils.h"

#include <goto-programs/goto_program.h>
#include <goto-programs/remove_skip.h>
#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <map>
#include <deque>
#include <set>
#include <vector>

namespace
{
using symbol_sett = std::set<irep_idt>;

void add_symbols(const exprt &expr, symbol_sett &dest)
{
  const auto ids = find_symbol_identifiers(expr);
  dest.insert(ids.begin(), ids.end());
}

// Include type-only expressions (notably VLA sizes) and resolve tag symbols.
// The visited set also makes recursive struct/pointer types terminate.
void add_type_dependencies(
  const typet &type, const namespacet &ns, symbol_sett &roots,
  symbol_sett &visited)
{
  find_symbols_sett ids;
  find_type_and_expr_symbols(type, ids);
  for(const auto &id : ids)
  {
    roots.insert(id);
    const symbolt *symbol = nullptr;
    if(visited.insert(id).second && !ns.lookup(id, symbol) && symbol)
      add_type_dependencies(symbol->type, ns, roots, visited);
  }
}

void add_expression_types(
  const exprt &expr, const namespacet &ns, symbol_sett &roots,
  symbol_sett &visited)
{
  add_type_dependencies(expr.type(), ns, roots, visited);
  for(const auto &key : {ID_C_c_sizeof_type, ID_C_va_arg_type})
    if(expr.find(key).is_not_nil())
      add_type_dependencies(
        static_cast<const typet &>(expr.find(key)), ns, roots, visited);
  for(const auto &operand : expr.operands())
    add_expression_types(operand, ns, roots, visited);
}

bool qualified(const typet &type)
{
  return type.get_bool(ID_C_volatile) || type.get_bool(ID_C_atomic);
}

bool integer(const typet &type)
{
  return type.id() == ID_bool || type.id() == ID_c_bool ||
         type.id() == ID_signedbv || type.id() == ID_unsignedbv;
}

bool can_cleanup(const goto_programt &program)
{
  for(const auto &ins : program.instructions)
  {
    // Upstream remove_skip accepts these OTHER forms as no-ops, whereas
    // this converter rejects them. Do not hide that existing rejection.
    if(ins.is_other() &&
       (ins.get_other().is_nil() || ins.get_other().get_statement() == ID_skip))
      return false;
    if(ins.is_goto() && ins.targets.size() != 1)
      return false;
  }
  return true;
}

class purityt
{
  const namespacet &ns;
  const std::function<bool(const irep_idt &)> &is_memory;

public:
  purityt(
    const namespacet &ns,
    const std::function<bool(const irep_idt &)> &is_memory)
    : ns(ns), is_memory(is_memory)
  {
  }

  bool scalar(const exprt &expr) const
  {
    if(expr.id() != ID_symbol || qualified(expr.type()))
      return false;
    const auto &id = to_symbol_expr(expr).get_identifier();
    const symbolt *symbol = nullptr;
    if(ns.lookup(id, symbol) || !symbol || symbol->is_type ||
       is_memory(id) || qualified(symbol->type))
      return false;
    const auto type = follow_tag_type(symbol->type, ns);
    return !qualified(type) && (integer(type) || type.id() == ID_pointer);
  }

  bool expression(const exprt &expr) const
  {
    const auto type = follow_tag_type(expr.type(), ns);
    if(qualified(expr.type()) || qualified(type))
      return false;
    if(expr.id() == ID_symbol)
      return scalar(expr);
    if(expr.id() == ID_constant)
      return integer(type) ||
        (type.id() == ID_pointer && expr.get(ID_value) == ID_NULL);
    // Arbitrary integer inputs have no effect if no retained use observes
    // them. Pointer nondeterminism is deliberately outside this whitelist.
    if(expr.id() == ID_side_effect)
      return expr.get(ID_statement) == ID_nondet && integer(type) &&
             expr.operands().empty();
    if(expr.id() == ID_if)
    {
      if(expr.operands().size() != 3 ||
         !integer(follow_tag_type(expr.operands()[0].type(), ns)) ||
         (!integer(type) && type.id() != ID_pointer))
        return false;
    }
    else
    {
      // Exclude division, shifts, pointer arithmetic/conversions, memory
      // queries and unknown operators even when their result is dead. They
      // may have a diagnostic or an unsupported-lowering obligation.
      static const std::set<irep_idt> operators{
        ID_typecast, ID_plus, ID_minus, ID_unary_minus, ID_mult,
        ID_bitand, ID_bitor, ID_bitxor, ID_bitnot, ID_equal, ID_notequal,
        ID_lt, ID_le, ID_gt, ID_ge, ID_and, ID_or, ID_xor, ID_not,
        ID_implies};
      if(!integer(type) || !operators.count(expr.id()))
        return false;
      static const std::set<irep_idt> unary{
        ID_typecast, ID_unary_minus, ID_bitnot, ID_not};
      static const std::set<irep_idt> binary{
        ID_minus, ID_equal, ID_notequal, ID_lt, ID_le, ID_gt, ID_ge, ID_implies};
      const auto arity = expr.operands().size();
      if(unary.count(expr.id()) ? arity != 1
         : binary.count(expr.id()) ? arity != 2 : arity < 2)
        return false;
      for(const auto &operand : expr.operands())
        if(!integer(follow_tag_type(operand.type(), ns)))
          return false;
    }
    for(const auto &operand : expr.operands())
      if(!expression(operand))
        return false;
    return true;
  }
};

void project_dead_initial_values(
  goto_programt &program, const namespacet &ns, const purityt &pure,
  scalar_projection_reportt &report)
{
  struct livet
  {
    symbol_sett uses, defs, in, out;
    std::vector<std::size_t> successors, predecessors;
  };
  std::vector<goto_programt::targett> instructions;
  std::map<const goto_programt::instructiont *, std::size_t> index;
  for(auto it = program.instructions.begin(); it != program.instructions.end(); ++it)
  {
    index[&*it] = instructions.size();
    instructions.push_back(it);
  }
  std::vector<livet> live(instructions.size());
  for(std::size_t i = 0; i < instructions.size(); ++i)
  {
    const auto &ins = *instructions[i];
    auto &node = live[i];
    symbol_sett type_visited;
    add_expression_types(ins.code(), ns, node.uses, type_visited);
    if(ins.is_assign() && pure.scalar(ins.assign_lhs()))
    {
      add_symbols(ins.assign_rhs(), node.uses);
      node.defs.insert(to_symbol_expr(ins.assign_lhs()).get_identifier());
    }
    else if(ins.is_decl() && pure.scalar(ins.decl_symbol()))
      node.defs.insert(ins.decl_symbol().get_identifier());
    else if(ins.is_dead() && pure.scalar(ins.dead_symbol()))
      ; // DEAD does not kill a scalar value in this transition model.
    else
      // Includes custom OTHER copy/free/check arguments and unknown effects.
      add_symbols(ins.code(), node.uses);
    if(ins.has_condition())
    {
      add_symbols(ins.condition(), node.uses);
      add_expression_types(ins.condition(), ns, node.uses, type_visited);
    }
    for(const auto successor : program.get_successors(instructions[i]))
      if(successor != program.instructions.end())
      {
        const auto j = index.at(&*successor);
        node.successors.push_back(j);
        live[j].predecessors.push_back(i);
      }
  }

  // A monotone backwards fixed point includes every loop backedge. A DECL's
  // arbitrary value is removable only if absent from live-out on every path.
  std::deque<std::size_t> pending;
  std::vector<bool> queued(live.size(), true);
  for(std::size_t i = live.size(); i > 0; --i)
    pending.push_back(i - 1);
  while(!pending.empty())
  {
    const auto i = pending.front();
    pending.pop_front();
    queued[i] = false;
    auto &node = live[i];
    node.out.clear();
    for(const auto successor : node.successors)
      node.out.insert(live[successor].in.begin(), live[successor].in.end());
    auto incoming = node.out;
    for(const auto &def : node.defs)
      incoming.erase(def);
    incoming.insert(node.uses.begin(), node.uses.end());
    if(incoming != node.in)
    {
      node.in = std::move(incoming);
      for(const auto predecessor : node.predecessors)
        if(!queued[predecessor])
        {
          queued[predecessor] = true;
          pending.push_back(predecessor);
        }
    }
  }
  bool changed = false;
  for(std::size_t i = 0; i < instructions.size(); ++i)
  {
    auto &ins = *instructions[i];
    if(ins.is_decl() && pure.scalar(ins.decl_symbol()) &&
       !live[i].out.count(ins.decl_symbol().get_identifier()))
    {
      ins.turn_into_skip();
      ++report.declarations;
      changed = true;
    }
    else if(ins.is_dead() && pure.scalar(ins.dead_symbol()))
    {
      ins.turn_into_skip();
      ++report.lifetimes;
      changed = true;
    }
  }
  if(changed)
  {
    remove_skip(program);
    program.update();
  }
}
} // namespace

scalar_projection_reportt project_dead_scalars(
  goto_programt &program,
  const namespacet &ns,
  const std::function<bool(const irep_idt &)> &is_memory_symbol,
  scalar_projection_modet mode)
{
  scalar_projection_reportt report;
  report.before = program.instructions.size();
  report.after = report.before;
  if(mode == scalar_projection_modet::NONE || !can_cleanup(program))
    return report;
  purityt pure(ns, is_memory_symbol);
  symbol_sett roots, all_symbols, type_visited;
  std::map<irep_idt, symbol_sett> dependencies;
  std::set<const goto_programt::instructiont *> candidates;
  for(const auto &ins : program.instructions)
  {
    add_symbols(ins.code(), all_symbols);
    if(ins.source_location().get_bool("c2btor_witness_value_root"))
      add_symbols(ins.code(), roots);
    add_expression_types(ins.code(), ns, roots, type_visited);
    if(ins.has_condition())
    {
      add_symbols(ins.condition(), all_symbols);
      add_expression_types(ins.condition(), ns, roots, type_visited);
      add_symbols(ins.condition(), roots);
    }
    if(ins.is_assign() && pure.scalar(ins.assign_lhs()) &&
       pure.expression(ins.assign_rhs()))
    {
      candidates.insert(&ins);
      add_symbols(ins.assign_rhs(),
        dependencies[to_symbol_expr(ins.assign_lhs()).get_identifier()]);
    }
    else if(ins.is_decl() && pure.scalar(ins.decl_symbol()))
      ; // Declaration identity is not a read of its arbitrary initial value.
    else if(ins.is_dead() && pure.scalar(ins.dead_symbol()))
      ; // A non-addressable scalar DEAD has no lifetime side effect.
    else
      add_symbols(ins.code(), roots);
  }

  // Symbol-table initializers and types are implicit reads that need not be
  // repeated as code operands. Preserve nonconstant initializers themselves,
  // including any unsupported construct they may still contain.
  symbol_sett examined;
  all_symbols.insert(roots.begin(), roots.end());
  while(true)
  {
    symbol_sett next;
    for(const auto &id : all_symbols)
    {
      const symbolt *symbol = nullptr;
      if(!examined.insert(id).second || ns.lookup(id, symbol) || !symbol)
        continue;
      add_type_dependencies(symbol->type, ns, roots, type_visited);
      if(symbol->is_static_lifetime && symbol->value.is_not_nil())
      {
        add_symbols(symbol->value, roots);
        add_symbols(symbol->value, next);
        add_expression_types(symbol->value, ns, roots, type_visited);
        if(!symbol->value.is_constant() || !pure.expression(symbol->value))
        {
          roots.insert(id);
          report.forced_static_symbols.insert(id);
        }
      }
    }
    const auto before = all_symbols.size();
    next.insert(roots.begin(), roots.end());
    all_symbols.insert(next.begin(), next.end());
    if(before == all_symbols.size())
      break;
  }

  for(bool changed = true; changed;)
  {
    changed = false;
    for(const auto &[id, used] : dependencies)
      if(roots.count(id))
        for(const auto &source : used)
          changed |= roots.insert(source).second;
  }
  for(auto &ins : program.instructions)
  {
    if(candidates.count(&ins) &&
       !roots.count(to_symbol_expr(ins.assign_lhs()).get_identifier()))
    {
      ins.turn_into_skip();
      ++report.assignments;
    }
    else if(ins.is_decl() && pure.scalar(ins.decl_symbol()) &&
            !roots.count(ins.decl_symbol().get_identifier()))
    {
      ins.turn_into_skip();
      ++report.declarations;
    }
    else if(ins.is_dead() && pure.scalar(ins.dead_symbol()) &&
            !roots.count(ins.dead_symbol().get_identifier()))
    {
      ins.turn_into_skip();
      ++report.lifetimes;
    }
  }
  if(report.assignments || report.declarations || report.lifetimes)
  {
    remove_skip(program);
    program.update();
  }
  if(mode == scalar_projection_modet::LIVENESS)
    project_dead_initial_values(program, ns, pure, report);
  report.after = program.instructions.size();
  return report;
}
