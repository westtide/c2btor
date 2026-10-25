// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "array_uniform_pruning.h"

#include <goto-programs/goto_program.h>
#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <deque>
#include <map>
#include <unordered_map>

namespace
{
using factst = std::map<irep_idt, exprt>;

irep_idt array_root(const exprt &expr)
{
  const exprt *root = &expr;
  while(root->id() == ID_index)
    root = &to_index_expr(*root).array();
  return root->id() == ID_symbol
           ? to_symbol_expr(*root).get_identifier()
           : irep_idt{};
}

bool scalar_literal(const exprt &expr)
{
  return expr.id() == ID_constant &&
         (expr.type().id() == ID_signedbv ||
          expr.type().id() == ID_unsignedbv ||
          expr.type().id() == ID_bool || expr.type().id() == ID_c_bool);
}

exprt converted_literal(
  const exprt &value, const typet &type, const namespacet &ns)
{
  if(value.type() == type)
    return value;
  return simplify_expr(typecast_exprt(value, type), ns);
}

void transfer(
  const goto_programt::instructiont &instruction,
  factst &facts,
  const std::set<irep_idt> &certified,
  const namespacet &ns)
{
  if(instruction.is_decl())
    facts.erase(instruction.decl_symbol().get_identifier());
  else if(instruction.is_dead())
    facts.erase(array_root(to_code_dead(instruction.code()).symbol()));
  else if(instruction.is_assign())
  {
    const auto &lhs = instruction.assign_lhs();
    const auto id = array_root(lhs);
    if(!certified.count(id))
      return;
    const auto rhs = simplify_expr(instruction.assign_rhs(), ns);
    if(lhs.id() == ID_symbol && rhs.id() == ID_array_of &&
       rhs.operands().size() == 1 && scalar_literal(rhs.operands()[0]))
      facts[id] = rhs.operands()[0];
    else if(
      lhs.id() == ID_symbol && rhs.id() == ID_symbol &&
      instruction.code().get_bool("c2btor_certified_array_copy") &&
      certified.count(to_symbol_expr(rhs).get_identifier()))
    {
      const auto source = facts.find(to_symbol_expr(rhs).get_identifier());
      if(source != facts.end())
        facts[id] = source->second;
      else
        facts.erase(id);
    }
    else if(lhs.id() == ID_index && facts.count(id) &&
            scalar_literal(rhs) &&
            converted_literal(facts.at(id), lhs.type(), ns) == rhs)
    {
      // Writing the known uniform value to a certified legal element keeps it.
    }
    else
      facts.erase(id);
  }
  else if(instruction.is_function_call() || instruction.is_other())
    facts.clear();
}

factst meet(const factst &left, const factst &right)
{
  factst result;
  for(const auto &entry : left)
  {
    const auto other = right.find(entry.first);
    if(other != right.end() && entry.second == other->second)
      result.insert(entry);
  }
  return result;
}

void rewrite(
  exprt &expr, const factst &facts, const namespacet &ns, std::size_t &count)
{
  if(expr.id() == ID_index &&
     to_index_expr(expr).array().id() == ID_symbol)
  {
    const auto fact = facts.find(array_root(expr));
    if(fact != facts.end())
    {
      const auto value = converted_literal(fact->second, expr.type(), ns);
      if(scalar_literal(value))
      {
        expr = value;
        ++count;
        return;
      }
    }
  }
  for(auto &operand : expr.operands())
    rewrite(operand, facts, ns, count);
}
} // namespace

std::size_t prune_uniform_array_reads(
  goto_programt &program,
  const namespacet &ns,
  const std::set<irep_idt> &certified_arrays)
{
  if(program.instructions.empty() || certified_arrays.empty())
    return 0;
  using targett = goto_programt::targett;
  std::unordered_map<const goto_programt::instructiont *, factst> before;
  std::deque<targett> pending;
  const auto entry = program.instructions.begin();
  before.emplace(&*entry, factst{});
  pending.push_back(entry);
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    auto after = before.at(&*current);
    transfer(*current, after, certified_arrays, ns);
    // Unseen predecessors are lattice top, not an invented uniform value.
    // Any later conflicting reachable predecessor removes the fact again.
    for(const auto successor : program.get_successors(current))
    {
      const auto old = before.find(&*successor);
      if(old == before.end())
      {
        before.emplace(&*successor, after);
        pending.push_back(successor);
      }
      else
      {
        auto joined = meet(old->second, after);
        if(joined != old->second)
        {
          old->second = std::move(joined);
          pending.push_back(successor);
        }
      }
    }
  }
  std::size_t count = 0;
  for(auto &instruction : program.instructions)
  {
    const auto found = before.find(&instruction);
    if(found == before.end())
      continue;
    if(instruction.is_assign())
      rewrite(instruction.assign_rhs_nonconst(), found->second, ns, count);
    if(instruction.has_condition())
      rewrite(instruction.condition_nonconst(), found->second, ns, count);
  }
  return count;
}
