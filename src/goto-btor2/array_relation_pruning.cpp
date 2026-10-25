// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "array_relation_pruning.h"

#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <goto-programs/goto_program.h>

#include <algorithm>
#include <deque>
#include <iterator>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

namespace
{
using relationt = std::pair<irep_idt, irep_idt>;
using factst = std::set<relationt>;
using beforet = std::unordered_map<const goto_programt::instructiont *, factst>;

relationt ordered(const irep_idt &left, const irep_idt &right)
{
  return left < right ? relationt{left, right} : relationt{right, left};
}

void kill(const irep_idt &root, factst &facts)
{
  for(auto it = facts.begin(); it != facts.end();)
    if(it->first == root || it->second == root)
      it = facts.erase(it);
    else
      ++it;
}

// The supported source fragment has direct array lvalues. Scanning the whole
// lvalue also fails conservatively for other aggregate views. An indirect write
// has no trustworthy root and therefore kills every relation.
void kill_lvalue(
  const exprt &lhs,
  factst &facts,
  const std::set<irep_idt> &certified)
{
  if(lhs.id() == ID_dereference)
  {
    facts.clear();
    return;
  }
  if(lhs.id() == ID_symbol)
  {
    const auto &id = to_symbol_expr(lhs).get_identifier();
    if(certified.count(id))
      kill(id, facts);
    return;
  }
  for(const auto &operand : lhs.operands())
    kill_lvalue(operand, facts, certified);
}

void transfer(
  const goto_programt::instructiont &instruction,
  factst &facts,
  const std::set<irep_idt> &certified)
{
  if(instruction.is_decl())
    kill(instruction.decl_symbol().get_identifier(), facts);
  else if(instruction.is_dead())
    kill(instruction.dead_symbol().get_identifier(), facts);
  else if(instruction.is_assign())
  {
    const auto &lhs = instruction.assign_lhs();
    const auto &rhs = instruction.assign_rhs();
    if(
      instruction.code().get_bool("c2btor_certified_array_copy") &&
      lhs.id() == ID_symbol && rhs.id() == ID_symbol &&
      lhs.type() == rhs.type() && lhs.type().id() == ID_array)
    {
      const auto &destination = to_symbol_expr(lhs).get_identifier();
      const auto &source = to_symbol_expr(rhs).get_identifier();
      if(certified.count(destination) && certified.count(source))
      {
        if(destination == source)
          return;
        std::vector<irep_idt> source_class{source};
        for(const auto &relation : facts)
          if(relation.first == source)
            source_class.push_back(relation.second);
          else if(relation.second == source)
            source_class.push_back(relation.first);
        kill(destination, facts);
        for(const auto &member : source_class)
          if(member != destination)
            facts.insert(ordered(destination, member));
        return;
      }
    }
    kill_lvalue(lhs, facts, certified);
  }
  else if(
    instruction.is_function_call() || instruction.is_other() ||
    instruction.is_start_thread() || instruction.is_end_thread())
    facts.clear();
}

factst meet(const factst &left, const factst &right)
{
  factst result;
  std::set_intersection(
    left.begin(),
    left.end(),
    right.begin(),
    right.end(),
    std::inserter(result, result.end()));
  return result;
}

void rewrite(exprt &expr, const factst &facts, std::size_t &count)
{
  if(
    (expr.id() == ID_equal || expr.id() == ID_notequal) &&
    expr.operands().size() == 2 && expr.operands()[0].id() == ID_index &&
    expr.operands()[1].id() == ID_index)
  {
    const auto &left = to_index_expr(expr.operands()[0]);
    const auto &right = to_index_expr(expr.operands()[1]);
    if(
      left.array().id() == ID_symbol && right.array().id() == ID_symbol &&
      left.type() == right.type() &&
      left.array().type() == right.array().type() &&
      left.index() == right.index() &&
      facts.count(ordered(
        to_symbol_expr(left.array()).get_identifier(),
        to_symbol_expr(right.array()).get_identifier())))
    {
      expr = from_integer(expr.id() == ID_equal ? 1 : 0, expr.type());
      ++count;
      return;
    }
  }
  for(auto &operand : expr.operands())
    rewrite(operand, facts, count);
}
beforet equalities_before(
  goto_programt &program,
  const std::set<irep_idt> &certified_arrays)
{
  beforet before;
  if(program.instructions.empty() || certified_arrays.empty())
    return before;
  using targett = goto_programt::targett;
  std::deque<targett> pending;
  const auto entry = program.instructions.begin();
  before.emplace(&*entry, factst{});
  pending.push_back(entry);
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    auto after = before.at(&*current);
    transfer(*current, after, certified_arrays);
    // An unseen predecessor is lattice top. Any later conflicting reachable
    // predecessor removes relations before rewriting starts.
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
  return before;
}

void rewrite_read(
  exprt &expr,
  const factst &facts,
  const namespacet &ns,
  std::size_t &count)
{
  // An indexed lvalue below address_of observes object identity, not the
  // stored element value. Certified roots exclude this use already, but the
  // rewrite itself must still distinguish a read from an address expression.
  if(expr.id() == ID_address_of)
    return;
  for(auto &operand : expr.operands())
    rewrite_read(operand, facts, ns, count);
  if(expr.id() != ID_index || to_index_expr(expr).array().id() != ID_symbol)
    return;
  auto &index = to_index_expr(expr);
  const auto &root = to_symbol_expr(index.array()).get_identifier();
  auto canonical = root;
  for(const auto &relation : facts)
  {
    const auto candidate = relation.first == root    ? relation.second
                           : relation.second == root ? relation.first
                                                     : root;
    if(id2string(candidate) < id2string(canonical))
    {
      const symbolt *symbol = nullptr;
      if(
        !ns.lookup(candidate, symbol) && symbol &&
        symbol->type == index.array().type())
        canonical = candidate;
    }
  }
  if(canonical != root)
  {
    index.array() = symbol_exprt(canonical, index.array().type());
    ++count;
  }
}
} // namespace

std::size_t prune_equal_array_comparisons(
  goto_programt &program,
  const namespacet &,
  const std::set<irep_idt> &certified_arrays)
{
  const auto before = equalities_before(program, certified_arrays);
  std::size_t count = 0;
  for(auto &instruction : program.instructions)
  {
    const auto found = before.find(&instruction);
    if(found == before.end())
      continue;
    if(instruction.is_assign())
      rewrite(instruction.assign_rhs_nonconst(), found->second, count);
    if(instruction.has_condition())
      rewrite(instruction.condition_nonconst(), found->second, count);
  }
  return count;
}

std::size_t prune_equal_array_reads(
  goto_programt &program,
  const namespacet &ns,
  const std::set<irep_idt> &certified_arrays)
{
  const auto before = equalities_before(program, certified_arrays);
  std::size_t count = 0;
  for(auto &instruction : program.instructions)
  {
    const auto found = before.find(&instruction);
    if(found == before.end())
      continue;
    if(instruction.is_assign())
      rewrite_read(instruction.assign_rhs_nonconst(), found->second, ns, count);
    if(instruction.has_condition())
      rewrite_read(instruction.condition_nonconst(), found->second, ns, count);
  }
  return count;
}
