// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "scalar_block_liveness.h"

#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "btor2_type_utils.h"

#include <deque>

namespace
{
using symbol_sett = std::set<irep_idt>;

void add_symbols(const exprt &expression, symbol_sett &destination)
{
  const auto symbols = find_symbol_identifiers(expression);
  destination.insert(symbols.begin(), symbols.end());
}

void add_type_dependencies(
  const typet &type,
  const namespacet &ns,
  symbol_sett &destination,
  symbol_sett &visited)
{
  find_symbols_sett symbols;
  find_type_and_expr_symbols(type, symbols);
  for(const auto &id : symbols)
  {
    destination.insert(id);
    const symbolt *symbol = nullptr;
    if(visited.insert(id).second && !ns.lookup(id, symbol) && symbol)
      add_type_dependencies(symbol->type, ns, destination, visited);
  }
}

void add_expression_types(
  const exprt &expression,
  const namespacet &ns,
  symbol_sett &destination,
  symbol_sett &visited)
{
  add_type_dependencies(expression.type(), ns, destination, visited);
  for(const auto &key : {ID_C_c_sizeof_type, ID_C_va_arg_type})
    if(expression.find(key).is_not_nil())
      add_type_dependencies(
        static_cast<const typet &>(expression.find(key)),
        ns,
        destination,
        visited);
  for(const auto &operand : expression.operands())
    add_expression_types(operand, ns, destination, visited);
}

bool scalar_symbol(const exprt &expression, const namespacet &ns)
{
  if(expression.id() != ID_symbol)
    return false;
  const auto type = follow_tag_type(expression.type(), ns);
  return type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
         type.id() == ID_bool || type.id() == ID_c_bool;
}
} // namespace

scalar_block_liveness_reportt classify_scalar_block_state(
  const goto_programt &program,
  const namespacet &ns,
  const std::vector<std::vector<unsigned>> &blocks,
  const std::set<irep_idt> &candidate_ids,
  const std::map<unsigned, std::vector<unsigned>> &successors)
{
  struct nodet
  {
    symbol_sett uses, definitions, live_in;
    std::vector<unsigned> successors, predecessors;
  };
  std::vector<nodet> nodes(program.instructions.size());
  symbol_sett all_symbols;
  unsigned location = 0;
  for(const auto &instruction : program.instructions)
  {
    auto &node = nodes[location++];
    symbol_sett visited_types;
    add_expression_types(instruction.code(), ns, node.uses, visited_types);
    if(instruction.is_assign() && scalar_symbol(instruction.assign_lhs(), ns))
    {
      node.definitions.insert(
        to_symbol_expr(instruction.assign_lhs()).get_identifier());
      add_symbols(instruction.assign_rhs(), node.uses);
    }
    else if(
      instruction.is_decl() && scalar_symbol(instruction.decl_symbol(), ns))
      node.definitions.insert(instruction.decl_symbol().get_identifier());
    else if(
      instruction.is_dead() && scalar_symbol(instruction.dead_symbol(), ns))
      ; // DEAD does not kill a scalar value in the converter's transition
        // model.
    else
      // Unknown calls/custom memory operations have no inferred definitions.
      add_symbols(instruction.code(), node.uses);
    if(instruction.has_condition())
    {
      add_symbols(instruction.condition(), node.uses);
      add_expression_types(
        instruction.condition(), ns, node.uses, visited_types);
    }
    all_symbols.insert(node.uses.begin(), node.uses.end());
  }

  // A malformed or incomplete caller CFG must not justify removing state.
  bool complete = successors.size() == nodes.size();
  std::set<unsigned> covered;
  for(const auto &block : blocks)
  {
    complete &= !block.empty();
    for(const auto loc : block)
      complete &= loc < nodes.size() && covered.insert(loc).second;
  }
  complete &= covered.size() == nodes.size();
  for(const auto &entry : successors)
  {
    if(entry.first >= nodes.size())
    {
      complete = false;
      continue;
    }
    for(const auto target : entry.second)
      if(target >= nodes.size())
        complete = false;
      else
      {
        nodes[entry.first].successors.push_back(target);
        nodes[target].predecessors.push_back(entry.first);
      }
  }

  scalar_block_liveness_reportt report;
  if(!complete)
  {
    report.persistent_symbols = candidate_ids;
    all_symbols.insert(candidate_ids.begin(), candidate_ids.end());
    for(const auto &block : blocks)
      if(!block.empty())
        report.entry_live[block.front()] = all_symbols;
    return report;
  }

  // A backwards monotone fixed point includes every supplied loop backedge.
  std::deque<unsigned> pending;
  std::vector<bool> queued(nodes.size(), true);
  for(unsigned loc = nodes.size(); loc > 0; --loc)
    pending.push_back(loc - 1);
  while(!pending.empty())
  {
    const auto loc = pending.front();
    pending.pop_front();
    queued[loc] = false;
    auto &node = nodes[loc];
    symbol_sett incoming;
    for(const auto successor : node.successors)
      incoming.insert(
        nodes[successor].live_in.begin(), nodes[successor].live_in.end());
    for(const auto &definition : node.definitions)
      incoming.erase(definition);
    incoming.insert(node.uses.begin(), node.uses.end());
    if(incoming != node.live_in)
    {
      node.live_in = std::move(incoming);
      for(const auto predecessor : node.predecessors)
        if(!queued[predecessor])
        {
          queued[predecessor] = true;
          pending.push_back(predecessor);
        }
    }
  }
  for(const auto &block : blocks)
  {
    const auto &live = nodes[block.front()].live_in;
    report.entry_live.emplace(block.front(), live);
    for(const auto &id : candidate_ids)
      if(live.count(id))
        report.persistent_symbols.insert(id);
  }
  for(const auto &id : candidate_ids)
    if(!report.persistent_symbols.count(id))
      report.local_symbols.insert(id);
  return report;
}
