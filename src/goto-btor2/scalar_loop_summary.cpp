// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "scalar_loop_summary.h"
#include "source_event_provenance.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/remove_skip.h>

#include "pre_state_optimization.h"

#include <algorithm>
#include <deque>
#include <map>
#include <optional>
#include <unordered_map>
#include <vector>

namespace
{
using instructiont = goto_programt::instructiont;
using constantst = std::map<irep_idt, mp_integer>;
using beforet = std::unordered_map<const instructiont *, constantst>;

bool integer_type(const typet &type)
{
  return (type.id() == ID_signedbv || type.id() == ID_unsignedbv) &&
         !type.get_bool(ID_C_volatile) && !type.get_bool(ID_C_atomic);
}

bool fits(const mp_integer &value, const typet &type)
{
  if(!integer_type(type))
    return false;
  const auto &integer = to_integer_bitvector_type(type);
  return value >= integer.smallest() && value <= integer.largest();
}

bool plain_symbol(const exprt &expr, const namespacet &ns)
{
  if(expr.id() != ID_symbol || !integer_type(expr.type()))
    return false;
  const symbolt *symbol = nullptr;
  return !ns.lookup(to_symbol_expr(expr).get_identifier(), symbol) && symbol &&
         !symbol->is_type && symbol->type == expr.type() &&
         integer_type(symbol->type);
}

// A deliberately small evaluator. Every arithmetic intermediate and every
// conversion must fit its own type; no C promotion or wrap is invented here.
std::optional<mp_integer>
evaluate(const exprt &expr, const constantst &constants, const namespacet &ns)
{
  if(!integer_type(expr.type()))
    return {};
  if(expr.id() == ID_constant)
  {
    mp_integer value;
    return !to_integer(to_constant_expr(expr), value) &&
               fits(value, expr.type())
             ? std::optional<mp_integer>(value)
             : std::nullopt;
  }
  if(expr.id() == ID_symbol && plain_symbol(expr, ns))
  {
    const auto found = constants.find(to_symbol_expr(expr).get_identifier());
    return found != constants.end() && fits(found->second, expr.type())
             ? std::optional<mp_integer>(found->second)
             : std::nullopt;
  }
  if(
    expr.operands().size() == 1 &&
    (expr.id() == ID_typecast || expr.id() == ID_unary_minus))
  {
    auto value = evaluate(expr.operands()[0], constants, ns);
    if(value && expr.id() == ID_unary_minus)
      *value = -*value;
    return value && fits(*value, expr.type()) ? value : std::nullopt;
  }
  if(
    expr.operands().size() != 2 ||
    (expr.id() != ID_plus && expr.id() != ID_minus && expr.id() != ID_mult))
    return {};
  const auto left = evaluate(expr.operands()[0], constants, ns);
  const auto right = evaluate(expr.operands()[1], constants, ns);
  if(!left || !right)
    return {};
  mp_integer result = *left;
  if(expr.id() == ID_plus)
    result += *right;
  else if(expr.id() == ID_minus)
    result -= *right;
  else
    result *= *right;
  return fits(result, expr.type()) ? std::optional<mp_integer>(result)
                                   : std::nullopt;
}

constantst meet(const constantst &left, const constantst &right)
{
  constantst result;
  for(const auto &entry : left)
  {
    const auto other = right.find(entry.first);
    if(other != right.end() && entry.second == other->second)
      result.insert(entry);
  }
  return result;
}

beforet constants_before(
  goto_programt &program,
  const namespacet &ns,
  const std::set<irep_idt> &addressed)
{
  beforet before;
  if(program.instructions.empty())
    return before;
  std::deque<goto_programt::targett> pending;
  const auto entry = program.instructions.begin();
  before.emplace(&*entry, constantst{});
  pending.push_back(entry);
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    auto after = before.at(&*current);
    if(current->is_decl())
      after.erase(current->decl_symbol().get_identifier());
    else if(current->is_dead())
      after.erase(current->dead_symbol().get_identifier());
    else if(current->is_assign() && current->assign_lhs().id() == ID_symbol)
    {
      const auto &lhs = to_symbol_expr(current->assign_lhs());
      const auto id = lhs.get_identifier();
      const auto value = plain_symbol(lhs, ns) && !addressed.count(id)
                           ? evaluate(current->assign_rhs(), after, ns)
                           : std::nullopt;
      if(value)
        after[id] = *value;
      else
        after.erase(id);
    }
    for(const auto next : program.get_successors(current))
    {
      const auto old = before.find(&*next);
      if(old == before.end())
      {
        before.emplace(&*next, after);
        pending.push_back(next);
      }
      else
      {
        auto joined = meet(old->second, after);
        if(joined != old->second)
        {
          old->second = std::move(joined);
          pending.push_back(next);
        }
      }
    }
  }
  return before;
}

bool harmless(const instructiont &instruction)
{
  return instruction.is_skip() || instruction.is_location();
}

bool contains(const exprt &expr, const irep_idt &id)
{
  if(expr.id() == ID_symbol && to_symbol_expr(expr).get_identifier() == id)
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) { return contains(operand, id); });
}

// Same-type casts do not alter a value or its arithmetic width. In particular,
// a narrowing cast around promoted C arithmetic is deliberately not accepted.
const exprt &without_identity_casts(const exprt &expr)
{
  if(
    expr.id() == ID_typecast && expr.operands().size() == 1 &&
    expr.type() == expr.operands()[0].type())
    return without_identity_casts(expr.operands()[0]);
  return expr;
}

std::optional<mp_integer> additive_step(
  const exprt &expression,
  const symbol_exprt &symbol,
  const namespacet &ns)
{
  const auto &rhs = without_identity_casts(expression);
  if(
    rhs.type() != symbol.type() || rhs.operands().size() != 2 ||
    (rhs.id() != ID_plus && rhs.id() != ID_minus) ||
    rhs.operands()[0].type() != symbol.type() ||
    rhs.operands()[1].type() != symbol.type())
    return {};
  if(without_identity_casts(rhs.operands()[0]) == symbol)
  {
    auto amount = evaluate(rhs.operands()[1], constantst{}, ns);
    if(amount && rhs.id() == ID_minus)
      *amount = -*amount;
    return amount;
  }
  if(rhs.id() == ID_plus && without_identity_casts(rhs.operands()[1]) == symbol)
    return evaluate(rhs.operands()[0], constantst{}, ns);
  return {};
}
} // namespace

scalar_loop_summary_reportt
summarize_scalar_loops(goto_programt &program, const namespacet &ns)
{
  scalar_loop_summary_reportt report;
  const auto memory = scan_pre_state_memory_symbols(program, ns);
  if(memory.arbitrary_pointer_input)
  {
    report.diagnostics.push_back(
      "retained: arbitrary pointer input opens aliases");
    return report;
  }
  // No unknown external or concurrent effect may invalidate scalar constants
  // or the no-alias certificate before reaching a summarized loop.
  for(const auto &instruction : program.instructions)
    if(
      instruction.is_start_thread() || instruction.is_end_thread() ||
      instruction.is_function_call() || instruction.is_other() ||
      (instruction.is_assign() &&
       instruction.assign_lhs().id() == ID_dereference))
    {
      report.diagnostics.push_back(
        "retained: thread, call, OTHER operation, or indirect write");
      return report;
    }

  std::vector<goto_programt::targett> order;
  std::map<const instructiont *, std::size_t> positions;
  for(auto it = program.instructions.begin(); it != program.instructions.end();
      ++it)
  {
    positions[&*it] = order.size();
    order.push_back(it);
  }
  const auto before = constants_before(program, ns, memory.addressed_symbols);
  for(std::size_t back = 0; back < order.size(); ++back)
  {
    const auto &jump = *order[back];
    if(!jump.is_goto() || jump.condition() != true || jump.targets.size() != 1)
      continue;
    const auto head = positions.at(&*jump.targets.front());
    if(head == 0 || head >= back || back + 1 >= order.size())
      continue;
    const auto &header = *order[head];
    if(
      !header.is_goto() || header.targets.size() != 1 ||
      positions.at(&*header.targets.front()) != back + 1)
      continue;
    ++report.candidates;
    const auto reject = [&](const std::string &why)
    {
      report.diagnostics.push_back(
        "loop " + std::to_string(head) + ": retained: " + why);
    };

    exprt relation = header.condition();
    bool negated = false;
    if(relation.id() == ID_not && relation.operands().size() == 1)
    {
      relation = relation.operands()[0];
      negated = true;
    }
    irep_idt comparison = relation.id();
    if(!negated)
      comparison = comparison == ID_gt   ? ID_le
                   : comparison == ID_ge ? ID_lt
                                         : irep_idt();
    if(
      (comparison != ID_lt && comparison != ID_le) ||
      relation.operands().size() != 2 ||
      !plain_symbol(relation.operands()[0], ns))
    {
      reject("not a canonical increasing integer guard");
      continue;
    }
    const auto counter = to_symbol_expr(relation.operands()[0]);
    const auto counter_id = counter.get_identifier();
    if(
      memory.addressed_symbols.count(counter_id) ||
      relation.operands()[1].type() != counter.type() ||
      contains(relation.operands()[1], counter_id))
    {
      reject("counter aliases, mixed-width bound, or self-dependent guard");
      continue;
    }
    std::size_t init = head - 1, step = back - 1;
    while(init > 0 && harmless(*order[init]))
      --init;
    while(step > head && harmless(*order[step]))
      --step;
    if(
      !order[init]->is_assign() || order[init]->assign_lhs() != counter ||
      !order[step]->is_assign() || order[step]->assign_lhs() != counter)
    {
      reject("counter initialization or step is not adjacent");
      continue;
    }
    const auto known = before.find(&*order[init]);
    const constantst empty;
    const auto &constants = known == before.end() ? empty : known->second;
    const auto initial = evaluate(order[init]->assign_rhs(), constants, ns);
    const auto bound = evaluate(relation.operands()[1], constants, ns);
    const auto increment =
      additive_step(order[step]->assign_rhs(), counter, ns);
    if(
      !initial || !bound || !fits(*initial, counter.type()) || !increment ||
      *increment != 1)
    {
      reject("initial value, invariant bound, or unit step is not certified");
      continue;
    }
    const mp_integer last = *bound - (comparison == ID_lt ? 1 : 0);
    const mp_integer trips =
      last < *initial ? mp_integer(0) : last - *initial + 1;
    const mp_integer final_counter = *initial + trips;
    if(!fits(final_counter, counter.type()))
    {
      reject("counter would wrap before exiting");
      continue;
    }

    std::optional<symbol_exprt> accumulator;
    std::optional<mp_integer> amount;
    bool valid = true;
    for(std::size_t i = head + 1; i < back && valid; ++i)
    {
      const auto &instruction = *order[i];
      if(i == step || harmless(instruction))
        continue;
      if(
        accumulator || !instruction.is_assign() ||
        !plain_symbol(instruction.assign_lhs(), ns))
      {
        valid = false;
        break;
      }
      accumulator = to_symbol_expr(instruction.assign_lhs());
      const auto id = accumulator->get_identifier();
      amount = additive_step(instruction.assign_rhs(), *accumulator, ns);
      if(
        !amount || id == counter_id || memory.addressed_symbols.count(id) ||
        contains(relation.operands()[1], id))
        valid = false;
    }
    if(!valid || (accumulator && !amount))
    {
      reject(
        "body is not empty or one unaliased same-type integer constant "
        "reduction");
      continue;
    }
    for(std::size_t i = 0; i < order.size() && valid; ++i)
      for(const auto &target : order[i]->targets)
      {
        const auto destination = positions.at(&*target);
        if(destination > init && destination <= back && (i < head || i > back))
          valid = false;
      }
    if(!valid)
    {
      reject("outside edge bypasses initialization or enters the body");
      continue;
    }

    const mp_integer delta = accumulator ? trips * *amount : mp_integer(0);
    exprt replacement = accumulator ? exprt(*accumulator) : nil_exprt();
    if(accumulator && accumulator->type().id() == ID_signedbv && trips != 0)
    {
      const auto entry = evaluate(*accumulator, constants, ns);
      if(!entry || !fits(*entry + delta, accumulator->type()))
      {
        reject("signed accumulator entry or no-overflow range is unknown");
        continue;
      }
      // A constant result avoids introducing a signed delta whose magnitude
      // might not itself fit, e.g. INT_MIN - INT_MIN == 0.
      replacement = from_integer(*entry + delta, accumulator->type());
    }
    else if(accumulator && trips != 0)
      replacement =
        plus_exprt(*accumulator, from_integer(delta, accumulator->type()));

    auto location = order[head]->source_location();
    if(!btor2_original_event_ids(location).empty())
    {
      for(std::size_t i = head; i <= back; ++i)
        btor2_merge_event_origins(location, order[i]->source_location());
      location.set("c2btor_summary_kind", accumulator ? "scalar-reduction" : "scalar-counter");
      location.set("c2btor_summary_id", "scalar-summary-" + id2string(location.get("c2btor_original_event_ids")));
    }
    if(trips == 0 || !accumulator)
      order[head]->turn_into_skip();
    else
      *order[head] = goto_programt::make_assignment(
        code_assignt(*accumulator, replacement), location);
    for(std::size_t i = head + 1; i <= back; ++i)
      if(i != step)
        order[i]->turn_into_skip();
    *order[step] = goto_programt::make_assignment(
      code_assignt(counter, from_integer(final_counter, counter.type())),
      location);
    ++report.summarized;
    if(!accumulator)
      ++report.empty_loops;
    report.diagnostics.push_back(
      accumulator
        ? id2string(accumulator->get_identifier()) + ": summarized " +
            integer2string(trips) + " constant integer reductions"
        : id2string(counter_id) + ": summarized " + integer2string(trips) +
            " iterations with no body effects");
  }
  if(report.summarized)
  {
    remove_skip(program);
    program.update();
  }
  return report;
}
