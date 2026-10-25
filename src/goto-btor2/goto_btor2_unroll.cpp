// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

/*******************************************************************\

Module: Goto 程序常量界循环展开 - 实现

Authors: C2BTOR contributors; CBMC attribution is retained in LICENSES/

\*******************************************************************/

#include "goto_btor2_unroll.h"
#include "memory_capacity.h"

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/bitvector_types.h>
#include <util/irep_ids.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/symbol.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <algorithm>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

namespace
{

bool is_alloc_call(const goto_programt::instructiont &instr)
{
  if(instr.is_function_call())
  {
    const exprt &function = instr.call_function();
    irep_idt fid;
    if(function.id() == ID_symbol)
      fid = to_symbol_expr(function).get_identifier();
    else if(function.id() == ID_address_of)
    {
      const exprt &obj =
        function.operands().empty() ? nil_exprt() : function.operands()[0];
      if(obj.id() == ID_symbol)
        fid = to_symbol_expr(obj).get_identifier();
    }
    const std::string s = id2string(fid);
    const std::string malloc_suffix = "::malloc";
    const std::string calloc_suffix = "::calloc";
    return s == "malloc" || s == "calloc" ||
           (s.size() >= malloc_suffix.size() &&
            s.compare(
              s.size() - malloc_suffix.size(),
              malloc_suffix.size(),
              malloc_suffix) == 0) ||
           (s.size() >= calloc_suffix.size() &&
            s.compare(
              s.size() - calloc_suffix.size(),
              calloc_suffix.size(),
              calloc_suffix) == 0);
  }
  if(instr.is_assign())
  {
    const exprt &rhs = instr.assign_rhs();
    const exprt *cur = &rhs;
    while(cur->id() == ID_typecast)
      cur = &to_typecast_expr(*cur).op();
    return cur->id() == ID_side_effect &&
           to_side_effect_expr(*cur).get_statement() == ID_allocate;
  }
  return false;
}

std::optional<mp_integer> as_integer(const exprt &e)
{
  if(e.id() == ID_unary_minus)
  {
    auto v = as_integer(to_unary_minus_expr(e).op());
    if(v.has_value())
      return -*v;
    return std::nullopt;
  }
  if(e.is_constant())
  {
    mp_integer v;
    if(!to_integer(to_constant_expr(e), v))
      return v;
  }
  return std::nullopt;
}

std::map<irep_idt, mp_integer> collect_constants(
  const std::vector<const goto_programt::instructiont *> &order,
  std::size_t stop_before)
{
  std::map<irep_idt, mp_integer> known;
  for(std::size_t i = 0; i < stop_before && i < order.size(); ++i)
  {
    const auto &ins = *order[i];
    // Only straight-line reaching constants are hints for the trip count.
    if(ins.is_target() || ins.is_goto() || ins.is_function_call())
      known.clear();
    if(ins.is_decl())
      known.erase(ins.decl_symbol().get_identifier());
    if(ins.is_dead())
      known.erase(ins.dead_symbol().get_identifier());
    if(ins.is_other())
      known.clear();
    if(!ins.is_assign())
      continue;
    const auto &lhs = ins.assign_lhs();
    if(lhs.id() != ID_symbol)
    {
      known.clear();
      continue;
    }
    const auto id = to_symbol_expr(lhs).get_identifier();
    const auto &rhs = ins.assign_rhs();
    if(auto value = as_integer(rhs))
      known[id] = *value;
    else if(
      rhs.id() == ID_symbol &&
      known.count(to_symbol_expr(rhs).get_identifier()))
      known[id] = known.at(to_symbol_expr(rhs).get_identifier());
    else
      known.erase(id);
  }
  return known;
}

struct parsed_guardt
{
  irep_idt var, op;
  exprt threshold;
};

std::vector<parsed_guardt> parse_guard(const exprt &guard)
{
  exprt relation = guard;
  bool negated = false;
  if(relation.id() == ID_not)
  {
    relation = to_not_expr(relation).op();
    negated = true;
  }
  static const std::map<irep_idt, irep_idt> negate = {
    {ID_gt, ID_le}, {ID_le, ID_gt}, {ID_lt, ID_ge}, {ID_ge, ID_lt}};
  static const std::map<irep_idt, irep_idt> swap = {
    {ID_gt, ID_lt}, {ID_lt, ID_gt}, {ID_ge, ID_le}, {ID_le, ID_ge}};
  if(!negate.count(relation.id()))
    return {};
  const auto &g = to_binary_expr(relation);
  const auto op = negated ? negate.at(g.id()) : g.id();
  std::vector<parsed_guardt> candidates;
  if(g.op0().id() == ID_symbol)
    candidates.push_back(
      {to_symbol_expr(g.op0()).get_identifier(), op, g.op1()});
  if(g.op1().id() == ID_symbol)
    candidates.push_back(
      {to_symbol_expr(g.op1()).get_identifier(), swap.at(op), g.op0()});
  return candidates;
}

std::optional<mp_integer> induction_delta(
  const goto_programt::instructiont &instruction,
  const irep_idt &var)
{
  if(
    !instruction.is_assign() || instruction.assign_lhs().id() != ID_symbol ||
    to_symbol_expr(instruction.assign_lhs()).get_identifier() != var)
    return mp_integer(0);
  const auto &rhs = instruction.assign_rhs();
  if(
    (rhs.id() != ID_plus && rhs.id() != ID_minus) || rhs.operands().size() != 2)
    return {};
  const auto &left = rhs.operands()[0], &right = rhs.operands()[1];
  if(left.id() == ID_symbol && to_symbol_expr(left).get_identifier() == var)
  {
    const auto delta = as_integer(right);
    if(delta)
      return rhs.id() == ID_minus ? -*delta : *delta;
  }
  if(
    rhs.id() == ID_plus && right.id() == ID_symbol &&
    to_symbol_expr(right).get_identifier() == var)
    return as_integer(left);
  return {};
}

std::optional<mp_integer> trip_bound(
  const parsed_guardt &guard,
  const mp_integer &threshold,
  const mp_integer &initial,
  const mp_integer &minimum_step)
{
  // Mathematical division gives the complete bound without enumerating trips.
  // The caller separately proves that all machine updates remain in range.
  if(guard.op == ID_lt || guard.op == ID_le)
  {
    if(initial > threshold || (initial == threshold && guard.op == ID_lt))
      return mp_integer(0);
    if(minimum_step <= 0)
      return {};
    const mp_integer distance =
      threshold - initial + (guard.op == ID_le ? 1 : 0);
    return (distance + minimum_step - 1) / minimum_step;
  }
  if(initial < threshold || (initial == threshold && guard.op == ID_gt))
    return mp_integer(0);
  if(minimum_step >= 0)
    return {};
  const mp_integer stride = -minimum_step;
  const mp_integer distance = initial - threshold + (guard.op == ID_ge ? 1 : 0);
  return (distance + stride - 1) / stride;
}

} // namespace

std::size_t unroll_malloc_counted_loops(
  goto_programt &program,
  const namespacet &ns,
  messaget &log)
{
  std::size_t total = 0;
  // Intervals and alias facts must describe the original sizing CFG. Re-running
  // after cutting a loop could underestimate values modified by that loop.
  const auto bounds = infer_memory_capacity(program, ns, {}, true);
  for(;;)
  {
    std::vector<goto_programt::targett> order;
    std::vector<const goto_programt::instructiont *> instructions;
    std::map<const goto_programt::instructiont *, std::size_t> positions;
    for(auto pc = program.instructions.begin();
        pc != program.instructions.end();
        ++pc)
    {
      positions.emplace(&*pc, order.size());
      order.push_back(pc);
      instructions.push_back(&*pc);
    }
    bool summarized = false;
    for(std::size_t back = 0; back < order.size() && !summarized; ++back)
    {
      const auto &edge = *order[back];
      if(
        !edge.is_goto() || !edge.condition().is_true() ||
        edge.targets.size() != 1)
        continue;
      const auto head = positions.at(&*edge.get_target());
      if(head >= back || back + 1 >= order.size())
        continue;
      const auto &header = *order[head];
      if(
        !header.is_goto() || header.condition().is_true() ||
        header.targets.size() != 1 ||
        positions.at(&*header.get_target()) != back + 1)
        continue;
      if(!std::any_of(
           instructions.begin() + head + 1,
           instructions.begin() + back,
           [](const auto *instruction) { return is_alloc_call(*instruction); }))
        continue;
      // Internal zero-allocation cycles need no trip bound. They remain in the
      // sizing CFG; allocation-count dataflow crosses them without growth.
      std::vector<std::vector<std::size_t>> successors(order.size()),
        predecessors(order.size());
      bool single_entry = true;
      for(std::size_t i = 0; i < order.size(); ++i)
      {
        for(const auto &target : order[i]->targets)
        {
          const auto to = positions.at(&*target);
          if((i <= head || i > back) && to >= head && to <= back)
            single_entry = false;
          if(i > head && i < back && to == head)
            single_entry =
              false; // additional outer back edge needs its own certificate
        }
        if(i <= head || i >= back)
          continue;
        for(const auto next : program.get_successors(order[i]))
        {
          const auto to = positions.at(&*next);
          if(to > head && to <= back)
          {
            successors[i].push_back(to);
            predecessors[to].push_back(i);
          }
        }
      }
      if(!single_entry)
        continue;
      std::vector<bool> reaches_back(order.size(), false);
      std::vector<std::size_t> pending{back};
      reaches_back[back] = true;
      while(!pending.empty())
      {
        const auto node = pending.back();
        pending.pop_back();
        for(const auto before : predecessors[node])
          if(!reaches_back[before])
          {
            reaches_back[before] = true;
            pending.push_back(before);
          }
      }
      exprt continuation = simplify_expr(not_exprt(header.condition()), ns);
      for(const auto &guard : parse_guard(continuation))
      {
        const auto known = collect_constants(instructions, head);
        const auto initial = known.find(guard.var);
        const auto &type = ns.lookup(guard.var).type;
        if(
          initial == known.end() ||
          (type.id() != ID_signedbv && type.id() != ID_unsignedbv))
          continue;
        std::optional<mp_integer> threshold = as_integer(guard.threshold);
        if(!threshold)
        {
          const auto state = bounds.condition_intervals.find(&header);
          if(state != bounds.condition_intervals.end())
          {
            const auto interval = state->second.find(guard.threshold);
            if(interval != state->second.end())
              threshold = guard.op == ID_lt || guard.op == ID_le
                            ? interval->second.second
                            : interval->second.first;
          }
        }
        if(!threshold)
          continue;
        bool safe = true;
        const bool increasing = guard.op == ID_lt || guard.op == ID_le;
        std::vector<mp_integer> deltas(order.size(), 0);
        for(std::size_t i = 0; i < order.size(); ++i)
        {
          if(
            has_subexpr(
              order[i]->code(),
              [&](const exprt &e)
              {
                return e.id() == ID_address_of &&
                       has_symbol_expr(
                         to_address_of_expr(e).object(), guard.var, true);
              }) ||
            (order[i]->has_condition() &&
             has_subexpr(
               order[i]->condition(),
               [&](const exprt &e)
               {
                 return e.id() == ID_address_of &&
                        has_symbol_expr(
                          to_address_of_expr(e).object(), guard.var, true);
               })))
            safe = false;
          if(i <= head || i >= back || !reaches_back[i])
            continue;
          if(bounds.unknown_indirect_writes.count(&*order[i]))
            safe = false;
          const auto delta = induction_delta(*order[i], guard.var);
          if(!delta || (increasing ? *delta < 0 : *delta > 0))
            safe = false;
          else
            deltas[i] = increasing ? *delta : -*delta;
          const bool memory_event =
            order[i]->is_other() &&
            (order[i]->get_other().get_statement() == "c2btor_deallocate" ||
             order[i]->get_other().get_statement() == "c2btor_copy_check" ||
             order[i]->get_other().get_statement() == "c2btor_copy_byte" ||
             order[i]->get_other().get_statement() == "c2btor_copy_range");
          // Inlining a discarded malloc result leaves a pure EXPRESSION.
          // It observes the result without changing the induction state.
          const bool pure_expression =
            order[i]->is_other() &&
            order[i]->get_other().get_statement() == ID_expression &&
            !has_subexpr(
              order[i]->code(),
              [](const exprt &expr) { return expr.id() == ID_side_effect; });
          if(
            order[i]->is_function_call() ||
            (order[i]->is_other() && !memory_event && !pure_expression) ||
            (order[i]->is_decl() &&
             order[i]->decl_symbol().get_identifier() == guard.var) ||
            (order[i]->is_dead() &&
             order[i]->dead_symbol().get_identifier() == guard.var))
            safe = false;
        }
        if(!safe)
          continue;
        // Every path returning to the outer header must progress. A positive
        // update cycle has no finite maximum; zero-update inner cycles are OK.
        std::vector<std::optional<mp_integer>> minimum(order.size()),
          maximum(order.size());
        minimum[head + 1] = maximum[head + 1] = 0;
        bool changed = false;
        for(std::size_t pass = head + 1; pass <= back; ++pass)
        {
          changed = false;
          for(std::size_t i = head + 1; i < back; ++i)
            if(reaches_back[i] && minimum[i])
              for(const auto next : successors[i])
              {
                const mp_integer lo = *minimum[i] + deltas[i];
                const mp_integer hi = *maximum[i] + deltas[i];
                if(!minimum[next] || lo < *minimum[next])
                {
                  minimum[next] = lo;
                  changed = true;
                }
                if(!maximum[next] || hi > *maximum[next])
                {
                  maximum[next] = hi;
                  changed = true;
                }
              }
          if(!changed)
            break;
        }
        if(changed || !minimum[back] || *minimum[back] <= 0)
          continue;
        const mp_integer step = increasing ? *minimum[back] : -*minimum[back];
        const auto trips = trip_bound(guard, *threshold, initial->second, step);
        if(!trips)
          continue;
        const auto &machine = to_integer_bitvector_type(type);
        const mp_integer final =
          initial->second + (increasing ? 1 : -1) * *trips * *maximum[back];
        if(
          initial->second < machine.smallest() ||
          initial->second > machine.largest() || final < machine.smallest() ||
          final > machine.largest())
          continue;
        for(std::size_t i = head + 1; i < back; ++i)
          if(allocation_evaluation_weight(*order[i]) != 0)
          {
            const auto old =
              order[i]->code().get_string(C2BTOR_ALLOCATION_MULTIPLIER);
            const mp_integer factor =
              old.empty() ? mp_integer(1) : string2integer(old);
            order[i]->code_nonconst().set(
              C2BTOR_ALLOCATION_MULTIPLIER, integer2string(factor * *trips));
          }
        // This is exclusively an allocation-count overapproximation. Memory
        // capacity is inferred from the original program, never this summary.
        order[back]->turn_into_skip();
        program.update();
        ++total;
        summarized = true;
        log.status()
          << "[capacity analysis] summarized counted allocation loop (K="
          << *trips << ") around '" << guard.var << "'" << messaget::eom;
        break;
      }
    }
    if(!summarized)
      break;
  }
  return total;
}
