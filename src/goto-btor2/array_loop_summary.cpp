// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "array_loop_summary.h"
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
#include <functional>
#include <map>
#include <optional>
#include <vector>

namespace
{
struct intervalt
{
  mp_integer lo, hi;
};
using environmentt = std::map<irep_idt, intervalt>;
using instructiont = goto_programt::instructiont;

bool qualified(const typet &type)
{
  return type.get_bool(ID_C_volatile) || type.get_bool(ID_C_atomic) ||
         (type.id() == ID_array &&
          qualified(to_array_type(type).element_type()));
}

bool integer_type(const typet &type)
{
  return type.id() == ID_signedbv || type.id() == ID_unsignedbv;
}

bool in_type(const intervalt &value, const typet &type)
{
  if(!integer_type(type) || qualified(type))
    return false;
  const auto &bv = to_integer_bitvector_type(type);
  return value.lo >= bv.smallest() && value.hi <= bv.largest();
}

// Every intermediate expression must fit its own machine type. In particular,
// a cast is accepted only when it preserves every mathematical value.
std::optional<intervalt> evaluate(const exprt &expr, const environmentt &env)
{
  if(!integer_type(expr.type()) || qualified(expr.type()))
    return {};
  if(expr.id() == ID_constant)
  {
    mp_integer value;
    if(to_integer(to_constant_expr(expr), value))
      return {};
    return intervalt{value, value};
  }
  if(expr.id() == ID_symbol)
  {
    const auto found = env.find(to_symbol_expr(expr).get_identifier());
    return found != env.end() && in_type(found->second, expr.type())
             ? std::optional<intervalt>(found->second)
             : std::nullopt;
  }
  if(expr.id() == ID_typecast && expr.operands().size() == 1)
  {
    const auto value = evaluate(expr.operands()[0], env);
    return value && in_type(*value, expr.type()) ? value : std::nullopt;
  }
  if(expr.id() == ID_unary_minus && expr.operands().size() == 1)
  {
    const auto value = evaluate(expr.operands()[0], env);
    if(!value)
      return {};
    const intervalt result{-value->hi, -value->lo};
    return in_type(result, expr.type()) ? std::optional<intervalt>(result)
                                        : std::nullopt;
  }
  if(
    (expr.id() != ID_plus && expr.id() != ID_minus && expr.id() != ID_mult) ||
    expr.operands().size() < 2)
    return {};
  auto result = evaluate(expr.operands()[0], env);
  if(!result)
    return {};
  for(std::size_t i = 1; i < expr.operands().size(); ++i)
  {
    const auto rhs = evaluate(expr.operands()[i], env);
    if(!rhs)
      return {};
    if(expr.id() == ID_plus)
      result = intervalt{result->lo + rhs->lo, result->hi + rhs->hi};
    else if(expr.id() == ID_minus)
      result = intervalt{result->lo - rhs->hi, result->hi - rhs->lo};
    else
    {
      const std::vector<mp_integer> products{
        result->lo * rhs->lo,
        result->lo * rhs->hi,
        result->hi * rhs->lo,
        result->hi * rhs->hi};
      const auto bounds = std::minmax_element(products.begin(), products.end());
      result = intervalt{*bounds.first, *bounds.second};
    }
    if(!in_type(*result, expr.type()))
      return {};
  }
  return result;
}

struct loopt
{
  std::size_t init, head, back, step;
  irep_idt counter;
  typet counter_type;
  mp_integer initial, last, final, trips;
};

struct arrayt
{
  symbol_exprt symbol;
  mp_integer length;
};

struct affinet
{
  mp_integer coefficient, constant;
};

std::optional<affinet>
affine(const exprt &expr, const irep_idt &counter, const environmentt &env)
{
  if(!evaluate(expr, env))
    return {};
  if(expr.id() == ID_symbol && to_symbol_expr(expr).get_identifier() == counter)
    return affinet{1, 0};
  // The interval evaluator already checked all intermediate machine widths.
  if(expr.id() == ID_typecast && expr.operands().size() == 1)
    return affine(expr.operands()[0], counter, env);
  if(expr.id() == ID_unary_minus && expr.operands().size() == 1)
  {
    const auto value = affine(expr.operands()[0], counter, env);
    if(value)
      return affinet{-value->coefficient, -value->constant};
    return {};
  }
  if(
    (expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult) &&
    expr.operands().size() == 2)
  {
    const auto left = affine(expr.operands()[0], counter, env);
    const auto right = affine(expr.operands()[1], counter, env);
    if(!left || !right)
      return {};
    if(expr.id() == ID_plus)
      return affinet{
        left->coefficient + right->coefficient,
        left->constant + right->constant};
    if(expr.id() == ID_minus)
      return affinet{
        left->coefficient - right->coefficient,
        left->constant - right->constant};
    if(left->coefficient == 0)
      return affinet{
        left->constant * right->coefficient, left->constant * right->constant};
    if(right->coefficient == 0)
      return affinet{
        right->constant * left->coefficient, right->constant * left->constant};
    return {};
  }
  const auto value = evaluate(expr, env);
  if(value && value->lo == value->hi)
    return affinet{0, value->lo};
  return {};
}

bool harmless(const instructiont &ins)
{
  return ins.is_skip() || ins.is_location();
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

bool pure_tree(const exprt &expr)
{
  if(
    qualified(expr.type()) || expr.id() == ID_side_effect ||
    expr.id() == ID_dereference)
    return false;
  return std::all_of(expr.operands().begin(), expr.operands().end(), pure_tree);
}

struct nondet_fillt
{
  std::map<irep_idt, std::vector<affinet>> indices;
  std::map<irep_idt, std::size_t> stores;
  std::vector<array_nondet_callt> calls;
};

bool contains_including_types(const irept &tree, const irep_idt &id)
{
  if(tree.id() == ID_symbol && tree.get(ID_identifier) == id)
    return true;
  for(const auto &operand : tree.get_sub())
    if(contains_including_types(operand, id))
      return true;
  for(const auto &named : tree.get_named_sub())
    if(contains_including_types(named.second, id))
      return true;
  return false;
}

void referenced_symbols(const irept &tree, std::set<irep_idt> &symbols)
{
  if(tree.id() == ID_symbol)
    symbols.insert(tree.get(ID_identifier));
  for(const auto &operand : tree.get_sub())
    referenced_symbols(operand, symbols);
  for(const auto &named : tree.get_named_sub())
    referenced_symbols(named.second, symbols);
}

// Each sample has a private, closed lifetime and exactly one destination cell.
// Two stores of one sample would correlate cells and cannot be represented by
// an unconstrained array-valued input.
std::optional<nondet_fillt> independent_nondet_fill(
  const loopt &loop,
  const std::vector<goto_programt::targett> &order,
  const std::map<irep_idt, arrayt> &arrays,
  const environmentt &body,
  const std::set<irep_idt> &addressed,
  const namespacet &ns)
{
  std::vector<std::size_t> effects;
  for(std::size_t i = loop.head + 1; i < loop.back; ++i)
    if(i != loop.step && !harmless(*order[i]))
      effects.push_back(i);
  if(effects.empty() || effects.size() % 4 != 0)
    return {};
  nondet_fillt result;
  std::set<irep_idt> samples;
  // Backends also consult namespace types and static initializers. Follow the
  // referenced-symbol closure so a hidden VLA extent or initializer cannot
  // observe a removed sample, even when its instruction has a shallow type.
  std::set<irep_idt> referenced;
  for(const auto instruction : order)
  {
    referenced_symbols(instruction->code(), referenced);
    if(instruction->has_condition())
      referenced_symbols(instruction->condition(), referenced);
  }
  std::set<irep_idt> inspected;
  std::vector<const symbolt *> visible;
  while(inspected.size() < referenced.size())
  {
    const auto pending = referenced;
    for(const auto &id : pending)
      if(inspected.insert(id).second)
      {
        const symbolt *symbol = nullptr;
        if(!ns.lookup(id, symbol) && symbol)
        {
          visible.push_back(symbol);
          referenced_symbols(symbol->type, referenced);
          referenced_symbols(symbol->value, referenced);
        }
      }
  }
  for(std::size_t i = 0; i < effects.size(); i += 4)
  {
    const auto &decl = *order[effects[i]];
    const auto &input = *order[effects[i + 1]];
    const auto &store = *order[effects[i + 2]];
    const auto &dead = *order[effects[i + 3]];
    if(
      !decl.is_decl() || !input.is_assign() || !store.is_assign() ||
      !dead.is_dead())
      return {};
    const auto &sample = decl.decl_symbol();
    const auto id = sample.get_identifier();
    const auto &value = input.assign_rhs();
    if(
      !integer_type(sample.type()) || qualified(sample.type()) ||
      addressed.count(id) || !samples.insert(id).second ||
      input.assign_lhs() != sample || dead.dead_symbol() != sample ||
      value.id() != ID_side_effect || value.get(ID_statement) != ID_nondet ||
      !value.operands().empty() || value.type() != sample.type() ||
      store.assign_lhs().id() != ID_index || store.assign_rhs() != sample)
      return {};
    const auto &lhs = to_index_expr(store.assign_lhs());
    if(lhs.array().id() != ID_symbol || lhs.type() != sample.type())
      return {};
    const auto root = to_symbol_expr(lhs.array()).get_identifier();
    const auto index = affine(lhs.index(), loop.counter, body);
    if(!arrays.count(root) || !index || !pure_tree(store.code()))
      return {};
    const std::set<std::size_t> lifetime{
      effects[i], effects[i + 1], effects[i + 2], effects[i + 3]};
    for(std::size_t position = 0; position < order.size(); ++position)
      if(
        !lifetime.count(position) &&
        (contains_including_types(order[position]->code(), id) ||
         (order[position]->has_condition() &&
          contains_including_types(order[position]->condition(), id))))
        return {};
    for(const auto symbol : visible)
      if(
        contains_including_types(symbol->type, id) ||
        contains_including_types(symbol->value, id))
        return {};
    result.indices[root].push_back(*index);
    result.stores.emplace(root, effects[i + 2]);
    result.calls.push_back(
      {root,
       index->coefficient,
       index->constant,
       input.source_location(),
       value.get(ID_C_identifier),
       sample.type(),
       i / 4});
  }
  return result;
}
} // namespace

array_loop_summary_reportt
summarize_array_loops(goto_programt &program, const namespacet &ns)
{
  array_loop_summary_reportt report;
  std::vector<goto_programt::targett> order;
  std::map<const instructiont *, std::size_t> positions;
  for(auto it = program.instructions.begin(); it != program.instructions.end();
      ++it)
  {
    positions[&*it] = order.size();
    order.push_back(it);
  }
  const auto memory = scan_pre_state_memory_symbols(program, ns);
  if(memory.arbitrary_pointer_input)
  {
    report.diagnostics.push_back(
      "retained: arbitrary pointer input opens aliases");
    return report;
  }
  // Single-threaded, explicit GotoIR only. Calls and pointer writes might
  // modify induction/bound symbols even without an explicit scalar lhs.
  for(const auto &ins : program.instructions)
    if(
      ins.is_start_thread() || ins.is_end_thread() || ins.is_function_call() ||
      ins.is_other() ||
      (ins.is_assign() && ins.assign_lhs().id() == ID_dereference))
    {
      report.diagnostics.push_back(
        "retained: thread, call, OTHER operation, or indirect write");
      return report;
    }

  std::map<irep_idt, std::size_t> writes;
  for(const auto &ins : program.instructions)
    if(ins.is_assign() && ins.assign_lhs().id() == ID_symbol)
      ++writes[to_symbol_expr(ins.assign_lhs()).get_identifier()];

  // Only a branch-free entry prefix establishes constants and declaration-time
  // VLA extents. Never infer a VLA dimension from a symbol-table initializer.
  environmentt constants;
  std::map<irep_idt, arrayt> arrays;
  std::size_t prefix_end = 0;
  for(; prefix_end < order.size(); ++prefix_end)
  {
    const auto &ins = *order[prefix_end];
    if(
      ins.is_goto() || ins.is_assume() || ins.is_other() ||
      ins.is_end_function())
      break;
    if(ins.is_assign() && ins.assign_lhs().id() == ID_symbol)
    {
      const auto id = to_symbol_expr(ins.assign_lhs()).get_identifier();
      const auto value = evaluate(ins.assign_rhs(), constants);
      if(value && value->lo == value->hi && !memory.addressed_symbols.count(id))
        constants[id] = *value;
      else
        constants.erase(id);
    }
    if(ins.is_decl())
    {
      const auto &symbol = ins.decl_symbol();
      const auto id = symbol.get_identifier();
      constants.erase(id);
      if(
        symbol.type().id() != ID_array || qualified(symbol.type()) ||
        memory.addressed_symbols.count(id))
        continue;
      const auto &type = to_array_type(symbol.type());
      if(!integer_type(type.element_type()))
        continue;
      const auto extent = evaluate(type.size(), constants);
      if(extent && extent->lo == extent->hi && extent->lo > 0)
        arrays.emplace(id, arrayt{symbol, extent->lo});
    }
  }
  for(auto it = constants.begin(); it != constants.end();)
    if(writes[it->first] != 1)
      it = constants.erase(it);
    else
      ++it;

  std::vector<loopt> loops;
  for(std::size_t back = 0; back < order.size(); ++back)
  {
    const auto &jump = *order[back];
    if(!jump.is_goto() || jump.condition() != true || jump.targets.size() != 1)
      continue;
    const auto head = positions.at(&*jump.targets.front());
    if(head == 0 || head >= back)
      continue;
    const auto &header = *order[head];
    if(
      !header.is_goto() || header.targets.size() != 1 ||
      positions.at(&*header.targets.front()) != back + 1)
      continue;
    exprt relation = header.condition();
    bool negated = false;
    if(relation.id() == ID_not && relation.operands().size() == 1)
    {
      relation = relation.operands()[0];
      negated = true;
    }
    // The header branches on exit, so NOT(i <= bound) and i > bound
    // describe the same increasing counted loop.
    irep_idt comparison = relation.id();
    if(!negated)
      comparison = comparison == ID_gt   ? ID_le
                   : comparison == ID_ge ? ID_lt
                                         : irep_idt();
    if(
      (comparison != ID_lt && comparison != ID_le) ||
      relation.operands().size() != 2 ||
      relation.operands()[0].id() != ID_symbol)
      continue;
    const auto &counter_expr = to_symbol_expr(relation.operands()[0]);
    const auto counter = counter_expr.get_identifier();
    if(
      memory.addressed_symbols.count(counter) ||
      !integer_type(counter_expr.type()) || qualified(counter_expr.type()))
      continue;
    std::size_t init = head - 1, step = back - 1;
    while(init > 0 && harmless(*order[init]))
      --init;
    while(step > head && harmless(*order[step]))
      --step;
    if(
      !order[init]->is_assign() || order[init]->assign_lhs() != counter_expr ||
      !order[step]->is_assign() || order[step]->assign_lhs() != counter_expr)
      continue;
    const auto initial = evaluate(order[init]->assign_rhs(), constants);
    const auto threshold = evaluate(relation.operands()[1], constants);
    if(
      !initial || initial->lo != initial->hi || !threshold ||
      threshold->lo != threshold->hi)
      continue;
    const mp_integer last = threshold->hi - (comparison == ID_lt ? 1 : 0);
    if(last < initial->lo)
      continue;
    environmentt body = constants;
    body[counter] = {initial->lo, last};
    const auto delta = affine(order[step]->assign_rhs(), counter, body);
    if(
      !delta || delta->coefficient != 1 || delta->constant != 1 ||
      !in_type({initial->lo, last + 1}, counter_expr.type()))
      continue;
    bool valid = true;
    for(std::size_t i = 0; i < order.size() && valid; ++i)
    {
      const auto &ins = *order[i];
      if(
        i > head && i < back && i != step &&
        ((ins.is_assign() && ins.assign_lhs().id() == ID_symbol &&
          to_symbol_expr(ins.assign_lhs()).get_identifier() == counter) ||
         (ins.is_decl() && ins.decl_symbol().get_identifier() == counter) ||
         (ins.is_dead() && ins.dead_symbol().get_identifier() == counter)))
        valid = false;
      for(const auto &target : ins.targets)
      {
        const auto destination = positions.at(&*target);
        // The initial value is established by `init`, not by a harmless
        // location between that assignment and the header. An outside edge
        // into such a location would bypass the initialization as surely as
        // an outside edge directly to the header.
        if(destination > init && destination <= back && (i < head || i > back))
          valid = false;
        // A jump into the body from the header/earlier iteration would
        // bypass the range-establishing guard.
        if(
          i >= head && i <= back && destination > head && destination <= back &&
          destination <= i)
          valid = false;
      }
    }
    if(valid)
      loops.push_back(
        {init,
         head,
         back,
         step,
         counter,
         counter_expr.type(),
         initial->lo,
         last,
         last + 1,
         last - initial->lo + 1});
  }

  // Earlier certified summaries can occur in a later candidate's use closure.
  // They have already proved that extending their writes to the complete
  // logical index domain is unobservable for every participating array.
  std::set<const instructiont *> certified_whole_operations;
  for(const auto &loop : loops)
  {
    irep_idt root;
    irep_idt source;
    std::vector<affinet> indices;
    std::optional<mp_integer> fill;
    typet fill_type;
    environmentt body = constants;
    body[loop.counter] = {loop.initial, loop.last};
    const auto nondet = independent_nondet_fill(
      loop, order, arrays, body, memory.addressed_symbols, ns);
    if(nondet)
      root = nondet->indices.begin()->first;
    bool valid = true;
    std::string reason;
    for(std::size_t i = loop.head + 1; !nondet && i < loop.back && valid; ++i)
    {
      const auto &ins = *order[i];
      if(i == loop.step || harmless(ins))
        continue;
      if(!ins.is_assign() || ins.assign_lhs().id() != ID_index)
      {
        valid = false;
        reason = "loop body contains a property, branch, or other effect";
        break;
      }
      const auto &lhs = to_index_expr(ins.assign_lhs());
      if(lhs.array().id() != ID_symbol)
      {
        valid = false;
        reason = "array access is not a direct one-dimensional root";
        break;
      }
      const auto id = to_symbol_expr(lhs.array()).get_identifier();
      if(root.empty())
        root = id;
      if(id != root || !arrays.count(root) || !pure_tree(ins.code()))
      {
        valid = false;
        reason = "write does not target one unqualified entry-declared array";
        break;
      }
      const auto index = affine(lhs.index(), loop.counter, body);
      if(!index || ins.assign_rhs().type() != lhs.type())
      {
        valid = false;
        reason = "index wraps, is not affine, or element types differ";
        break;
      }
      const auto &rhs = ins.assign_rhs();
      if(rhs.id() == ID_index)
      {
        const auto &read = to_index_expr(rhs);
        const auto from = read.array().id() == ID_symbol
                            ? to_symbol_expr(read.array()).get_identifier()
                            : irep_idt{};
        const auto read_index = affine(read.index(), loop.counter, body);
        if(
          fill || from.empty() || !arrays.count(from) ||
          (!source.empty() && source != from) ||
          arrays.at(from).symbol.type() != arrays.at(root).symbol.type() ||
          arrays.at(from).length != arrays.at(root).length || !read_index ||
          read_index->coefficient != index->coefficient ||
          read_index->constant != index->constant)
        {
          valid = false;
          reason = "copy requires one equal-typed source and identical indices";
          break;
        }
        source = from;
      }
      else
      {
        const auto value = evaluate(rhs, constants);
        if(
          !source.empty() || !value || value->lo != value->hi ||
          (fill && *fill != value->lo))
        {
          valid = false;
          reason = "value is neither a uniform constant nor a direct copy";
          break;
        }
        fill = value->lo;
        fill_type = lhs.type();
      }
      indices.push_back(*index);
    }
    if(root.empty())
      continue;
    ++report.candidates;
    const auto reject = [&](const std::string &why)
    { report.diagnostics.push_back(id2string(root) + ": retained: " + why); };
    if(!valid || (!nondet && (indices.empty() || (!fill && source.empty()))))
    {
      reject(reason.empty() ? "no constant fill or same-index copy" : reason);
      continue;
    }
    const std::map<irep_idt, std::vector<affinet>> coverage =
      nondet ? nondet->indices
             : std::map<irep_idt, std::vector<affinet>>{{root, indices}};
    for(const auto &entry : coverage)
    {
      const mp_integer tile = entry.second.size();
      std::set<mp_integer> offsets;
      for(const auto &index : entry.second)
      {
        const mp_integer offset =
          index.coefficient * loop.initial + index.constant;
        if(
          index.coefficient != tile || offset < 0 || offset >= tile ||
          !offsets.insert(offset).second)
          valid = false;
      }
      if(tile * loop.trips != arrays.at(entry.first).length)
        valid = false;
    }
    if(!valid)
    {
      reject("affine tiles do not cover exactly the declared legal extent");
      continue;
    }

    // Whole-array fill/copy also updates the backing index domain outside the
    // C extent. Certify the complete use closure of BOTH copy operands. This
    // also rules out aliases and cross-element feedback through another view.
    std::set<irep_idt> participants{root};
    for(const auto &entry : coverage)
      participants.insert(entry.first);
    if(!source.empty())
      participants.insert(source);
    for(const auto &participant : participants)
      for(std::size_t position = 0; position < order.size() && valid;
          ++position)
      {
        const auto &ins = *order[position];
        if(
          certified_whole_operations.count(&ins) ||
          (ins.is_decl() &&
           ins.decl_symbol().get_identifier() == participant) ||
          (ins.is_dead() && ins.dead_symbol().get_identifier() == participant))
          continue;
        environmentt at = constants;
        for(const auto &bounded : loops)
          if(position > bounded.head && position <= bounded.step)
            at[bounded.counter] = {bounded.initial, bounded.last};
        const auto check = [&](const auto &self, const exprt &expr) -> bool
        {
          if(!contains(expr, participant))
            return true;
          if(
            !pure_tree(expr) || expr.id() == ID_address_of ||
            expr.id() == ID_byte_extract_little_endian ||
            expr.id() == ID_byte_extract_big_endian ||
            expr.id() == ID_byte_update_little_endian ||
            expr.id() == ID_byte_update_big_endian)
            return false;
          if(expr.id() == ID_index)
          {
            const auto &index = to_index_expr(expr);
            if(
              index.array().id() == ID_symbol &&
              to_symbol_expr(index.array()).get_identifier() == participant)
            {
              const auto bounds = evaluate(index.index(), at);
              return bounds && bounds->lo >= 0 &&
                     bounds->hi < arrays.at(participant).length &&
                     !contains(index.index(), participant);
            }
          }
          if(
            expr.id() == ID_symbol &&
            to_symbol_expr(expr).get_identifier() == participant)
            return false;
          return std::all_of(
            expr.operands().begin(),
            expr.operands().end(),
            [&](const exprt &operand) { return self(self, operand); });
        };
        valid = check(check, ins.code()) &&
                (!ins.has_condition() || check(check, ins.condition()));
      }
    if(!valid)
    {
      reject("complete array use closure is not proven direct and in bounds");
      continue;
    }

    const auto &array = arrays.at(root);
    auto location = order[loop.head]->source_location();
    if(!btor2_original_event_ids(location).empty())
    {
      for(std::size_t i = loop.head; i <= loop.back; ++i)
        btor2_merge_event_origins(location, order[i]->source_location());
      location.set("c2btor_summary_kind", nondet ? "array-nondet" : source.empty() ? "array-fill" : "array-copy");
      location.set("c2btor_summary_id", nondet
        ? "array-nondet-" + std::to_string(report.nondet_summaries.size())
        : "array-summary-" + std::to_string(report.summarized));
    }
    for(std::size_t i = loop.head + 1; i <= loop.back; ++i)
      if(i != loop.step)
        order[i]->turn_into_skip();
    if(nondet)
    {
      const auto group_id =
        "array-nondet-" + std::to_string(report.nondet_summaries.size());
      report.nondet_summaries.push_back(
        {group_id, loop.initial, loop.trips, nondet->calls, location});
      bool first = true;
      for(const auto &entry : coverage)
      {
        const auto &target = arrays.at(entry.first).symbol;
        const auto position =
          first ? loop.head : nondet->stores.at(entry.first);
        auto summary_location = location;
        summary_location.set("c2btor_nondet_summary_group", group_id);
        summary_location.set("c2btor_nondet_summary_array", entry.first);
        *order[position] = goto_programt::make_assignment(
          target,
          side_effect_expr_nondett(target.type(), summary_location),
          summary_location);
        certified_whole_operations.insert(&*order[position]);
        first = false;
      }
    }
    else
    {
      code_assignt replacement(
        array.symbol,
        source.empty() ? exprt(array_of_exprt(
                           from_integer(*fill, fill_type),
                           to_array_type(array.symbol.type())))
                       : exprt(arrays.at(source).symbol));
      // Only this pass introduces storage-wide copies. The logical backend
      // requires its equal-extent, closed-use certificate.
      if(!source.empty())
        replacement.set("c2btor_certified_array_copy", true);
      *order[loop.head] = goto_programt::make_assignment(replacement, location);
      certified_whole_operations.insert(&*order[loop.head]);
    }
    *order[loop.step] = goto_programt::make_assignment(
      code_assignt(
        symbol_exprt(loop.counter, loop.counter_type),
        from_integer(loop.final, loop.counter_type)),
      location);
    ++report.summarized;
    if(nondet)
      ++report.nondet_initializations;
    else if(source.empty())
      ++report.fills;
    else
      ++report.copies;
    report.certified_arrays.insert(participants.begin(), participants.end());
    if(nondet)
      for(const auto &entry : coverage)
        report.diagnostics.push_back(
          id2string(entry.first) +
          ": summarized independent nondet initialization " +
          integer2string(loop.trips) + " iterations, " +
          integer2string(arrays.at(entry.first).length) + " elements");
    else
      report.diagnostics.push_back(
        id2string(root) +
        (source.empty() ? ": summarized fill "
                        : ": summarized copy from " + id2string(source) + " ") +
        integer2string(loop.trips) + " iterations, " +
        integer2string(array.length) + " elements");
  }
  if(report.summarized)
  {
    remove_skip(program);
    program.update();
  }
  return report;
}
