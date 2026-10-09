#include "simplify_callback_targets.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unreachable.h>

#include <deque>
#include <map>
#include <unordered_map>


namespace
{
using factst = std::map<exprt, exprt>;

bool same_object_type(typet lhs, typet rhs)
{
  lhs.remove(ID_C_constant);
  rhs.remove(ID_C_constant);
  return lhs == rhs;
}

// Values never contain reads of mutable storage: only literals and addresses.
// Keeping addresses symbolic is essential when the addressed object's value changes.
bool is_value(const exprt &e)
{
  if(e.is_constant())
    return true;
  if(e.id() == ID_address_of)
  {
    const exprt *object = &to_address_of_expr(e).object();
    while(object->id() == ID_member || object->id() == ID_index)
    {
      if(
        object->id() == ID_index &&
        !to_index_expr(*object).index().is_constant())
        return false;
      object = &object->operands()[0];
    }
    return object->id() == ID_symbol;
  }
  if(
    e.id() != ID_typecast && e.id() != ID_struct && e.id() != ID_array &&
    e.id() != ID_array_of)
    return false;
  for(const auto &op : e.operands())
    if(!is_value(op))
      return false;
  return true;
}

const exprt &root_object(const exprt &e)
{
  if(e.id() == ID_member || e.id() == ID_index)
    return root_object(e.operands()[0]);
  return e;
}

bool is_subobject(const exprt &object, const exprt &base)
{
  return object == base ||
         ((object.id() == ID_member || object.id() == ID_index) &&
          is_subobject(object.operands()[0], base));
}

class evaluatort
{
  const namespacet &ns;
  const factst &facts;

public:
  evaluatort(const namespacet &ns, const factst &facts) : ns(ns), facts(facts)
  {
  }

  exprt lvalue(const exprt &e, unsigned depth = 0) const
  {
    if(depth > 32)
      return e;
    if(e.id() == ID_dereference)
    {
      exprt pointer = value(to_dereference_expr(e).pointer(), depth + 1);
      while(pointer.id() == ID_typecast &&
            pointer.operands()[0].type().id() == ID_pointer &&
            same_object_type(
              to_pointer_type(pointer.type()).base_type(),
              to_pointer_type(pointer.operands()[0].type()).base_type()))
        pointer = pointer.operands()[0];
      // Do not guess through casts that reinterpret the pointed-to object.
      if(pointer.id() == ID_address_of)
      {
        const auto &object = to_address_of_expr(pointer).object();
        if(same_object_type(object.type(), e.type()))
          return lvalue(object, depth + 1);
      }
      if(pointer.id() == ID_plus)
      {
        auto object = simplify_expr(dereference_exprt(pointer, e.type()), ns);
        if(object.id() == ID_index && same_object_type(object.type(), e.type()))
          return lvalue(object, depth + 1);
      }
      return dereference_exprt(pointer, e.type());
    }
    exprt result = e;
    if(e.id() == ID_member || e.id() == ID_index)
    {
      result.operands()[0] = lvalue(e.operands()[0], depth + 1);
      if(e.id() == ID_index)
      {
        result.operands()[1] = value(e.operands()[1], depth + 1);
        mp_integer index;
        if(
          result.operands()[1].is_constant() &&
          !to_integer(to_constant_expr(result.operands()[1]), index))
          result.operands()[1] = from_integer(index, c_index_type());
      }
    }
    return result;
  }

  exprt value(const exprt &e, unsigned depth = 0) const
  {
    if(depth > 32 || e.type().get_bool(ID_C_volatile))
      return e;
    if(e.id() == ID_address_of)
      return address_of_exprt(
        lvalue(to_address_of_expr(e).object(), depth + 1));
    if(e.id() == ID_side_effect)
      return e;

    exprt result = e;
    if(
      e.id() == ID_symbol || e.id() == ID_member || e.id() == ID_index ||
      e.id() == ID_dereference)
    {
      result = lvalue(e, depth + 1);
      auto it = facts.find(result);
      if(it != facts.end())
        return it->second;
      if(result.id() == ID_symbol)
      {
        const auto &symbol = ns.lookup(to_symbol_expr(result));
        if(
          symbol.is_static_lifetime && symbol.type.get_bool(ID_C_constant) &&
          !symbol.type.get_bool(ID_C_volatile) && is_value(symbol.value))
          return symbol.value;
        return result;
      }
      if(result.id() == ID_dereference)
        return result;
    }
    for(auto &op : result.operands())
      op = value(op, depth + 1);
    return simplify_expr(result, ns);
  }
};

// Record scalar leaves so updating one field does not leave a stale aggregate
// value, or erase facts about disjoint fields. Large/unknown arrays are omitted.
void record(
  const exprt &lhs,
  const exprt &rhs,
  factst &facts,
  const namespacet &ns)
{
  if(lhs.type().get_bool(ID_C_volatile))
    return;
  if(rhs.id() == ID_struct)
  {
    const auto &type = rhs.type().id() == ID_struct_tag
                         ? ns.follow_tag(to_struct_tag_type(rhs.type()))
                         : to_struct_type(rhs.type());
    for(std::size_t i = 0; i < type.components().size(); ++i)
    {
      const auto &component = type.components()[i];
      record(
        member_exprt(lhs, component.get_name(), component.type()),
        rhs.operands()[i],
        facts,
        ns);
    }
  }
  else if(rhs.id() == ID_array && rhs.operands().size() <= 256)
  {
    for(std::size_t i = 0; i < rhs.operands().size(); ++i)
      record(
        index_exprt(lhs, from_integer(i, c_index_type())),
        rhs.operands()[i],
        facts,
        ns);
  }
  else if(
    is_value(rhs) && rhs.type().id() != ID_array && rhs.type().id() != ID_union)
    facts[lhs] = rhs;
}

void transfer(
  const goto_programt::instructiont &instruction,
  factst &facts,
  const namespacet &ns)
{
  if(instruction.is_assign())
  {
    evaluatort evaluate(ns, facts);
    const exprt rhs = evaluate.value(instruction.assign_rhs());
    const exprt lhs = evaluate.lvalue(instruction.assign_lhs());
    const exprt &root = root_object(lhs);
    if(root.id() != ID_symbol)
    {
      facts.clear(); // Store through an unresolved alias may change any fact.
      return;
    }
    bool uncertain_subobject = false;
    for(const exprt *p = &lhs; p->id() == ID_member || p->id() == ID_index;
        p = &p->operands()[0])
    {
      if(p->id() == ID_index && !to_index_expr(*p).index().is_constant())
        uncertain_subobject = true;
      if(
        p->operands()[0].type().id() == ID_union ||
        p->operands()[0].type().id() == ID_union_tag)
        uncertain_subobject = true;
    }
    const exprt &invalidated = uncertain_subobject ? root : lhs;
    for(auto it = facts.begin(); it != facts.end();)
      if(
        is_subobject(it->first, invalidated) ||
        is_subobject(invalidated, it->first))
        it = facts.erase(it);
      else
        ++it;
    if(!uncertain_subobject)
      record(lhs, rhs, facts, ns);
  }
  else if(instruction.is_decl() || instruction.is_dead())
  {
    const auto &symbol = instruction.is_decl() ? instruction.decl_symbol()
                                               : instruction.dead_symbol();
    for(auto it = facts.begin(); it != facts.end();)
      if(root_object(it->first) == symbol)
        it = facts.erase(it);
      else
        ++it;
  }
  else if(instruction.is_function_call() || instruction.is_other())
  {
    // The preserved pure dereference of an indirect call has no write effects.
    // Every other unmodelled operation, including memory intrinsics, is a barrier.
    if(!(instruction.is_other() &&
         instruction.code().get_statement() == ID_expression &&
         instruction.code().operands().size() == 1 &&
         instruction.code().operands()[0].id() == ID_dereference &&
         instruction.code().operands()[0].type().id() == ID_code))
      facts.clear();
  }
}
} // namespace

void simplify_callback_targets(
  goto_programt &program,
  const symbol_tablet &symbols,
  messaget &log,
  std::vector<source_locationt> *unreachable_assertions)
{
  if(program.instructions.empty())
    return;
  // This is a sequential must-value analysis. Do not use it on concurrent code.
  for(const auto &instruction : program.instructions)
    if(instruction.is_start_thread() || instruction.is_end_thread())
      return;
  const namespacet ns(symbols);
  using targett = goto_programt::targett;
  std::unordered_map<const goto_programt::instructiont *, factst> states;
  std::deque<targett> work;
  auto entry = program.instructions.begin();
  states.emplace(&*entry, factst{});
  work.push_back(entry);
  while(!work.empty())
  {
    const auto current = work.front();
    work.pop_front();
    factst after = states.at(&*current);
    exprt condition = true_exprt();
    if(current->is_goto() || current->is_assume())
      condition = evaluatort(ns, after).value(current->condition());
    transfer(*current, after, ns);
    auto successors = program.get_successors(current);
    if(current->is_goto())
    {
      successors.clear();
      if(!condition.is_false())
        successors.insert(
          successors.end(), current->targets.begin(), current->targets.end());
      if(
        !condition.is_true() &&
        std::next(current) != program.instructions.end())
        successors.push_back(std::next(current));
    }
    if(current->is_assume() && condition.is_false())
      successors.clear();
    for(const auto successor : successors)
    {
      auto inserted = states.emplace(&*successor, after);
      bool changed = inserted.second;
      if(!changed)
      {
        auto &joined = inserted.first->second;
        for(auto it = joined.begin(); it != joined.end();)
        {
          const auto incoming = after.find(it->first);
          if(incoming == after.end() || incoming->second != it->second)
          {
            it = joined.erase(it);
            changed = true;
          }
          else
            ++it;
        }
      }
      if(changed)
        work.push_back(successor);
    }
  }
  std::size_t folded = 0;
  for(auto &instruction : program.instructions)
  {
    auto state = states.find(&instruction);
    if(state == states.end() || !instruction.is_goto())
      continue;
    auto guard = evaluatort(ns, state->second).value(instruction.condition());
    if(
      (guard.is_true() || guard.is_false()) && guard != instruction.condition())
    {
      instruction.condition_nonconst() = guard;
      ++folded;
    }
  }
  if(folded != 0)
  {
    // get_successors includes the target even for a false GOTO. Remove those
    // edges before computing reachability, or their dead callback bodies remain.
    remove_skip(program);
    std::vector<std::pair<targett, source_locationt>> assertions;
    if(unreachable_assertions != nullptr)
      for(auto it = program.instructions.begin();
          it != program.instructions.end(); ++it)
      {
        bool is_error_call = false;
        if(it->is_function_call() && it->call_function().id() == ID_symbol)
        {
          const auto callee =
            id2string(to_symbol_expr(it->call_function()).get_identifier());
          is_error_call = callee.find("__assert_fail") != std::string::npos ||
                          callee.find("reach_error") != std::string::npos;
        }
        if(it->is_assert() || is_error_call)
          assertions.emplace_back(it, it->source_location());
      }
    remove_unreachable(program);
    if(unreachable_assertions != nullptr)
      for(const auto &assertion : assertions)
        if(assertion.first->is_skip())
          unreachable_assertions->push_back(assertion.second);
    remove_skip(program);
    program.update();
    log.status() << "Simplified " << folded
                 << " constant guards before BTOR2 conversion" << messaget::eom;
  }
}
