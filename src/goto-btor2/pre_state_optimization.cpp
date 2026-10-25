// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "pre_state_optimization.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/remove_skip.h>

#include "btor2_type_utils.h"
#include "memory_access.h"

#include <deque>
#include <map>
#include <unordered_map>

namespace
{
using symbol_sett = std::set<irep_idt>;
using factst = std::map<irep_idt, exprt>;

bool qualified(const typet &type)
{
  return type.get_bool(ID_C_volatile) || type.get_bool(ID_C_atomic);
}

bool integer(const typet &type)
{
  return type.id() == ID_bool || type.id() == ID_c_bool ||
         type.id() == ID_signedbv || type.id() == ID_unsignedbv;
}

bool aggregate(const typet &type)
{
  return type.id() == ID_array || type.id() == ID_struct ||
         type.id() == ID_union;
}

bool qualified_storage_type(const typet &raw, const namespacet &ns)
{
  const auto type = follow_tag_type(raw, ns);
  if(qualified(raw) || qualified(type))
    return true;
  if(type.id() == ID_array)
    return qualified_storage_type(to_array_type(type).element_type(), ns);
  if(type.id() == ID_struct || type.id() == ID_union)
    for(const auto &field : to_struct_union_type(type).components())
      if(qualified_storage_type(field.type(), ns))
        return true;
  return false;
}

void add_symbols(const exprt &expr, symbol_sett &dest)
{
  const auto ids = find_symbol_identifiers(expr);
  dest.insert(ids.begin(), ids.end());
}

// sizeof and VLA expressions can be hidden in types rather than operands.
void add_type_dependencies(
  const typet &type,
  const namespacet &ns,
  symbol_sett &roots,
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
  const exprt &expr,
  const namespacet &ns,
  symbol_sett &roots,
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

const exprt &root_object(const exprt &expr)
{
  if(expr.id() == ID_member || expr.id() == ID_index)
    return root_object(expr.operands()[0]);
  return expr;
}

bool scalar_symbol(const exprt &expr, const namespacet &ns)
{
  if(expr.id() != ID_symbol || qualified(expr.type()))
    return false;
  const symbolt *symbol = nullptr;
  if(
    ns.lookup(to_symbol_expr(expr).get_identifier(), symbol) || !symbol ||
    symbol->is_type || qualified(symbol->type))
    return false;
  const auto type = follow_tag_type(symbol->type, ns);
  return !qualified(type) && integer(type);
}

bool literal_initializer(const exprt &expr)
{
  if(expr.is_constant())
    return true;
  if(
    expr.id() != ID_struct && expr.id() != ID_array &&
    expr.id() != ID_array_of && expr.id() != ID_typecast)
    return false;
  for(const auto &operand : expr.operands())
    if(!literal_initializer(operand))
      return false;
  return true;
}

// A whitelist deliberately excludes memory queries, pointer arithmetic,
// floating point and unrecognised/side-effecting operations.
// Dead unsupported operations must still reach the normal converter checks.
bool pure_expression(const exprt &expr, const namespacet &ns)
{
  const auto type = follow_tag_type(expr.type(), ns);
  if(qualified_storage_type(expr.type(), ns))
    return false;
  if(expr.id() == ID_symbol)
  {
    const symbolt *symbol = nullptr;
    if(
      ns.lookup(to_symbol_expr(expr).get_identifier(), symbol) || !symbol ||
      symbol->is_type || qualified_storage_type(symbol->type, ns))
      return false;
    // Such an initializer is evaluated implicitly by the converter. Do not
    // erase its last code reference, including references to aggregate data.
    if(
      symbol->is_static_lifetime && symbol->value.is_not_nil() &&
      !literal_initializer(symbol->value))
      return false;
    return integer(type) || aggregate(type);
  }
  if(expr.id() == ID_constant)
    return integer(type) || (type.id() == ID_pointer &&
                             to_constant_expr(expr).is_null_pointer());
  if(expr.id() == ID_side_effect)
    return expr.get(ID_statement) == ID_nondet && integer(type) &&
           expr.operands().empty();
  if(expr.id() == ID_member)
  {
    if(
      expr.operands().size() != 1 ||
      !aggregate(follow_tag_type(expr.operands()[0].type(), ns)))
      return false;
  }
  else if(expr.id() == ID_index)
  {
    if(
      expr.operands().size() != 2 ||
      follow_tag_type(expr.operands()[0].type(), ns).id() != ID_array ||
      !integer(follow_tag_type(expr.operands()[1].type(), ns)))
      return false;
  }
  else if(
    expr.id() == ID_struct || expr.id() == ID_array || expr.id() == ID_array_of)
  {
    if(!aggregate(type))
      return false;
  }
  else if(expr.id() == ID_if)
  {
    if(
      expr.operands().size() != 3 || !integer(type) ||
      !integer(follow_tag_type(expr.operands()[0].type(), ns)))
      return false;
  }
  else
  {
    static const symbol_sett operators{
      ID_typecast, ID_plus,  ID_minus,  ID_unary_minus, ID_mult,
      ID_div,      ID_mod,   ID_shl,    ID_lshr,        ID_ashr,
      ID_bitand,   ID_bitor, ID_bitxor, ID_bitnot,      ID_equal,
      ID_notequal, ID_lt,    ID_le,     ID_gt,          ID_ge,
      ID_and,      ID_or,    ID_xor,    ID_not,         ID_implies};
    if(!integer(type) || !operators.count(expr.id()))
      return false;
    static const symbol_sett unary{
      ID_typecast, ID_unary_minus, ID_bitnot, ID_not};
    static const symbol_sett binary{
      ID_minus,
      ID_div,
      ID_mod,
      ID_shl,
      ID_lshr,
      ID_ashr,
      ID_equal,
      ID_notequal,
      ID_lt,
      ID_le,
      ID_gt,
      ID_ge,
      ID_implies};
    const auto arity = expr.operands().size();
    if(
      unary.count(expr.id())    ? arity != 1
      : binary.count(expr.id()) ? arity != 2
                                : arity < 2)
      return false;
    for(const auto &operand : expr.operands())
      if(!integer(follow_tag_type(operand.type(), ns)))
        return false;
  }
  for(const auto &operand : expr.operands())
    if(!pure_expression(operand, ns))
      return false;
  return true;
}

bool type_has_side_effect(const irept &irep)
{
  if(irep.id() == ID_side_effect)
    return true;
  for(const auto &sub : irep.get_sub())
    if(type_has_side_effect(sub))
      return true;
  for(const auto &named : irep.get_named_sub())
    if(type_has_side_effect(named.second))
      return true;
  return false;
}

bool division_or_shift(const exprt &expr)
{
  return expr.id() == ID_div || expr.id() == ID_mod || expr.id() == ID_shl ||
         expr.id() == ID_lshr || expr.id() == ID_ashr;
}

bool contains_unsimplified_arithmetic(const exprt &expr)
{
  // CBMC's algebraic 0/x rewrite need not preserve the encoder's division by
  // zero totalization. Nor may equal-looking nondet expressions be correlated.
  if(division_or_shift(expr) || expr.id() == ID_side_effect)
    return true;
  for(const auto &operand : expr.operands())
    if(contains_unsimplified_arithmetic(operand))
      return true;
  return false;
}

exprt evaluate_constant_binary(exprt expr, const namespacet &ns)
{
  const auto type = follow_tag_type(expr.type(), ns);
  if(type.id() != ID_signedbv && type.id() != ID_unsignedbv)
    return expr;
  // Match convert_binary(): both operands are first converted to the result
  // width. Shift distance bits are then unsigned, regardless of signed type.
  for(auto &operand : expr.operands())
  {
    if(!operand.is_constant())
      return expr;
    operand =
      simplify_expr(typecast_exprt::conditional_cast(operand, type), ns);
  }
  const auto lhs = numeric_cast<mp_integer>(expr.operands()[0]);
  const auto rhs = numeric_cast<mp_integer>(expr.operands()[1]);
  if(!lhs.has_value() || !rhs.has_value())
    return expr;
  if(expr.id() == ID_div || expr.id() == ID_mod)
  {
    if(*rhs == 0)
      return expr;
    return from_integer(
      expr.id() == ID_div ? *lhs / *rhs : *lhs % *rhs, expr.type());
  }
  const auto width = to_bitvector_type(type).get_width();
  const unsignedbv_typet unsigned_type(width);
  const auto distance = numeric_cast<mp_integer>(simplify_expr(
    typecast_exprt::conditional_cast(expr.operands()[1], unsigned_type), ns));
  const typet source_type =
    expr.id() == ID_ashr ? typet(signedbv_typet(width)) : typet(unsigned_type);
  const auto value = numeric_cast<mp_integer>(simplify_expr(
    typecast_exprt::conditional_cast(expr.operands()[0], source_type), ns));
  if(!distance.has_value() || !value.has_value())
    return expr;
  if(*distance >= width)
    return from_integer(
      expr.id() == ID_ashr && *value < 0 ? -1 : 0, expr.type());
  return from_integer(
    expr.id() == ID_shl ? *value << *distance : *value >> *distance,
    expr.type());
}

exprt evaluate(const exprt &expr, const factst &facts, const namespacet &ns)
{
  // Only scalar integer expressions are constant propagated. In particular,
  // replacing an address operand with the value of its object is forbidden.
  if(!integer(follow_tag_type(expr.type(), ns)) || !pure_expression(expr, ns))
    return expr;
  if(expr.id() == ID_side_effect)
    return expr;
  if(expr.id() == ID_symbol)
  {
    const auto found = facts.find(to_symbol_expr(expr).get_identifier());
    if(found == facts.end())
      return expr;
    // The declared target type governs both arithmetic wrap and truncation.
    return found->second.type() == expr.type()
             ? found->second
             : simplify_expr(typecast_exprt(found->second, expr.type()), ns);
  }
  if(expr.id() == ID_member || expr.id() == ID_index)
    return expr;
  exprt result = expr;
  for(auto &operand : result.operands())
    operand = evaluate(operand, facts, ns);
  if(division_or_shift(result))
    return evaluate_constant_binary(std::move(result), ns);
  if(contains_unsimplified_arithmetic(result))
    return result;
  return simplify_expr(result, ns);
}

void transfer(
  const goto_programt::instructiont &ins,
  factst &facts,
  const namespacet &ns)
{
  if(ins.is_assign())
  {
    const auto &lhs = ins.assign_lhs();
    const auto rhs = evaluate(ins.assign_rhs(), facts, ns);
    const auto &root = root_object(lhs);
    bool known_lvalue = root.id() == ID_symbol && !qualified(lhs.type());
    for(const exprt *view = &lhs; view != &root; view = &view->operands()[0])
      known_lvalue &=
        !qualified(view->type()) &&
        (view->id() != ID_index ||
         (follow_tag_type(view->operands()[0].type(), ns).id() == ID_array &&
          pure_expression(to_index_expr(*view).index(), ns)));
    if(!known_lvalue || !pure_expression(ins.assign_rhs(), ns))
    {
      facts.clear();
      return;
    }
    const auto id = to_symbol_expr(root).get_identifier();
    facts.erase(id);
    if(
      scalar_symbol(lhs, ns) && rhs.is_constant() &&
      integer(follow_tag_type(rhs.type(), ns)))
    {
      auto value = rhs.type() == lhs.type()
                     ? rhs
                     : simplify_expr(typecast_exprt(rhs, lhs.type()), ns);
      if(value.is_constant())
        facts.emplace(id, std::move(value));
    }
  }
  else if(ins.is_decl() || ins.is_dead())
  {
    const auto &symbol = ins.is_decl() ? ins.decl_symbol() : ins.dead_symbol();
    if(ins.is_decl() && type_has_side_effect(symbol.type()))
      facts.clear();
    else
      facts.erase(symbol.get_identifier());
  }
  else if(ins.is_function_call() || ins.is_other() || ins.is_set_return_value())
    facts.clear();
  else if(ins.has_condition() && !pure_expression(ins.condition(), ns))
    facts.clear();
  // ASSERT is an observation, never a premise for constant propagation.
}

bool can_optimize(const goto_programt &program)
{
  for(const auto &ins : program.instructions)
    if(
      ins.is_start_thread() || ins.is_end_thread() ||
      (ins.is_goto() && ins.targets.size() != 1) ||
      (ins.is_other() && (ins.get_other().is_nil() ||
                          ins.get_other().get_statement() == ID_skip)))
      return false;
  return true;
}

bool pointer_bookkeeping_initialization(
  const goto_programt::instructiont &ins,
  const namespacet &ns)
{
  const exprt *object = nullptr;
  if(ins.is_assign() && ins.assign_lhs().id() == ID_symbol)
    object = &ins.assign_lhs();
  else if(ins.is_decl())
    object = &ins.decl_symbol();
  else if(ins.is_dead())
    object = &ins.dead_symbol();
  if(!object)
    return false;
  static const symbol_sett bookkeeping{
    "__CPROVER_deallocated",
    "__CPROVER_dead_object",
    "__CPROVER_malloc_object",
    "__CPROVER_memory_leak"};
  const auto &id = to_symbol_expr(*object).get_identifier();
  const symbolt *symbol = nullptr;
  if(
    !bookkeeping.count(id) || ns.lookup(id, symbol) || !symbol ||
    is_c_source_object(*symbol, ns) || object->type().id() != ID_pointer)
    return false;
  if(!ins.is_assign())
    return true;
  const auto &rhs = ins.assign_rhs();
  if(rhs.is_constant() && rhs.type().id() == ID_pointer)
    return to_constant_expr(rhs).is_null_pointer();
  if(rhs.id() == ID_typecast && rhs.type().id() == ID_pointer)
  {
    const auto &operand = to_typecast_expr(rhs).op();
    const auto value = numeric_cast<mp_integer>(operand);
    return integer(operand.type()) && value.has_value() && *value == 0;
  }
  return false;
}

bool pointer_identity_sensitive(
  const goto_programt &program,
  const namespacet &ns)
{
  symbol_sett symbols, tags;
  // Scan types as well as expression operands: an aggregate may contain a
  // pointer without having a pointer-typed operand at any particular use.
  const auto scan = [&](const auto &self, const irept &node) -> bool
  {
    if(
      node.id() == ID_pointer || node.id() == ID_string_constant ||
      node.id() == ID_address_of || node.id() == ID_pointer_object ||
      node.id() == ID_pointer_offset || node.id() == ID_object_size ||
      (node.id() == ID_side_effect && node.get(ID_statement) == ID_allocate))
      return true;
    if(node.id() == ID_symbol)
    {
      const auto &id = node.get(ID_identifier);
      const symbolt *symbol = nullptr;
      if(
        symbols.insert(id).second && !ns.lookup(id, symbol) && symbol &&
        (self(self, symbol->type) ||
         (symbol->is_static_lifetime && symbol->value.is_not_nil() &&
          self(self, symbol->value))))
        return true;
    }
    if(node.id() == ID_struct_tag || node.id() == ID_union_tag)
    {
      const auto &id = node.get(ID_identifier);
      const symbolt *symbol = nullptr;
      if(
        tags.insert(id).second && !ns.lookup(id, symbol) && symbol &&
        self(self, symbol->type))
        return true;
    }
    for(const auto &sub : node.get_sub())
      if(self(self, sub))
        return true;
    for(const auto &named : node.get_named_sub())
      if(self(self, named.second))
        return true;
    return false;
  };
  for(const auto &ins : program.instructions)
  {
    // CBMC's unused global NULL bookkeeping does not reserve a memory root.
    // Every other observation/write of these pointers is scanned normally.
    if(pointer_bookkeeping_initialization(ins, ns))
      continue;
    if(
      scan(scan, ins.code()) ||
      (ins.has_condition() && scan(scan, ins.condition())))
      return true;
  }
  return false;
}

void propagate_constants(
  goto_programt &program,
  const namespacet &ns,
  pre_state_optimization_reportt &report)
{
  using targett = goto_programt::targett;
  std::unordered_map<const goto_programt::instructiont *, factst> states;
  std::deque<targett> pending;
  auto entry = program.instructions.begin();
  states.emplace(&*entry, factst{});
  pending.push_back(entry);
  while(!pending.empty())
  {
    const auto current = pending.front();
    pending.pop_front();
    auto after = states.at(&*current);
    const auto guard = current->is_goto() || current->is_assume()
                         ? evaluate(current->condition(), after, ns)
                         : true_exprt();
    transfer(*current, after, ns);
    auto successors = program.get_successors(current);
    if(current->is_goto())
    {
      successors.clear();
      if(!guard.is_false())
        successors.insert(
          successors.end(), current->targets.begin(), current->targets.end());
      if(!guard.is_true() && std::next(current) != program.instructions.end())
        successors.push_back(std::next(current));
    }
    if(current->is_assume() && guard.is_false())
      successors.clear();
    for(const auto successor : successors)
    {
      if(successor == program.instructions.end())
        continue;
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
        pending.push_back(successor);
    }
  }
  for(auto &ins : program.instructions)
  {
    const auto state = states.find(&ins);
    if(state == states.end())
    {
      if(ins.is_end_function())
        continue;
      if(ins.is_assert())
        report.unreachable_assertions.push_back(ins.source_location());
      ins.turn_into_skip();
      ++report.unreachable_instructions;
      continue;
    }
    if(ins.is_assign())
    {
      auto rhs = evaluate(ins.assign_rhs(), state->second, ns);
      if(rhs != ins.assign_rhs())
      {
        ins.assign_rhs_nonconst() = std::move(rhs);
        ++report.constants_replaced;
      }
    }
    if(ins.has_condition())
    {
      auto condition = evaluate(ins.condition(), state->second, ns);
      if(condition != ins.condition())
      {
        if(
          (ins.is_goto() || ins.is_assume()) &&
          (condition.is_true() || condition.is_false()))
          ++report.folded_guards;
        ins.condition_nonconst() = std::move(condition);
        ++report.constants_replaced;
      }
    }
  }
  remove_skip(program);
  program.update();
}

bool removable_lvalue(
  const exprt &lhs,
  const namespacet &ns,
  const pre_state_memory_symbolst &memory)
{
  const auto &root = root_object(lhs);
  if(root.id() != ID_symbol || !pure_expression(root, ns))
    return false;
  const auto &id = to_symbol_expr(root).get_identifier();
  if(memory.addressed_symbols.count(id))
    return false;
  const symbolt *symbol = nullptr;
  if(
    ns.lookup(id, symbol) || !symbol ||
    (memory.arbitrary_pointer_input && is_c_source_object(*symbol, ns)) ||
    type_has_side_effect(symbol->type))
    return false;
  for(const exprt *view = &lhs; view != &root; view = &view->operands()[0])
  {
    if(qualified(view->type()))
      return false;
    if(
      view->id() == ID_index &&
      (follow_tag_type(view->operands()[0].type(), ns).id() != ID_array ||
       !pure_expression(to_index_expr(*view).index(), ns)))
      return false;
  }
  return true;
}

void project_storage(
  goto_programt &program,
  const namespacet &ns,
  const pre_state_memory_symbolst &memory,
  pre_state_optimization_reportt &report)
{
  symbol_sett roots = memory.addressed_symbols, all, visited;
  std::map<irep_idt, symbol_sett> dependencies;
  std::set<const goto_programt::instructiont *> candidates;
  for(const auto &ins : program.instructions)
  {
    add_symbols(ins.code(), all);
    if(ins.source_location().get_bool("c2btor_witness_value_root"))
      add_symbols(ins.code(), roots);
    add_expression_types(ins.code(), ns, roots, visited);
    if(ins.has_condition())
    {
      add_symbols(ins.condition(), all);
      add_symbols(ins.condition(), roots);
      add_expression_types(ins.condition(), ns, roots, visited);
    }
    if(
      ins.is_assign() && removable_lvalue(ins.assign_lhs(), ns, memory) &&
      pure_expression(ins.assign_rhs(), ns))
    {
      candidates.insert(&ins);
      const auto &id =
        to_symbol_expr(root_object(ins.assign_lhs())).get_identifier();
      auto &used = dependencies[id];
      add_symbols(ins.assign_rhs(), used);
      // Indices compute the location written, and matter if this write is kept.
      for(const exprt *view = &ins.assign_lhs();
          view->id() == ID_member || view->id() == ID_index;
          view = &view->operands()[0])
        if(view->id() == ID_index)
          add_symbols(to_index_expr(*view).index(), used);
    }
    else if(ins.is_decl() && removable_lvalue(ins.decl_symbol(), ns, memory))
      ;
    else if(ins.is_dead() && removable_lvalue(ins.dead_symbol(), ns, memory))
      ;
    else
      // Unknown calls, alias writes and custom memory events stay intact.
      add_symbols(ins.code(), roots);
  }
  all.insert(roots.begin(), roots.end());
  symbol_sett examined;
  for(bool changed = true; changed;)
  {
    changed = false;
    symbol_sett discovered;
    for(const auto &id : all)
    {
      const symbolt *symbol = nullptr;
      if(!examined.insert(id).second || ns.lookup(id, symbol) || !symbol)
        continue;
      add_type_dependencies(symbol->type, ns, roots, visited);
      if(memory.arbitrary_pointer_input && is_c_source_object(*symbol, ns))
        roots.insert(id);
      if(symbol->is_static_lifetime && symbol->value.is_not_nil())
      {
        add_symbols(symbol->value, roots);
        add_symbols(symbol->value, discovered);
        add_expression_types(symbol->value, ns, roots, visited);
        if(
          !literal_initializer(symbol->value) ||
          !pure_expression(symbol->value, ns))
        {
          roots.insert(id);
          report.forced_static_symbols.insert(id);
        }
      }
    }
    discovered.insert(roots.begin(), roots.end());
    for(const auto &id : discovered)
      changed |= all.insert(id).second;
  }
  for(bool changed = true; changed;)
  {
    changed = false;
    for(const auto &entry : dependencies)
      if(roots.count(entry.first))
        for(const auto &source : entry.second)
          changed |= roots.insert(source).second;
  }
  symbol_sett removed_objects;
  for(auto &ins : program.instructions)
  {
    const exprt *removed = nullptr;
    if(
      ins.is_assign() && candidates.count(&ins) &&
      !roots.count(
        to_symbol_expr(root_object(ins.assign_lhs())).get_identifier()))
    {
      removed = &root_object(ins.assign_lhs());
      ++report.assignments;
    }
    else if(
      ins.is_decl() && removable_lvalue(ins.decl_symbol(), ns, memory) &&
      !roots.count(ins.decl_symbol().get_identifier()))
    {
      removed = &ins.decl_symbol();
      ++report.declarations;
    }
    else if(
      ins.is_dead() && removable_lvalue(ins.dead_symbol(), ns, memory) &&
      !roots.count(ins.dead_symbol().get_identifier()))
    {
      removed = &ins.dead_symbol();
      ++report.lifetimes;
    }
    if(removed)
    {
      const auto &id = to_symbol_expr(*removed).get_identifier();
      if(memory.symbols.count(id))
        removed_objects.insert(id);
      ins.turn_into_skip();
    }
  }
  remove_skip(program);
  program.update();
  const auto retained = scan_pre_state_memory_symbols(program, ns);
  for(const auto &id : removed_objects)
    if(!retained.symbols.count(id))
      ++report.removed_objects;
}
} // namespace

pre_state_memory_symbolst scan_pre_state_memory_symbols(
  const goto_programt &program,
  const namespacet &ns)
{
  pre_state_memory_symbolst result;
  result.arbitrary_pointer_input = has_arbitrary_pointer_input(program, ns);
  symbol_sett examined;
  const auto scan =
    [&](const auto &self, const exprt &expr, bool addressed) -> void
  {
    if(expr.id() == ID_symbol)
    {
      const auto &id = to_symbol_expr(expr).get_identifier();
      const symbolt *symbol = nullptr;
      const bool known = !ns.lookup(id, symbol) && symbol;
      const auto type = follow_tag_type(expr.type(), ns);
      if(addressed)
        result.addressed_symbols.insert(id);
      if(
        addressed || aggregate(type) ||
        (known && result.arbitrary_pointer_input &&
         is_c_source_object(*symbol, ns)))
        result.symbols.insert(id);
      if(
        known && examined.insert(id).second && symbol->is_static_lifetime &&
        symbol->value.is_not_nil())
        self(self, symbol->value, false);
    }
    if(expr.id() == ID_address_of)
      self(self, to_address_of_expr(expr).object(), true);
    else if(expr.id() == ID_member)
      self(self, to_member_expr(expr).compound(), addressed);
    else if(expr.id() == ID_index)
    {
      self(self, to_index_expr(expr).array(), addressed);
      self(self, to_index_expr(expr).index(), false);
    }
    else
      for(const auto &operand : expr.operands())
        self(self, operand, false);
  };
  for(const auto &ins : program.instructions)
  {
    scan(scan, ins.code(), false);
    if(ins.has_condition())
      scan(scan, ins.condition(), false);
  }
  if(result.arbitrary_pointer_input)
    for(const auto &entry : ns.get_symbol_table().symbols)
    {
      const auto &symbol = entry.second;
      if(
        is_c_source_object(symbol, ns) && symbol.is_static_lifetime &&
        (!symbol.is_extern || symbol.value.is_not_nil()))
        scan(scan, symbol.symbol_expr(), false);
    }
  return result;
}

pre_state_optimization_reportt
optimize_before_state(goto_programt &program, const namespacet &ns)
{
  pre_state_optimization_reportt report;
  report.before = program.instructions.size();
  if(pointer_identity_sensitive(program, ns))
    report.skipped_reason = "pointer-identity-sensitive-program";
  else if(!program.instructions.empty() && can_optimize(program))
  {
    propagate_constants(program, ns, report);
    const auto memory = scan_pre_state_memory_symbols(program, ns);
    project_storage(program, ns, memory, report);
  }
  report.after = program.instructions.size();
  report.memory_symbols = scan_pre_state_memory_symbols(program, ns).symbols;
  return report;
}
