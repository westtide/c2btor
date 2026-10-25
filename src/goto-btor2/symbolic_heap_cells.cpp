// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "symbolic_heap_cells.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include "btor2_type_utils.h"
#include "memory_access.h"

#include <algorithm>
#include <deque>
#include <map>
#include <set>
#include <vector>

namespace
{
// Bit r denotes a possible byte-offset residue r modulo 8. Missing facts
// mean every residue; joins take unions, so this domain needs no widening.
using residuest = unsigned;
constexpr residuest unknown = 0xff;
constexpr residuest aligned = 1;

struct statet
{
  bool reachable = false;
  std::map<irep_idt, residuest> pointers;
};

unsigned modulo8(const mp_integer &value)
{
  return numeric_cast_v<unsigned>((value % 8 + 8) % 8);
}

residuest combine(residuest left, residuest right, const irep_idt &operation)
{
  residuest result = 0;
  for(unsigned a = 0; a < 8; ++a)
    for(unsigned b = 0; b < 8; ++b)
      if((left & (1u << a)) && (right & (1u << b)))
      {
        const unsigned r = operation == ID_mult    ? a * b
                           : operation == ID_minus ? a + 8 - b
                                                   : a + b;
        result |= 1u << (r % 8);
      }
  return result;
}

bool pointer_type(const typet &type, const namespacet &ns)
{
  return follow_tag_type(type, ns).id() == ID_pointer;
}

bool volatile_type(const typet &type, const namespacet &ns)
{
  const auto followed = follow_tag_type(type, ns);
  return type.get_bool(ID_C_volatile) || type.get_bool(ID_C_atomic) ||
         followed.get_bool(ID_C_volatile) || followed.get_bool(ID_C_atomic);
}

class cell_certifiert
{
  const namespacet &ns;
  bool arbitrary_pointers;
  std::set<irep_idt> addressed_pointers;
  symbolic_heap_cell_certificatet result;

  residuest integer_residues(const exprt &raw) const
  {
    const auto expr = simplify_expr(raw, ns);
    if(const auto value = numeric_cast<mp_integer>(expr))
      return 1u << modulo8(*value);
    const auto type = follow_tag_type(expr.type(), ns);
    // A machine arithmetic modulus 2^W preserves modulo 8 when W >= 3.
    // Smaller casts and non-integer operations are deliberately unknown.
    if(
      (type.id() != ID_signedbv && type.id() != ID_unsignedbv) ||
      to_bitvector_type(type).get_width() < 3)
      return unknown;
    if(expr.id() == ID_typecast)
    {
      const auto &source = expr.operands()[0];
      const auto source_type = follow_tag_type(source.type(), ns);
      if(
        (source_type.id() == ID_signedbv ||
         source_type.id() == ID_unsignedbv) &&
        to_bitvector_type(source_type).get_width() >= 3)
        return integer_residues(source);
      return unknown;
    }
    if(expr.id() == ID_if)
      return integer_residues(expr.operands()[1]) |
             integer_residues(expr.operands()[2]);
    if(expr.id() == ID_unary_minus)
      return combine(aligned, integer_residues(expr.operands()[0]), ID_minus);
    if(
      (expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult) &&
      expr.operands().size() >= 2)
    {
      auto residues = integer_residues(expr.operands()[0]);
      for(std::size_t i = 1; i < expr.operands().size(); ++i)
        residues =
          combine(residues, integer_residues(expr.operands()[i]), expr.id());
      return residues;
    }
    return unknown;
  }

  residuest index_delta(const exprt &index, const typet &element) const
  {
    const auto size = pointer_offset_size(element, ns);
    return size
             ? combine(integer_residues(index), 1u << modulo8(*size), ID_mult)
             : unknown;
  }

  residuest address_residues(const exprt &object, const statet &state) const
  {
    if(object.id() == ID_symbol || object.id() == ID_string_constant)
      return aligned;
    if(object.id() == ID_dereference)
      return pointer_residues(object.operands()[0], state);
    if(object.id() == ID_index)
    {
      const auto &index = to_index_expr(object);
      const auto base = pointer_type(index.array().type(), ns)
                          ? pointer_residues(index.array(), state)
                          : address_residues(index.array(), state);
      return combine(base, index_delta(index.index(), object.type()), ID_plus);
    }
    if(object.id() == ID_member)
    {
      const auto &member = to_member_expr(object);
      const auto type = follow_tag_type(member.compound().type(), ns);
      if(type.id() == ID_union)
        return address_residues(member.compound(), state);
      const auto offset = member_offset_expr(member, ns);
      if(offset)
        return combine(
          address_residues(member.compound(), state),
          integer_residues(*offset),
          ID_plus);
    }
    return unknown;
  }

  residuest pointer_residues(const exprt &raw, const statet &state) const
  {
    const auto expr = simplify_expr(raw, ns);
    if(expr.id() == ID_symbol)
    {
      const auto found =
        state.pointers.find(to_symbol_expr(expr).get_identifier());
      return found == state.pointers.end() ? unknown : found->second;
    }
    if(expr.id() == ID_constant && pointer_type(expr.type(), ns))
      return to_constant_expr(expr).is_null_pointer() ? aligned : unknown;
    if(
      expr.id() == ID_side_effect && expr.get(ID_statement) == ID_allocate &&
      expr.operands().size() == 2)
      return aligned;
    if(expr.id() == ID_address_of)
      return address_residues(expr.operands()[0], state);
    if(expr.id() == ID_typecast)
    {
      if(pointer_type(expr.operands()[0].type(), ns))
        return pointer_residues(expr.operands()[0], state);
      if(follow_tag_type(expr.operands()[0].type(), ns).id() == ID_array)
        return address_residues(expr.operands()[0], state);
      const auto value =
        numeric_cast<mp_integer>(simplify_expr(expr.operands()[0], ns));
      return value && *value == 0 ? aligned : unknown;
    }
    if(expr.id() == ID_if)
      return pointer_residues(expr.operands()[1], state) |
             pointer_residues(expr.operands()[2], state);
    if(
      (expr.id() == ID_plus || expr.id() == ID_minus) &&
      expr.operands().size() == 2 && pointer_type(expr.type(), ns))
    {
      const exprt *pointer = &expr.operands()[0], *index = &expr.operands()[1];
      if(!pointer_type(pointer->type(), ns) && expr.id() == ID_plus)
        std::swap(pointer, index);
      if(pointer_type(pointer->type(), ns) && !pointer_type(index->type(), ns))
        return combine(
          pointer_residues(*pointer, state),
          index_delta(
            *index,
            to_pointer_type(follow_tag_type(pointer->type(), ns)).base_type()),
          expr.id());
    }
    return unknown;
  }

  void find_addressed_pointers(const exprt &expr)
  {
    if(expr.id() == ID_address_of)
    {
      const auto &object = expr.operands()[0];
      if(object.id() == ID_symbol && pointer_type(object.type(), ns))
        addressed_pointers.insert(to_symbol_expr(object).get_identifier());
    }
    for(const auto &operand : expr.operands())
      find_addressed_pointers(operand);
  }

  void forget_indirect_write(statet &state) const
  {
    if(arbitrary_pointers)
      state.pointers.clear();
    else
      for(const auto &id : addressed_pointers)
        state.pointers.erase(id);
  }

  bool known_nondet_call(const goto_programt::instructiont &instruction) const
  {
    if(instruction.call_function().id() != ID_symbol)
      return false;
    const auto name =
      id2string(to_symbol_expr(instruction.call_function()).get_identifier());
    return name.rfind("__VERIFIER_nondet_", 0) == 0 ||
           name.rfind("__CPROVER_nondet_", 0) == 0;
  }

  bool unknown_effect(const exprt &expr) const
  {
    if(
      expr.id() == ID_side_effect && expr.get(ID_statement) != ID_nondet &&
      expr.get(ID_statement) != ID_allocate)
      return true;
    return std::any_of(
      expr.operands().begin(),
      expr.operands().end(),
      [&](const exprt &operand) { return unknown_effect(operand); });
  }

  void
  transfer(const goto_programt::instructiont &instruction, statet &state) const
  {
    if(
      unknown_effect(instruction.code()) ||
      (instruction.has_condition() && unknown_effect(instruction.condition())))
      state.pointers.clear();
    if(instruction.is_decl())
      state.pointers.erase(instruction.decl_symbol().get_identifier());
    else if(instruction.is_dead())
      state.pointers.erase(instruction.dead_symbol().get_identifier());
    else if(instruction.is_assign())
    {
      const auto &lhs = instruction.assign_lhs();
      if(lhs.id() == ID_symbol)
      {
        const auto id = to_symbol_expr(lhs).get_identifier();
        const auto residues =
          pointer_type(lhs.type(), ns)
            ? pointer_residues(instruction.assign_rhs(), state)
            : unknown;
        state.pointers.erase(id);
        if(residues != unknown)
          state.pointers.emplace(id, residues);
      }
      else
        forget_indirect_write(state);
    }
    else if(instruction.is_function_call())
    {
      if(!known_nondet_call(instruction))
        state.pointers.clear();
      const auto &lhs = instruction.call_lhs();
      if(lhs.id() == ID_symbol)
        state.pointers.erase(to_symbol_expr(lhs).get_identifier());
      else if(lhs.is_not_nil())
        forget_indirect_write(state);
    }
    else if(instruction.is_other())
    {
      const auto statement = instruction.get_other().get_statement();
      if(
        statement != ID_expression && statement != "c2btor_deallocate" &&
        statement != "c2btor_copy_check")
        state.pointers.clear();
    }
  }

  bool fail(const std::string &reason)
  {
    result.reason = reason;
    return false;
  }

  bool access(const typet &raw_type, residuest residues)
  {
    const auto type = follow_tag_type(raw_type, ns);
    const auto bytes = pointer_offset_size(type, ns);
    if(
      (type.id() != ID_signedbv && type.id() != ID_unsignedbv &&
       type.id() != ID_floatbv && type.id() != ID_fixedbv) ||
      to_bitvector_type(type).get_width() != 64 || !bytes || *bytes != 8)
      return fail("memory access is not a scalar 64-bit, eight-byte value");
    ++result.accesses;
    return residues == aligned ||
           fail("memory byte offset is not proven divisible by eight");
  }

  bool inspect_address(const exprt &object, const statet &state)
  {
    if(volatile_type(object.type(), ns))
      return fail("volatile or atomic memory is outside the cell certificate");
    if(object.id() == ID_dereference)
      return inspect(object.operands()[0], state);
    if(object.id() == ID_index)
    {
      const auto &index = to_index_expr(object);
      return (pointer_type(index.array().type(), ns)
                ? inspect(index.array(), state)
                : inspect_address(index.array(), state)) &&
             inspect(index.index(), state);
    }
    if(object.id() == ID_member)
      return inspect_address(to_member_expr(object).compound(), state);
    if(object.id() == ID_symbol || object.id() == ID_string_constant)
      return true;
    return fail("unrecognized address-forming operation");
  }

  bool inspect(const exprt &expr, const statet &state)
  {
    if(volatile_type(expr.type(), ns))
      return fail("volatile or atomic values are outside the cell certificate");
    if(
      expr.id() == ID_byte_extract_little_endian ||
      expr.id() == ID_byte_extract_big_endian ||
      expr.id() == ID_byte_update_little_endian ||
      expr.id() == ID_byte_update_big_endian)
      return fail("byte extraction or update requires byte storage");
    if(
      expr.id() == ID_side_effect && expr.get(ID_statement) != ID_nondet &&
      expr.get(ID_statement) != ID_allocate)
      return fail("unknown expression side effect may alter pointer values");
    if(expr.id() == ID_address_of)
      return inspect_address(expr.operands()[0], state);
    if(
      expr.id() == ID_dereference &&
      !access(expr.type(), pointer_residues(expr.operands()[0], state)))
      return false;
    if(expr.id() == ID_index && pointer_type(expr.operands()[0].type(), ns))
    {
      const auto residues = combine(
        pointer_residues(expr.operands()[0], state),
        index_delta(expr.operands()[1], expr.type()),
        ID_plus);
      if(!access(expr.type(), residues))
        return false;
    }
    for(const auto &operand : expr.operands())
      if(!inspect(operand, state))
        return false;
    return true;
  }

  bool inspect_instruction(
    const goto_programt::instructiont &instruction,
    const statet &state)
  {
    if(instruction.is_assign() && instruction.assign_lhs().id() == ID_typecast)
      return fail("cast lvalue write needs byte storage and pointer reanalysis");
    if(instruction.is_function_call() && !known_nondet_call(instruction))
      return fail("unknown call may access memory or alter pointer values");
    if(instruction.is_other())
    {
      const auto statement = instruction.get_other().get_statement();
      if(
        statement == "c2btor_copy_byte" || statement == "c2btor_copy_range" ||
        statement == ID_array_copy || statement == ID_array_replace ||
        statement == ID_array_set || statement == ID_havoc_object)
        return fail("copy, fill or havoc requires byte storage");
      if(
        statement != ID_expression && statement != "c2btor_deallocate" &&
        statement != "c2btor_copy_check")
        return fail(
          "unknown GOTO operation may access memory or alter pointers");
    }
    else if(
      !instruction.is_assign() && !instruction.is_decl() &&
      !instruction.is_dead() && !instruction.is_function_call() &&
      !instruction.is_goto() && !instruction.is_assume() &&
      !instruction.is_assert() && !instruction.is_skip() &&
      !instruction.is_location() && !instruction.is_end_function() &&
      !instruction.is_set_return_value())
      return fail(
        "non-sequential GOTO operation is outside the cell certificate");
    return inspect(instruction.code(), state) &&
           (!instruction.has_condition() ||
            inspect(instruction.condition(), state));
  }

public:
  cell_certifiert(const goto_programt &program, const namespacet &ns)
    : ns(ns), arbitrary_pointers(has_arbitrary_pointer_input(program, ns))
  {
    for(const auto &instruction : program.instructions)
    {
      find_addressed_pointers(instruction.code());
      if(instruction.has_condition())
        find_addressed_pointers(instruction.condition());
    }
  }

  symbolic_heap_cell_certificatet run(const goto_programt &program)
  {
    if(config.ansi_c.char_width != 8 || config.ansi_c.pointer_width < 3)
    {
      fail(
        "cell certificate requires eight-bit bytes and at least three offset "
        "bits");
      return result;
    }
    if(program.instructions.empty())
    {
      fail("no memory accesses");
      return result;
    }
    std::vector<goto_programt::const_targett> instructions;
    std::map<const goto_programt::instructiont *, std::size_t> indices;
    for(auto it = program.instructions.begin();
        it != program.instructions.end();
        ++it)
    {
      indices.emplace(&*it, instructions.size());
      instructions.push_back(it);
    }
    std::vector<statet> before(instructions.size());
    before.front().reachable = true;
    for(const auto &entry : ns.get_symbol_table().symbols)
    {
      const auto &symbol = entry.second;
      if(symbol.is_static_lifetime && symbol.value.is_not_nil())
      {
        find_addressed_pointers(symbol.value);
        if(pointer_type(symbol.type, ns))
        {
          const auto residues = pointer_residues(symbol.value, before.front());
          if(residues != unknown)
            before.front().pointers.emplace(entry.first, residues);
        }
      }
    }
    std::deque<std::size_t> work{0};
    std::vector<bool> queued(instructions.size(), false);
    queued[0] = true;
    auto merge = [&](std::size_t index, const statet &incoming)
    {
      auto &destination = before[index];
      bool changed = !destination.reachable;
      if(!destination.reachable)
        destination = incoming;
      else
        for(auto it = destination.pointers.begin();
            it != destination.pointers.end();)
        {
          const auto found = incoming.pointers.find(it->first);
          const auto residues = found == incoming.pointers.end()
                                  ? unknown
                                  : it->second | found->second;
          if(residues == unknown)
          {
            it = destination.pointers.erase(it);
            changed = true;
          }
          else
          {
            changed |= it->second != residues;
            it->second = residues;
            ++it;
          }
        }
      if(changed && !queued[index])
      {
        queued[index] = true;
        work.push_back(index);
      }
    };
    while(!work.empty())
    {
      const auto i = work.front();
      work.pop_front();
      queued[i] = false;
      const auto instruction = instructions[i];
      auto next = before[i];
      transfer(*instruction, next);
      if(instruction->is_end_function())
        continue;
      for(const auto successor : program.get_successors(instruction))
      {
        if(successor == program.instructions.end())
          continue;
        const auto found = indices.find(&*successor);
        if(found == indices.end())
        {
          fail("GOTO successor lies outside the analyzed program");
          return result;
        }
        merge(found->second, next);
      }
    }
    for(std::size_t i = 0; i < instructions.size(); ++i)
      if(
        before[i].reachable &&
        !inspect_instruction(*instructions[i], before[i]))
        return result;
    result.word64 = result.accesses != 0;
    result.reason = result.word64
                      ? "all indirect accesses are aligned 64-bit values"
                      : "no memory accesses";
    return result;
  }
};
} // namespace

symbolic_heap_cell_certificatet
certify_symbolic_heap_cells(const goto_programt &program, const namespacet &ns)
{
  return cell_certifiert(program, ns).run(program);
}
