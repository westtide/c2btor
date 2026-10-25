// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_AUTOMATIC_LIFETIMES_H
#define CPROVER_GOTO_BTOR2_AUTOMATIC_LIFETIMES_H

#include <util/config.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <goto-programs/cfg.h>

#include <map>
#include <vector>

/// A deliberately small, sufficient certificate for reusing physical storage.
/// Pointer values must remain in non-addressed automatic scalar aliases, and
/// all aliases must die before the owning object. CFG joins use may-liveness;
/// an unknown effect while the owner may be live or an escaping identity
/// prevents certification. Unrelated effects outside that lifetime are harmless.
inline bool automatic_object_reuse_is_safe(
  const goto_programt &program,
  const namespacet &ns,
  const irep_idt &owner,
  const std::set<irep_idt> &memory_objects,
  bool internal_byte_snapshot = false)
{
  if(program.instructions.empty())
    return false;
  std::set<irep_idt> declared;
  for(const auto &instruction : program.instructions)
    if(instruction.is_decl())
      declared.insert(instruction.decl_symbol().get_identifier());
  std::set<irep_idt> aliases;
  const auto origin = [&](const auto &self, const exprt &e) -> bool
  {
    if(e.type().id() != ID_pointer)
      return false;
    if(e.id() == ID_symbol)
      return aliases.count(to_symbol_expr(e).get_identifier()) != 0;
    if(e.id() == ID_address_of)
    {
      const auto &object = to_address_of_expr(e).object();
      return has_symbol_expr(object, owner, true) ||
             has_subexpr(
               object,
               [&](const exprt &part)
               {
                 return (part.id() == ID_dereference &&
                         self(self, to_dereference_expr(part).pointer())) ||
                        (part.id() == ID_index &&
                         to_index_expr(part).array().type().id() ==
                           ID_pointer &&
                         self(self, to_index_expr(part).array()));
               });
    }
    if(e.id() == ID_dereference || e.id() == ID_index || e.id() == ID_member)
      return false;
    for(const auto &operand : e.operands())
      if(self(self, operand))
        return true;
    return false;
  };
  const auto transports = [&](const auto &self, const exprt &e) -> bool
  {
    // Reading object contents consumes its address, not its identity.
    if(e.id() == ID_dereference || e.id() == ID_index || e.id() == ID_member)
      return false;
    if(origin(origin, e))
      return true;
    for(const auto &operand : e.operands())
      if(self(self, operand))
        return true;
    return false;
  };
  bool changed;
  do
  {
    changed = false;
    for(const auto &instruction : program.instructions)
    {
      if(
        !instruction.is_assign() ||
        !transports(transports, instruction.assign_rhs()))
        continue;
      const auto &lhs = instruction.assign_lhs();
      if(lhs.id() != ID_symbol || lhs.type().id() != ID_pointer)
        return false;
      const auto id = to_symbol_expr(lhs).get_identifier();
      const symbolt *symbol = nullptr;
      if(
        ns.lookup(id, symbol) || !symbol || symbol->is_static_lifetime ||
        symbol->is_parameter || !declared.count(id) || memory_objects.count(id))
        return false;
      changed |= aliases.insert(id).second;
    }
  } while(changed);

  if(internal_byte_snapshot)
  {
    // A generated snapshot has no observable identity. Do not extend the
    // general alias certificate to byte copies: those could transport a user
    // object's pointer representation into persistent storage.
    const auto &symbol = ns.lookup(owner);
    if(
      !symbol.is_auxiliary || symbol.type.id() != ID_array ||
      !symbol.type.get_bool("C_c2btor_copy_snapshot") || !aliases.empty())
      return false;
    const auto &element_type = to_array_type(symbol.type).element_type();
    if(
      element_type.id() != ID_unsignedbv ||
      to_unsignedbv_type(element_type).get_width() != config.ansi_c.char_width)
      return false;
    for(const auto &instruction : program.instructions)
    {
      if(
        instruction.has_condition() &&
        has_symbol_expr(instruction.condition(), owner, true))
        return false;
      if(!has_symbol_expr(instruction.code(), owner, true))
        continue;
      if(
        (instruction.is_decl() &&
         instruction.decl_symbol().get_identifier() == owner) ||
        (instruction.is_dead() &&
         instruction.dead_symbol().get_identifier() == owner))
        continue;
      if(
        !instruction.is_other() ||
        instruction.code().get_statement() != "c2btor_copy_byte" ||
        instruction.code().operands().size() != 2)
        return false;
      for(const auto &operand : instruction.code().operands())
      {
        if(!has_symbol_expr(operand, owner, true))
          continue;
        if(operand.id() != ID_address_of)
          return false;
        const auto &object = to_address_of_expr(operand).object();
        if(object.id() != ID_index)
          return false;
        const auto &element = to_index_expr(object);
        if(
          element.array().id() != ID_symbol ||
          to_symbol_expr(element.array()).get_identifier() != owner ||
          has_symbol_expr(element.index(), owner, true))
          return false;
      }
    }
  }

  struct payloadt
  {
  };
  cfg_baset<payloadt> cfg;
  cfg(program);
  const auto entry = cfg.get_node_index(program.instructions.begin());
  // A separate must-provenance analysis admits non-addressed pointer states
  // containing NULL, fresh dynamic identities, or known other objects. In particular, library
  // allocation bookkeeping need not prevent unrelated local storage reuse.
  // Unknown parameters, loads and partially initialized aliases never qualify.
  std::map<irep_idt, std::size_t> pointer_indices;
  for(const auto &instruction : program.instructions)
  {
    find_symbols_sett ids;
    find_type_and_expr_symbols(instruction.code(), ids);
    if(instruction.has_condition())
      find_type_and_expr_symbols(instruction.condition(), ids);
    for(const auto &id : ids)
    {
      const symbolt *symbol = nullptr;
      if(
        !ns.lookup(id, symbol) && symbol && symbol->type.id() == ID_pointer &&
        !memory_objects.count(id) && !pointer_indices.count(id))
        pointer_indices.emplace(id, pointer_indices.size());
    }
  }
  // 0: unreachable, 2: owner-disjoint, 3: unknown (may include either).
  std::vector<std::vector<unsigned>> pointer_incoming(
    cfg.size(), std::vector<unsigned>(pointer_indices.size(), 0));
  for(const auto &pointer : pointer_indices)
  {
    const auto &symbol = ns.lookup(pointer.first);
    pointer_incoming[entry][pointer.second] =
      symbol.is_static_lifetime && !symbol.is_extern &&
          symbol.value.is_constant() &&
          to_constant_expr(symbol.value).is_null_pointer()
        ? 2
        : 3;
  }
  const auto owner_disjoint_pointer =
    [&](const auto &self, const exprt &e, const std::vector<unsigned> &facts)
    -> bool
  {
    if(e.type().id() != ID_pointer)
      return false;
    if(e.is_constant())
      return to_constant_expr(e).is_null_pointer();
    if(e.id() == ID_symbol)
    {
      const auto found =
        pointer_indices.find(to_symbol_expr(e).get_identifier());
      return found != pointer_indices.end() && facts[found->second] == 2;
    }
    if(e.id() == ID_typecast && !e.operands().empty())
    {
      const auto &operand = e.operands().front();
      return operand.type().id() == ID_pointer
               ? self(self, operand, facts)
               : operand.is_constant() && to_constant_expr(operand).is_zero();
    }
    if(e.id() == ID_if)
      return self(self, to_if_expr(e).true_case(), facts) &&
             self(self, to_if_expr(e).false_case(), facts);
    if(e.id() == ID_address_of)
    {
      const auto known_object =
        [&](const auto &check, const exprt &object) -> bool
      {
        if(object.id() == ID_symbol)
        {
          const auto id = to_symbol_expr(object).get_identifier();
          return id != owner && memory_objects.count(id) != 0;
        }
        if(object.id() == ID_index)
        {
          const auto &index = to_index_expr(object);
          return index.array().type().id() == ID_array &&
                 check(check, index.array());
        }
        if(object.id() == ID_member)
          return check(check, to_member_expr(object).compound());
        if(object.id() == ID_dereference)
          return self(self, to_dereference_expr(object).pointer(), facts);
        return false;
      };
      return known_object(known_object, to_address_of_expr(e).object());
    }
    if(e.id() == ID_plus || e.id() == ID_minus)
    {
      bool pointer_found = false;
      for(const auto &operand : e.operands())
        if(operand.type().id() == ID_pointer)
        {
          pointer_found = true;
          if(!self(self, operand, facts))
            return false;
        }
      return pointer_found;
    }
    return e.id() == ID_side_effect && e.get(ID_statement) == ID_allocate;
  };
  std::vector<bool> pointer_reached(cfg.size(), false);
  pointer_reached[entry] = true;
  std::vector<std::size_t> pointer_pending{entry};
  while(!pointer_pending.empty())
  {
    const auto node = pointer_pending.back();
    pointer_pending.pop_back();
    auto outgoing = pointer_incoming[node];
    const auto &instruction = *cfg[node].PC;
    if(instruction.is_decl() || instruction.is_dead())
    {
      const auto id = instruction.is_decl()
                        ? instruction.decl_symbol().get_identifier()
                        : instruction.dead_symbol().get_identifier();
      const auto pointer = pointer_indices.find(id);
      if(pointer != pointer_indices.end())
        outgoing[pointer->second] = 3;
    }
    else if(
      instruction.is_assign() && instruction.assign_lhs().id() == ID_symbol)
    {
      const auto pointer = pointer_indices.find(
        to_symbol_expr(instruction.assign_lhs()).get_identifier());
      if(pointer != pointer_indices.end())
        outgoing[pointer->second] = owner_disjoint_pointer(
                                      owner_disjoint_pointer,
                                      instruction.assign_rhs(),
                                      pointer_incoming[node])
                                      ? 2
                                      : 3;
    }
    for(const auto &edge : cfg[node].out)
    {
      bool update = !pointer_reached[edge.first];
      pointer_reached[edge.first] = true;
      for(std::size_t i = 0; i < outgoing.size(); ++i)
      {
        const auto merged = pointer_incoming[edge.first][i] | outgoing[i];
        update |= pointer_incoming[edge.first][i] != merged;
        pointer_incoming[edge.first][i] = merged;
      }
      if(update)
        pointer_pending.push_back(edge.first);
    }
  }
  std::vector<irep_idt> tracked{owner};
  tracked.insert(tracked.end(), aliases.begin(), aliases.end());
  std::map<irep_idt, std::size_t> indices;
  for(std::size_t i = 0; i < tracked.size(); ++i)
    indices.emplace(tracked[i], i);
  // 0: unreachable, 1: inactive, 2: live, 3: either.
  std::vector<std::vector<unsigned>> incoming(
    cfg.size(), std::vector<unsigned>(tracked.size(), 0));
  incoming[entry].assign(tracked.size(), 1);
  std::vector<std::size_t> pending{entry};
  while(!pending.empty())
  {
    const auto node = pending.back();
    pending.pop_back();
    auto outgoing = incoming[node];
    const auto &instruction = *cfg[node].PC;
    if(instruction.is_decl() || instruction.is_dead())
    {
      const auto id = instruction.is_decl()
                        ? instruction.decl_symbol().get_identifier()
                        : instruction.dead_symbol().get_identifier();
      const auto index = indices.find(id);
      if(index != indices.end())
        outgoing[index->second] = instruction.is_decl() ? 2 : 1;
    }
    for(const auto &edge : cfg[node].out)
    {
      bool update = false;
      for(std::size_t i = 0; i < tracked.size(); ++i)
      {
        const auto merged = incoming[edge.first][i] | outgoing[i];
        update |= incoming[edge.first][i] != merged;
        incoming[edge.first][i] = merged;
      }
      if(update)
        pending.push_back(edge.first);
    }
  }

  for(auto pc = program.instructions.begin(); pc != program.instructions.end();
      ++pc)
  {
    const auto &instruction = *pc;
    const auto node = cfg.get_node_index(pc);
    // Unknown addresses matter while this lifetime can be observed. Facts
    // computed outside it may flow in, so every pointer read during a live
    // lifetime must still have owner-disjoint provenance or be a tracked alias.
    const bool owner_may_be_live = (incoming[node][0] & 2) != 0;
    const auto safe_pointer = [&](const auto &self, const exprt &e) -> bool
    {
      if(
        owner_disjoint_pointer(
          owner_disjoint_pointer, e, pointer_incoming[node]) ||
        origin(origin, e))
        return true;
      if(e.id() == ID_address_of)
      {
        const auto &object = to_address_of_expr(e).object();
        if(object.id() == ID_symbol)
          return memory_objects.count(
                   to_symbol_expr(object).get_identifier()) != 0;
        if(object.id() == ID_member || object.id() == ID_index)
          return !has_subexpr(
            object,
            [](const exprt &part)
            {
              return part.id() == ID_dereference ||
                     (part.id() == ID_index &&
                      to_index_expr(part).array().type().id() == ID_pointer);
            });
      }
      if(
        e.id() == ID_typecast && !e.operands().empty() &&
        e.operands().front().type().id() == ID_pointer)
        return self(self, e.operands().front());
      if(e.id() == ID_if)
        return self(self, to_if_expr(e).true_case()) &&
               self(self, to_if_expr(e).false_case());
      if(e.id() == ID_plus || e.id() == ID_minus)
        for(const auto &operand : e.operands())
          if(operand.type().id() == ID_pointer)
            return self(self, operand);
      return false;
    };
    const auto unknown_live_pointer = [&](const exprt &e)
    { return e.type().id() == ID_pointer && !safe_pointer(safe_pointer, e); };
    const auto observes_identity = [&](const exprt &e)
    {
      // Untracked entry/global pointer values may guess an object's identity.
      // Do not infer their provenance merely because they are not aliases.
      if(e.id() == ID_symbol && e.type().id() == ID_pointer)
      {
        const auto id = to_symbol_expr(e).get_identifier();
        const symbolt *symbol = nullptr;
        if(ns.lookup(id, symbol) || !symbol)
          return true;
        // An inlined parameter with DECL/assignment is a local value. Its
        // provenance is checked at the reads below, not at its assignment LHS.
        if(symbol->is_parameter || !declared.count(id))
          return !owner_disjoint_pointer(
            owner_disjoint_pointer, e, pointer_incoming[node]);
      }
      const bool unknown_pointer =
        e.type().id() == ID_pointer &&
        ((e.id() == ID_typecast && !e.operands().empty() &&
          e.operands().front().type().id() != ID_pointer &&
          !(e.operands().front().is_constant() &&
            to_constant_expr(e.operands().front()).is_zero())) ||
         e.id() == ID_dereference || e.id() == ID_member || e.id() == ID_index);
      const bool unknown_object_query =
        e.id() == ID_pointer_object &&
        (e.operands().empty() || !owner_disjoint_pointer(
                                   owner_disjoint_pointer,
                                   e.operands().front(),
                                   pointer_incoming[node]));
      return unknown_pointer ||
             (unknown_object_query ||
              (e.id() == ID_side_effect && e.get(ID_statement) != ID_allocate &&
               e.type().id() == ID_pointer)) ||
             (e.id() == ID_typecast && e.type().id() != ID_pointer &&
              !e.operands().empty() && origin(origin, e.operands().front()));
    };
    const bool private_copy =
      internal_byte_snapshot && instruction.is_other() &&
      instruction.code().get_statement() == "c2btor_copy_byte" &&
      instruction.code().operands().size() == 2;
    if(internal_byte_snapshot && owner_may_be_live)
    {
      const auto unknown_identity = [&](const exprt &e)
      {
        if(e.type().id() != ID_pointer)
          return false;
        // The only permitted address of this owner is the canonical private
        // byte operand checked above. Every other pointer read must have a
        // must-provenance fact excluding the snapshot's identity.
        if(
          private_copy && e.id() == ID_address_of &&
          has_symbol_expr(e, owner, true))
          return false;
        return !owner_disjoint_pointer(
          owner_disjoint_pointer, e, pointer_incoming[node]);
      };
      const exprt &reads =
        instruction.is_assign() ? instruction.assign_rhs() : instruction.code();
      if(
        (!instruction.is_decl() && !instruction.is_dead() &&
         has_subexpr(reads, unknown_identity)) ||
        (instruction.is_assign() &&
         instruction.assign_lhs().id() != ID_symbol &&
         has_subexpr(instruction.assign_lhs(), unknown_identity)) ||
        (instruction.has_condition() &&
         has_subexpr(instruction.condition(), unknown_identity)))
        return false;
    }
    const bool pure_expression =
      instruction.is_other() &&
      instruction.code().get_statement() == ID_expression &&
      !has_subexpr(
        instruction.code(),
        [](const exprt &e) { return e.id() == ID_side_effect; });
    const bool heap_release =
      instruction.is_other() &&
      instruction.code().get_statement() == "c2btor_deallocate" &&
      instruction.code().operands().size() == 1 &&
      owner_disjoint_pointer(
        owner_disjoint_pointer,
        instruction.code().operands().front(),
        pointer_incoming[node]);
    const exprt &reads =
      instruction.is_assign() ? instruction.assign_rhs() : instruction.code();
    if(
      owner_may_be_live &&
      ((instruction.is_other() && !private_copy && !pure_expression &&
        !heap_release) ||
       (!instruction.is_decl() && !instruction.is_dead() &&
        has_subexpr(reads, observes_identity)) ||
       (instruction.is_assign() && instruction.assign_lhs().id() != ID_symbol &&
        has_subexpr(instruction.assign_lhs(), observes_identity)) ||
       (instruction.has_condition() &&
        has_subexpr(instruction.condition(), observes_identity)) ||
       (!instruction.is_decl() && !instruction.is_dead() &&
        has_subexpr(reads, unknown_live_pointer)) ||
       (instruction.is_assign() && instruction.assign_lhs().id() != ID_symbol &&
        has_subexpr(instruction.assign_lhs(), unknown_live_pointer)) ||
       (instruction.has_condition() &&
        has_subexpr(instruction.condition(), unknown_live_pointer))))
      return false;
    if(instruction.is_function_call())
      return false; // No effect summary for a residual call.
  }
  for(std::size_t node = 0; node < cfg.size(); ++node)
  {
    if(incoming[node][0] == 0)
      continue;
    const auto &instruction = *cfg[node].PC;
    if(instruction.is_decl() || instruction.is_dead())
    {
      const auto id = instruction.is_decl()
                        ? instruction.decl_symbol().get_identifier()
                        : instruction.dead_symbol().get_identifier();
      if(id == owner)
      {
        if(instruction.is_decl() && incoming[node][0] != 1)
          return false;
        for(std::size_t i = 1; i < tracked.size(); ++i)
          if(incoming[node][i] & 2)
            return false;
      }
      continue;
    }
    find_symbols_sett used;
    find_type_and_expr_symbols(instruction.code(), used);
    if(instruction.has_condition())
      find_type_and_expr_symbols(instruction.condition(), used);
    for(std::size_t i = 0; i < tracked.size(); ++i)
      if(
        used.count(tracked[i]) &&
        (incoming[node][0] != 2 || incoming[node][i] != 2))
        return false;
  }
  return true;
}
#endif
