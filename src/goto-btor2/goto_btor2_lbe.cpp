// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "goto_btor2_converter.h"

#include <set>

bool goto_to_btor2_convertert::lbe_expression(const exprt &expr) const
{
  const auto &type = expr.type();
  if(
    type.get_bool(ID_C_volatile) ||
    (optimizations.scalar_blocks && type.get_bool(ID_C_atomic)) ||
    (type.id() != ID_bool && type.id() != ID_c_bool &&
     type.id() != ID_signedbv && type.id() != ID_unsignedbv))
    return false;
  if(expr.id() == ID_symbol)
  {
    const auto variable = variables.find(to_symbol_expr(expr).get_identifier());
    return variable != variables.end() &&
           !variable->second.type.get_bool(ID_C_volatile) &&
           (!optimizations.scalar_blocks ||
            !variable->second.type.get_bool(ID_C_atomic));
  }
  if(optimizations.array_blocks && expr.id() == ID_index)
  {
    // Only complete logical element views enter a block. Pointer, byte and
    // partial-array views retain their ordinary instruction boundaries.
    if(!memory.logical_arrays.owns_lvalue(expr))
      return false;
    const exprt *root = &expr;
    std::size_t rank = 0;
    while(root->id() == ID_index && root->operands().size() == 2)
    {
      if(!lbe_expression(to_index_expr(*root).index()))
        return false;
      ++rank;
      root = &to_index_expr(*root).array();
    }
    if(
      root->id() != ID_symbol || !memory.logical_arrays.owns_symbol(
                                   to_symbol_expr(*root).get_identifier()))
      return false;
    std::vector<array_dimt> dimensions;
    typet leaf;
    get_array_dimensions(root->type(), ns, dimensions, leaf);
    return rank == dimensions.size() &&
           (leaf.id() == ID_signedbv || leaf.id() == ID_unsignedbv ||
            leaf.id() == ID_bool || leaf.id() == ID_c_bool);
  }
  static const std::set<irep_idt> pure{
    ID_constant, ID_typecast, ID_plus,   ID_minus, ID_unary_minus, ID_mult,
    ID_div,      ID_mod,      ID_bitand, ID_bitor, ID_bitxor,      ID_bitnot,
    ID_shl,      ID_lshr,     ID_ashr,   ID_equal, ID_notequal,    ID_lt,
    ID_le,       ID_gt,       ID_ge,     ID_and,   ID_or,          ID_xor,
    ID_not,      ID_implies,  ID_if};
  if(!pure.count(expr.id()))
    return false;
  for(const auto &operand : expr.operands())
    if(!lbe_expression(operand))
      return false;
  return true;
}

bool goto_to_btor2_convertert::lbe_instruction(unsigned loc) const
{
  const auto &info = locations.at(loc);
  const auto &instruction = *info.instruction;
  // A terminal sequential instruction or conditional GOTO self-loops at its
  // own PC. Keep it singleton so the self-loop cannot replay earlier writes.
  if(
    optimizations.scalar_blocks && loc + 1 >= locations.size() &&
    (!instruction.is_goto() || !instruction.condition().is_true()))
    return false;
  const auto logical_declaration = [&](const symbol_exprt &symbol)
  {
    if(
      !optimizations.array_blocks ||
      !memory.logical_arrays.owns_symbol(symbol.get_identifier()))
      return false;
    std::vector<array_dimt> dimensions;
    typet leaf;
    get_array_dimensions(symbol.type(), ns, dimensions, leaf);
    if(
      leaf.id() != ID_signedbv && leaf.id() != ID_unsignedbv &&
      leaf.id() != ID_bool && leaf.id() != ID_c_bool)
      return false;
    for(const auto &dimension : dimensions)
      if(!lbe_expression(dimension.size))
        return false;
    return !dimensions.empty();
  };
  // Addressable lifetimes belong to memory and are excluded by the symbol
  // test. A scalar DECL is a fresh input at this original declaration site;
  // scalar DEAD has no state update in the instruction encoding either.
  if(instruction.is_decl())
    return lbe_expression(instruction.decl_symbol()) ||
           logical_declaration(instruction.decl_symbol());
  if(instruction.is_dead())
    return lbe_expression(instruction.dead_symbol()) ||
           logical_declaration(instruction.dead_symbol());
  if(instruction.is_assign())
    return (instruction.assign_lhs().id() == ID_symbol ||
            (optimizations.array_blocks &&
             instruction.assign_lhs().id() == ID_index &&
             memory.logical_arrays.owns_lvalue(instruction.assign_lhs()))) &&
           lbe_expression(instruction.assign_lhs()) &&
           lbe_expression(instruction.assign_rhs());
  if(optimizations.scalar_blocks && instruction.is_assert())
    return lbe_expression(instruction.condition());
  if(instruction.is_goto())
  {
    if(
      instruction.targets.size() != 1 ||
      !lbe_expression(instruction.condition()))
      return false;
    if(!optimizations.scalar_blocks)
      for(auto successor : info.successors)
        if(successor <= loc)
          return false;
    return true;
  }
  return instruction.is_skip() || instruction.is_location();
}

void goto_to_btor2_convertert::plan_blocks()
{
  std::map<unsigned, std::set<unsigned>> predecessors;
  for(const auto &[loc, info] : locations)
    for(auto successor : info.successors)
      predecessors[successor].insert(loc);

  const auto terminal = [&](unsigned loc)
  {
    if(!optimizations.scalar_blocks)
      return false;
    if(locations.at(loc).instruction->is_assert())
      return true;
    for(const auto successor : locations.at(loc).successors)
      if(successor <= loc)
        return true;
    return false;
  };

  // Each contiguous region has one entry, no internal backward edge and no
  // external incoming edge to its interior. Its exits may target any block.
  // A size limit bounds formula growth without imposing a program loop bound.
  for(unsigned entry = 0; entry < locations.size();)
  {
    std::vector<unsigned> block{entry};
    if(
      (large_block_encoding || optimizations.scalar_blocks) &&
      lbe_instruction(entry) && !terminal(entry))
      for(unsigned loc = entry + 1; loc < locations.size() && block.size() < 64;
          ++loc)
      {
        if(!lbe_instruction(loc))
          break;
        bool external_entry = false;
        for(auto predecessor : predecessors[loc])
          if(predecessor < entry || predecessor >= loc)
            external_entry = true;
        if(external_entry)
          break;
        block.push_back(loc);
        if(terminal(loc))
          break;
      }
    for(auto loc : block)
      location_to_block[loc] = blocks.size();
    entry = block.back() + 1;
    blocks.push_back(std::move(block));
  }
  if(large_block_encoding || optimizations.scalar_blocks)
    log.status() << "Scalar LBE: " << locations.size() << " instructions -> "
                 << blocks.size() << " blocks (maximum 64 instructions)"
                 << messaget::eom;
}

void goto_to_btor2_convertert::process_block(const std::vector<unsigned> &block)
{
  using environmentt = std::map<irep_idt, btor2_nid_t>;
  struct incomingt
  {
    btor2_nid_t guard;
    environmentt values;
    logical_arrayst::valuest storage;
  };
  const auto entry = block.front();
  const auto sort = builder.get_bool_sort();
  const auto at_block = make_pc_equals(entry);
  const auto active = at_block;
  if(optimizations.array_blocks)
    memory.begin(entry, at_block);
  const auto initial_storage = optimizations.array_blocks
                                 ? memory.logical_arrays.values()
                                 : logical_arrayst::valuest{};
  environmentt initial;
  for(const auto &id : variable_order)
  {
    const auto &variable = variables.at(id);
    initial[id] = variable.state_nid ? variable.state_nid : variable.local_nid;
  }
  auto bind =
    [&](const environmentt &values, const logical_arrayst::valuest &storage)
  {
    expr_converter.clear_caches();
    for(const auto &[id, value] : values)
      expr_converter.register_symbol(id, value, variables.at(id).type);
    if(optimizations.array_blocks)
      memory.logical_arrays.bind(storage);
  };
  std::map<unsigned, std::vector<incomingt>> incoming;
  incoming[entry].push_back({builder.one(sort), initial, initial_storage});
  if(!optimizations.array_blocks)
    memory.begin(entry, at_block);
  builder.comment(
    "Scalar LBE block " + std::to_string(location_to_block.at(entry)));
  for(auto loc : block)
  {
    auto &info = locations[loc];
    const auto input_start = expr_converter.event_inputs().size();
    info.first_node = builder.get_node_count() + 1;
    auto values = initial;
    auto storage = initial_storage;
    auto reach = builder.zero(sort);
    // Incoming paths are disjoint. All RHSs and branch conditions below use
    // the latest values on those paths, including assignments in this step.
    bool first = true;
    for(const auto &path : incoming[loc])
    {
      if(first)
      {
        values = path.values;
        storage = path.storage;
      }
      else
      {
        for(const auto &[id, value] : path.values)
          if(values[id] != value)
            values[id] = builder.ite(
              variables.at(id).sort_nid, path.guard, value, values[id]);
        for(const auto &[state, value] : path.storage)
          if(storage.at(state) != value)
            storage[state] = builder.ite(
              memory.logical_arrays.state_sorts().at(state),
              path.guard,
              value,
              storage.at(state));
      }
      first = false;
      reach = builder.lor(sort, reach, path.guard);
    }
    info.pc_guard = builder.land(sort, active, reach);
    bind(values, storage);
    if(optimizations.array_blocks)
      memory.logical_arrays.set_location(loc);
    const auto &instruction = *info.instruction;
    if(instruction.is_decl())
    {
      const auto id = instruction.decl_symbol().get_identifier();
      if(optimizations.array_blocks && memory.logical_arrays.owns_symbol(id))
      {
        memory.declaration(instruction.decl_symbol(), false);
        storage = memory.logical_arrays.values();
      }
      else
      {
        const auto &variable = variables.at(id);
        const auto value =
          builder.input(variable.sort_nid, variable.name + "_decl");
        values[id] = value;
        info.value_node = value;
        info.value_sort = variable.sort_nid;
        info.input_nodes.push_back(value);
      }
    }
    if(
      instruction.is_dead() && optimizations.array_blocks &&
      memory.logical_arrays.owns_symbol(
        instruction.dead_symbol().get_identifier()))
      memory.declaration(instruction.dead_symbol(), true);
    if(instruction.is_assign())
    {
      if(
        optimizations.array_blocks &&
        memory.logical_arrays.owns_lvalue(instruction.assign_lhs()))
      {
        if(
          !memory.logical_arrays.assign(
            instruction.assign_lhs(),
            instruction.assign_rhs(),
            info.value_node) ||
          memory.logical_arrays.failed)
        {
          conversion_error(
            "Cannot convert logical array block assignment at " +
            std::to_string(loc) + ": " + memory.logical_arrays.failure_reason);
          break;
        }
        info.value_sort =
          expr_converter.convert_type(instruction.assign_lhs().type());
        if(!instruction.source_location().get("c2btor_nondet_summary_group").empty())
          info.summary_input_node = memory.logical_arrays.last_nondet_input();
        storage = memory.logical_arrays.values();
      }
      else
      {
        const auto id =
          to_symbol_expr(instruction.assign_lhs()).get_identifier();
        auto value = expr_converter.convert(instruction.assign_rhs());
        if(!value)
        {
          conversion_error(
            "Cannot convert scalar LBE assignment at " + std::to_string(loc));
          break;
        }
        values[id] = value;
        info.value_node = value;
        info.value_sort = variables.at(id).sort_nid;
      }
    }
    if(memory.failed || memory.logical_arrays.failed)
    {
      conversion_error("Cannot convert logical array block declaration");
      break;
    }
    if(instruction.is_assert())
    {
      auto condition = expr_converter.convert(instruction.condition());
      if(!condition)
      {
        conversion_error(
          "Cannot convert scalar LBE assertion at " + std::to_string(loc));
        break;
      }
      // Freeze the predicate at this execution point. A skipped assertion's
      // pc_guard is false, and ASSERT never restricts the outgoing path.
      assertions.push_back(
        assertion_infot{
          loc,
          instruction.condition(),
          btor2_make_bad_property_name(loc, instruction.source_location()),
          condition});
    }
    auto edge = [&](unsigned target, btor2_nid_t guard)
    {
      if(target > loc && target >= entry && target <= block.back())
        incoming[target].push_back({guard, values, storage});
      else
      {
        auto enabled = builder.land(sort, active, guard);
        pc_updates[entry].push_back({enabled, target});
        if(optimizations.array_blocks)
          memory.logical_arrays.commit(enabled, storage);
        for(const auto &[id, value] : values)
          if(variables.at(id).state_nid && value != initial.at(id))
          {
            if(optimizations.scalar_blocks && block_candidate_symbols.count(id))
            {
              const auto live = block_liveness.entry_live.find(target);
              if(
                live != block_liveness.entry_live.end() &&
                !live->second.count(id))
                continue;
            }
            state_updates[id].push_back({enabled, value});
          }
      }
    };
    if(instruction.is_goto())
    {
      auto condition = expr_converter.convert(instruction.condition());
      if(!condition)
      {
        conversion_error(
          "Cannot convert scalar LBE branch at " + std::to_string(loc));
        break;
      }
      edge(
        get_target_location(instruction.targets.front()),
        builder.land(sort, reach, condition));
      if(!instruction.condition().is_true())
        edge(loc + 1, builder.land(sort, reach, builder.lnot(sort, condition)));
    }
    else
      edge(loc + 1, reach);
    const auto &event_inputs = expr_converter.event_inputs();
    info.input_nodes.insert(info.input_nodes.end(), event_inputs.begin() + input_start, event_inputs.end());
    info.last_node = builder.get_node_count();
  }
  bind(initial, initial_storage);
  // Each outgoing path already committed its own storage and dimensions.
  // Restoring state identities makes memory.end's automatic commit a no-op.
  memory.end();
}

void goto_to_btor2_convertert::emit_lbe_observations()
{
  for(auto loc : location_order)
  {
    auto &info = locations[loc];
    const auto executed = info.pc_guard;
    info.executed_output = builder.observed_output(
      builder.get_bool_sort(),
      executed,
      "__c2btor_exec_" + std::to_string(loc));
    if(info.value_node && builder.is_bitvec_sort(info.value_sort))
      info.value_output = builder.observed_output(
        info.value_sort,
        info.value_node,
        "__c2btor_value_" + std::to_string(loc));
  }
}
