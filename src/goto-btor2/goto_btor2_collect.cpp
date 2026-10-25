// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

// One scalar state per value; all addressable objects use shared byte memory.
#include <util/find_symbols.h>
#include <util/symbol.h>

#include "btor2_type_utils.h"
#include "goto_btor2_converter.h"

#include <cctype>
namespace
{
std::string normalize_name(const irep_idt &id)
{
  std::string name = id2string(id);

  std::string::size_type pos = name.rfind("::");
  if(pos != std::string::npos)
    name = name.substr(pos + 2);

  // The witness reader recognises the converter's program counter as "pc".
  if(name == "pc")
    name = "pc__2";

  for(char &ch : name)
  {
    if(!std::isalnum(ch) && ch != '_')
      ch = '_';
  }

  return name;
}

} // namespace

bool goto_to_btor2_convertert::collect_variables()
{
  find_symbols_sett referenced;
  referenced.insert(
    scalar_projection_report.forced_static_symbols.begin(),
    scalar_projection_report.forced_static_symbols.end());
  for(const auto &instruction : program.instructions)
  {
    find_symbols(instruction.code(), referenced);
    if(instruction.has_condition())
      find_symbols(instruction.condition(), referenced);
  }
  for(const auto &id : referenced)
  {
    const symbolt *symbol = nullptr;
    if(
      ns.lookup(id, symbol) || !symbol || symbol->is_type ||
      symbol->type.id() == ID_code || memory.owns_symbol(id))
      continue;
    variable_infot var;
    var.id = id;
    var.name = normalize_name(id);
    var.type = var.logical_type = follow_tag_type(symbol->type, ns);
    if(memory.logical_records.count(id))
    {
      for(const auto &field : to_struct_type(var.type).components())
      {
        auto element = var;
        element.id = id2string(id) + "." + id2string(field.get_name());
        element.name = normalize_name(element.id);
        element.type = element.logical_type = field.type();
        variable_order.push_back(element.id);
        variables.emplace(element.id, std::move(element));
      }
      continue;
    }
    if(!expr_converter.get_width(var.type))
    {
      conversion_error("Unsupported scalar state: " + id2string(id));
      continue;
    }
    var.has_initializer =
      symbol->is_static_lifetime && symbol->value.is_not_nil();
    var.initializer = symbol->value;
    variables.emplace(id, std::move(var));
    variable_order.push_back(id);
  }
  log.status() << "Collected " << variables.size() << " scalar states and "
               << memory.heap.objects.size() << " memory objects"
               << messaget::eom;
  return !conversion_had_errors;
}

bool goto_to_btor2_convertert::collect_locations()
{
  unsigned loc_num = 0;

  // 第一遍：为每个指令分配位置编号
  std::set<unsigned> target_locs;
  instruction_to_loc.clear();
  instruction_to_loc.reserve(program.instructions.size());
  for(auto it = program.instructions.begin(); it != program.instructions.end();
      ++it, ++loc_num)
  {
    location_infot info;
    info.loc_number = loc_num;
    info.instruction = it;
    info.is_target = it->is_target();

    locations[loc_num] = info;
    location_order.push_back(loc_num);
    instruction_to_loc[&*it] = loc_num;
  }

  // 第二遍：填充后继信息，识别循环头
  for(auto &[loc, info] : locations)
  {
    const auto &instr = *info.instruction;

    if(instr.is_goto())
    {
      // 条件跳转：有两个后继（目标和 fall-through）
      if(!instr.condition().is_true())
      {
        info.successors.push_back(
          loc + 1 < locations.size() ? loc + 1 : loc); // encoded fall-through
      }

      if(instr.targets.empty())
        info.successors.push_back(loc);

      // 处理跳转目标
      for(const auto &target : instr.targets)
      {
        unsigned target_loc = 0;
        auto map_it = instruction_to_loc.find(&*target);
        if(map_it != instruction_to_loc.end())
          target_loc = map_it->second;
        info.successors.push_back(target_loc);

        // 后向边检测（循环检测）
        if(target_loc <= loc)
        {
          locations[target_loc].is_loop_head = true;
        }
      }
    }
    else if(instr.is_end_function())
    {
      // The converter advances END_FUNCTION, then self-loops at the end.
      info.successors.push_back(loc + 1 < locations.size() ? loc + 1 : loc);
    }
    else
    {
      // 顺序执行：后继是下一条指令
      if(loc + 1 < locations.size())
      {
        info.successors.push_back(loc + 1);
      }
      else
        info.successors.push_back(loc);
    }
  }

  log.status() << "Collected " << locations.size() << " locations"
               << messaget::eom;
  return true;
}

//===========================================================================
// VLA 上界提取
//===========================================================================

void goto_to_btor2_convertert::classify_block_states()
{
  find_symbols_sett forced;
  // Initializers are evaluated outside the runtime block environment.
  for(const auto &entry : variables)
    if(entry.second.has_initializer)
      find_type_and_expr_symbols(entry.second.initializer, forced);
  for(const auto &entry : memory.heap.objects)
    if(entry.second.static_lifetime)
      find_type_and_expr_symbols(entry.second.initializer, forced);
  // Follow namespace type tags as well as direct initializer dimensions.
  find_symbols_sett checked;
  for(;;)
  {
    auto pending = forced;
    bool changed = false;
    for(const auto &id : pending)
      if(checked.insert(id).second)
      {
        changed = true;
        const symbolt *symbol = nullptr;
        if(!ns.lookup(id, symbol) && symbol)
          find_type_and_expr_symbols(symbol->type, forced);
      }
    if(!changed)
      break;
  }
  // Singleton nondet calls retain result states for source-map replay.
  for(const auto &instruction : program.instructions)
  {
    const exprt *lhs = nullptr;
    if(instruction.is_function_call())
      lhs = &instruction.call_lhs();
    else if(instruction.is_assign() &&
            instruction.assign_rhs().id() == ID_side_effect)
      lhs = &instruction.assign_lhs();
    if(lhs)
      find_symbols(*lhs, forced);
  }
  for(const auto &id : variable_order)
  {
    const auto &var = variables.at(id);
    const symbolt *symbol = nullptr;
    const auto type_id = var.type.id();
    if(!forced.count(id) && !ns.lookup(id, symbol) && symbol &&
       !symbol->is_static_lifetime && !var.has_initializer &&
       !var.scalarized_fixed_array && !var.type.get_bool(ID_C_volatile) &&
       !var.type.get_bool(ID_C_atomic) &&
       (type_id == ID_bool || type_id == ID_c_bool ||
        type_id == ID_signedbv || type_id == ID_unsignedbv))
      block_candidate_symbols.insert(id);
  }
  std::map<unsigned, std::vector<unsigned>> successors;
  for(const auto &entry : locations)
    successors.emplace(entry.first, entry.second.successors);
  block_liveness = classify_scalar_block_state(
    program, ns, blocks, block_candidate_symbols, successors);
  log.status() << "Scalar block liveness: "
               << block_liveness.local_symbols.size()
               << " automatic values need no state" << messaget::eom;
}
