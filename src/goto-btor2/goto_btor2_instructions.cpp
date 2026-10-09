/*******************************************************************\

Module: Goto 程序到 BTOR2 的转换 - 指令处理

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// Goto 指令到 BTOR2 状态更新的转换
///
/// 本文件实现了 goto 程序中各类指令的转换逻辑。每条 goto 指令在 BTOR2
/// 中被建模为条件状态更新：当 PC 等于当前位置编号时执行相应的操作。
///
/// 指令转换规则：
/// - ASSIGN: 生成条件状态更新（state_updates）
/// - GOTO:   生成条件 PC 更新（pc_updates），条件跳转产生分支
/// - ASSERT: 记录断言信息，稍后生成 bad 属性
/// - ASSUME: 同时产生两个效果（且关系）：
///   (a) 记录假设信息，稍后生成 constraint（全局约束）；
///   (b) 限制 PC 转移，仅当条件成立时才推进到下一条指令
/// - FUNCTION_CALL: 处理 nondet/malloc/abort/__assert_fail 等特殊函数
/// - 其他: 仅生成 PC 递增（fall-through）

#include "goto_btor2_converter.h"
#include "btor2_type_utils.h"

#include "btor2_builder.h"
#include "expr_to_btor2.h"

#include <goto-programs/goto_functions.h>
#include <langapi/language_util.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/find_symbols.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <algorithm>
#include <sstream>
#include <cmath>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <unordered_map>
#include <vector>
#include <cctype>

namespace
{

bool is_verifier_nondet_function(const exprt &function)
{
  if(function.id() != ID_symbol)
    return false;
  const auto &id = to_symbol_expr(function).get_identifier();
  const std::string name = id2string(id);
  if(name == "__VERIFIER_nondet_int")
    return true;
  if(name.rfind("__VERIFIER_nondet_", 0) == 0)
    return true;
  if(name.rfind("__CPROVER_nondet_", 0) == 0)
    return true;
  return false;
}

std::optional<irep_idt> get_function_identifier(const exprt &function)
{
  if(function.id() == ID_symbol)
    return to_symbol_expr(function).get_identifier();

  if(function.id() == ID_address_of)
  {
    const exprt &obj = to_address_of_expr(function).object();
    if(obj.id() == ID_symbol)
      return to_symbol_expr(obj).get_identifier();
  }

  return std::nullopt;
}

bool matches_function_name(const irep_idt &id, const std::string &name)
{
  const std::string s = id2string(id);
  if(s == name)
    return true;

  const std::string suffix = "::" + name;
  if(s.size() >= suffix.size() &&
     s.compare(s.size() - suffix.size(), suffix.size(), suffix) == 0)
    return true;

  return false;
}

}

void goto_to_btor2_convertert::process_instructions()
{
  builder.comment("");
  builder.comment("Instruction processing");

  for(const auto &loc : location_order)
  {
    auto &info = locations[loc];
    const auto &instr = *info.instruction;
    info.first_node = builder.get_node_count() + 1;

    // at_loc 表示 PC == loc（当前是否在此位置）
    btor2_nid_t at_loc = make_pc_equals(loc);
    info.pc_guard = at_loc;
    expr_converter.clear_caches();
    memory.heap.begin(loc, at_loc);

    // 根据指令类型分派处理
    switch(instr.type())
    {
    case ASSIGN:
      process_assign(loc, at_loc, instr);
      break;

    case GOTO:
      process_goto(loc, at_loc, instr);
      break;

    case ASSERT:
      process_assert(loc, at_loc, instr);
      break;

    case ASSUME:
      process_assume(loc, at_loc, instr);
      break;

    // 以下指令不产生状态更新，只是 PC 递增
    case DECL:
      memory.declaration(instr.decl_symbol(), false);
      if(!memory.owns_lvalue(instr.decl_symbol()))
      {
        const auto id = instr.decl_symbol().get_identifier();
        const auto variable = variables.find(id);
        if(variable != variables.end())
          state_updates[id].push_back({at_loc, builder.input(
            variable->second.sort_nid, variable->second.name + "_decl")});
      }
      add_pc_fallthrough(loc, at_loc);
      break;
    case DEAD:
      memory.declaration(instr.dead_symbol(), true);
      add_pc_fallthrough(loc, at_loc);
      break;
    case SKIP:        // 空操作
    case LOCATION:    // 位置标记
    case END_FUNCTION: // 函数结束
    case SET_RETURN_VALUE: // 仅影响调用者；当前转换 main 可忽略
      add_pc_fallthrough(loc, at_loc);
      break;

    case FUNCTION_CALL:
      process_function_call(loc, at_loc, instr);
      break;

    case OTHER:
      if(instr.get_other().get_statement() == "c2btor_unlowered_recursion")
      {
        conversion_error(
          "Unsupported recursive frame in " +
          id2string(instr.get_other().get("function")) +
          "; recursion was not lowered, no model will be emitted");
        break;
      }
      if(instr.get_other().get_statement() == "c2btor_copy_check")
      {
        const auto &code = instr.get_other();
        auto destination = expr_converter.convert(code.op0());
        auto source = expr_converter.convert(code.op1());
        auto size = expr_converter.convert(typecast_exprt::conditional_cast(
          code.operands()[2], unsignedbv_typet(memory.heap.pointer_bits)));
        if(!destination || !source || !size)
          conversion_error("Cannot normalize memory copy arguments");
        else
        {
          auto &heap = memory.heap;
          auto sort = builder.get_bool_sort();
          heap.require(heap.accessible(source, size, false));
          heap.require(heap.accessible(destination, size, true));
          if(!code.get_bool("allow_overlap"))
          {
            // Bounds above ensure these nonnegative sums cannot wrap.
            auto separate = builder.neq(sort, heap.tag(source), heap.tag(destination));
            separate = builder.lor(sort, separate, builder.ulte(sort,
              builder.add(heap.pointer_sort, source, size), destination));
            separate = builder.lor(sort, separate, builder.ulte(sort,
              builder.add(heap.pointer_sort, destination, size), source));
            heap.require(separate);
          }
        }
        add_pc_fallthrough(loc, at_loc);
        break;
      }
      if(instr.get_other().get_statement() == "c2btor_copy_range")
      {
        const auto &code = instr.get_other();
        auto destination = expr_converter.convert(code.op0());
        auto source = expr_converter.convert(code.op1());
        auto size = expr_converter.convert(typecast_exprt::conditional_cast(
          code.operands()[2], unsignedbv_typet(memory.heap.pointer_bits)));
        if(destination && source && size)
          memory.heap.copy_range(destination, source, size);
        else
          conversion_error("Cannot normalize range copy");
        add_pc_fallthrough(loc, at_loc);
        break;
      }
      if(instr.get_other().get_statement() == "c2btor_copy_byte")
      {
        auto destination = expr_converter.convert(instr.get_other().op0());
        auto source = expr_converter.convert(instr.get_other().op1());
        if(destination && source)
          memory.heap.copy_byte(destination, source);
        else
          conversion_error("Cannot normalize byte copy");
        add_pc_fallthrough(loc, at_loc);
        break;
      }
      if(instr.get_other().get_statement() == "c2btor_deallocate")
      {
        const auto pointer = expr_converter.convert(instr.get_other().op0());
        if(pointer)
          memory.heap.deallocate(pointer);
        else
          conversion_error("Cannot lower deallocation pointer");
        add_pc_fallthrough(loc, at_loc);
        break;
      }
      if(
        instr.get_other().get_statement() == ID_array_copy ||
        instr.get_other().get_statement() == ID_array_replace ||
        instr.get_other().get_statement() == ID_array_set ||
        instr.get_other().get_statement() == ID_havoc_object)
      {
        conversion_error(
          "Unsupported memory operation at location " + std::to_string(loc) +
          ": " + id2string(instr.get_other().get_statement()) + " (" +
          instr.source_location().as_string() + ")");
        add_pc_fallthrough(loc, at_loc);
        break;
      }
      if(
        instr.get_other().get_statement() == ID_expression ||
        instr.get_other().get_statement() == ID_input ||
        instr.get_other().get_statement() == ID_output)
      {
        add_pc_fallthrough(loc, at_loc);
        break;
      }
      conversion_error("Unsupported OTHER statement: " +
        id2string(instr.get_other().get_statement()));
      break;

    case ATOMIC_BEGIN:
    case ATOMIC_END:
      add_pc_fallthrough(loc, at_loc);
      break;

    // 不支持的指令类型
    case NO_INSTRUCTION_TYPE:
    case START_THREAD:   // 多线程不支持
    case END_THREAD:
    case THROW:          // 异常不支持
    case CATCH:
    case INCOMPLETE_GOTO:
    {
      std::ostringstream oss;
      oss << "Unsupported instruction type at location " << loc << ": "
          << instr.type();
      if(instr.type() == OTHER)
        oss << " statement=" << instr.get_other().get_statement();
      conversion_error(oss.str());
      add_pc_fallthrough(loc, at_loc);
      break;
    }
    }
    memory.heap.end();
    info.last_node = builder.get_node_count();
  }
}

void goto_to_btor2_convertert::process_function_call(
  unsigned loc,
  btor2_nid_t at_loc,
  const goto_programt::instructiont &instr)
{
  const exprt &function = instr.call_function();
  if(is_verifier_nondet_function(function))
  {
    const exprt &lhs = instr.call_lhs();
    if(lhs.id() != ID_symbol)
    {
      conversion_error("nondet call with non-symbol LHS not supported");
      add_pc_fallthrough(loc, at_loc);
      return;
    }

    const irep_idt &var_id = to_symbol_expr(lhs).get_identifier();
    auto it = variables.find(var_id);
    if(it == variables.end())
    {
      conversion_error("Unknown variable for nondet call LHS: " + id2string(var_id));
      add_pc_fallthrough(loc, at_loc);
      return;
    }

    auto &var = it->second;
    // Create (or reuse) a BTOR2 input providing a fresh value each step.
    auto in_it = nondet_inputs.find(var_id);
    btor2_nid_t input_nid = 0;
    if(in_it == nondet_inputs.end())
    {
      input_nid =
        builder.input(var.sort_nid, var.name + "_nondet");
      nondet_inputs.emplace(var_id, input_nid);
    }
    else
    {
      input_nid = in_it->second;
    }

    state_updates[var_id].push_back({at_loc, input_nid});
    add_pc_fallthrough(loc, at_loc);
    return;
  }

  if(auto fid = get_function_identifier(function))
  {
    if(*fid == "sprintf" && function.id() == ID_symbol &&
       process_sprintf_hex(loc, at_loc, instr))
      return;
    if(matches_function_name(*fid, "malloc") ||
       matches_function_name(*fid, "calloc"))
    {
      // Failure, size overflow and calloc initialization are modeled by the
      // CBMC library. A bare always-successful allocation is not C malloc.
      conversion_error("Heap allocation call requires --inline and the CBMC library model");
      heap_modeling_incomplete = true;
      add_pc_fallthrough(loc, at_loc);
      return;
    }

    if(matches_function_name(*fid, "abort"))
    {
      // abort(): C 语义为程序终止，但路径在到达 abort 前是合法执行前缀。
      // 编码为终态自环：PC 到达 loc 后停留在 loc（可达但无前进迁移），
      // 而非全局 constraint（后者会错误地排除该路径，对可达性性质不可靠）。
      pc_updates[loc].push_back({at_loc, loc});
      return;
    }

    if(
      matches_function_name(*fid, "__assert_fail") ||
      matches_function_name(*fid, "reach_error"))
    {
      // __assert_fail / reach_error: property violation。
      // 编码为 bad 状态 + 终态自环（与 assert 失败一致：路径终止）。
      assertions.push_back(assertion_infot{
        loc,
        false_exprt(),
        btor2_make_bad_property_name(loc, instr.source_location())});
      pc_updates[loc].push_back({at_loc, loc});
      return;
    }
  }

  // A missing body may modify memory even when it has no return value.
  // Reject it independently of whether an unknown return input is emitted.
  conversion_error(
    "Unsupported call at location " + std::to_string(loc) + ": " +
    from_expr(ns, "", instr.call_function()) + " (" +
    instr.source_location().as_string() + ")");
  const exprt &lhs = instr.call_lhs();
  if(lhs.is_not_nil())
  {
    if(lhs.id() == ID_symbol)
    {
      const irep_idt &var_id = to_symbol_expr(lhs).get_identifier();
      auto it = variables.find(var_id);
      if(it != variables.end())
      {
        auto &var = it->second;
        if(var.scalarized_fixed_array && var.type.id() == ID_array)
        {
          const auto &array_type = to_array_type(var.type);
          for(const auto &elem_id : var.scalar_element_ids)
          {
            btor2_nid_t value =
              fresh_unknown(array_type.element_type(), "__unknown_call");
            if(value != 0)
              state_updates[elem_id].push_back({at_loc, value});
          }
        }
        else if(var.sort_nid != 0 && var.state_nid != 0)
        {
          btor2_nid_t value = fresh_unknown(var.type, "__unknown_call");
          if(value != 0)
            state_updates[var_id].push_back({at_loc, value});
        }
      }
    }
  }

  // Diagnostic output only: the return is unconstrained, but memory effects
  // are not modelled, so the conversion above has been marked as failed.
  add_pc_fallthrough(loc, at_loc);
}

void goto_to_btor2_convertert::process_goto(
  unsigned loc,
  btor2_nid_t at_loc,
  const goto_programt::instructiont &instr)
{
  const exprt &guard = instr.condition();
  const btor2_nid_t bool_sort = builder.get_bool_sort();

  // 跳转条件（无条件跳转时为 at_loc，条件跳转时为 at_loc ∧ guard）
  btor2_nid_t branch_guard;
  if(guard.is_true())
  {
    branch_guard = at_loc;
  }
  else
  {
    btor2_nid_t guard_nid = expr_converter.convert(guard);
    if(guard_nid == 0)
    {
      log.error() << "Unsupported guard at location " << loc << ": "
                  << from_expr(ns, "", guard) << " ("
                  << instr.source_location() << ")" << messaget::eom;
      guard_nid = fresh_unknown_bool("__unknown_guard");
    }
    branch_guard = builder.land(bool_sort, at_loc, guard_nid);
  }

  if(instr.targets.empty())
  {
    // 无目标：停机（自环）。
    pc_updates[loc].push_back({at_loc, loc});
  }
  else if(instr.targets.size() == 1)
  {
    // 单目标（常见情况）：直接跳转。
    unsigned target_loc = get_target_location(instr.targets.front());
    pc_updates[loc].push_back({branch_guard, target_loc});
  }
  else
  {
    // 多目标 GOTO（罕见：switch jump table、computed goto 残留等）。
    // 不能让所有目标共用同一守卫——逆序 ITE 链中只有第一个目标会生效。
    // 正确编码：用 fresh boolean 输入创建互斥守卫，确保每个目标可达。
    //
    //   g1 = branch_guard ∧ choice_1
    //   g2 = branch_guard ∧ ¬choice_1 ∧ choice_2
    //   g3 = branch_guard ∧ ¬choice_1 ∧ ¬choice_2
    //   ...
    warn("Multi-target GOTO at location " + std::to_string(loc) + " (" +
         std::to_string(instr.targets.size()) +
         " targets); encoding as nondeterministic choice");

    btor2_nid_t remaining = branch_guard;
    std::size_t target_idx = 0;
    for(auto target_it = instr.targets.begin();
        target_it != instr.targets.end();
        ++target_it, ++target_idx)
    {
      unsigned target_loc = get_target_location(*target_it);
      auto next_it = std::next(target_it);

      if(next_it == instr.targets.end())
      {
        // 最后一个目标：使用剩余守卫（确保穷尽性）
        pc_updates[loc].push_back({remaining, target_loc});
      }
      else
      {
        btor2_nid_t choice =
          fresh_unknown_bool("__goto_choice_" + std::to_string(target_idx));
        btor2_nid_t take = builder.land(bool_sort, remaining, choice);
        btor2_nid_t skip = builder.land(bool_sort, remaining, builder.lnot(bool_sort, choice));
        pc_updates[loc].push_back({take, target_loc});
        remaining = skip;
      }
    }
  }

  // 条件跳转的 fall-through
  if(!guard.is_true())
  {
    btor2_nid_t guard_nid = expr_converter.convert(guard);
    if(guard_nid == 0)
      guard_nid = fresh_unknown_bool("__unknown_guard");
    btor2_nid_t not_guard = builder.lnot(bool_sort, guard_nid);
    btor2_nid_t fall_through = builder.land(bool_sort, at_loc, not_guard);
    pc_updates[loc].push_back({fall_through, loc + 1});
  }
}

void goto_to_btor2_convertert::process_assert(
  unsigned loc,
  btor2_nid_t at_loc,
  const goto_programt::instructiont &instr)
{
  assertions.push_back(assertion_infot{
    loc,
    instr.condition(),
    btor2_make_bad_property_name(loc, instr.source_location())});

  // C 语义：assert(c) 失败时调用 abort，程序终止。
  // 编码为：仅当条件成立时 PC 才推进到 loc+1；条件为假时 PC 停滞在 loc
  // （自环），且 bad 被触发。这样断言失败后不会产生"僵尸路径"继续执行
  // 下游指令并触发其他 bad，避免复合反例。
  //
  // 注意：cond_nid 必须与 generate_properties 中的 bad 谓词使用同一节点，
  // 否则当条件转换失败（fallback 为 fresh input）时，PC 守卫与 bad 谓词
  // 会引用不同的 input，破坏"assert 失败则 halt"不变量。
  btor2_nid_t cond_nid = expr_converter.convert(instr.condition());
  if(cond_nid == 0)
    cond_nid = fresh_unknown_bool("__unknown_assert_cond");

  // 存入 assertion_infot，供 generate_properties 复用
  if(!assertions.empty() && assertions.back().loc_number == loc)
    assertions.back().cond_nid = cond_nid;

  btor2_nid_t bool_sort = builder.get_bool_sort();
  // proceed = at_loc && cond
  btor2_nid_t proceed = builder.land(bool_sort, at_loc, cond_nid);

  if(loc + 1 < locations.size())
    pc_updates[loc].push_back({proceed, loc + 1});
  else
    pc_updates[loc].push_back({proceed, loc});
}

void goto_to_btor2_convertert::process_assume(
  unsigned loc,
  btor2_nid_t at_loc,
  const goto_programt::instructiont &instr)
{
  // 保存假设信息
  assumptions.push_back({loc, instr.condition()});

  // 只有假设成立时才继续执行
  btor2_nid_t cond_nid = expr_converter.convert(instr.condition());
  if(cond_nid == 0)
    cond_nid = fresh_unknown_bool("__unknown_assume");

  btor2_nid_t bool_sort = builder.get_bool_sort();
  // can_proceed = at_loc && condition
  btor2_nid_t can_proceed = builder.land(bool_sort, at_loc, cond_nid);
  pc_updates[loc].push_back({can_proceed, loc + 1});

  // 如果假设失败，可以建模为停止（保持当前位置）
  // 或作为隐式约束
}

void goto_to_btor2_convertert::add_pc_fallthrough(unsigned loc, btor2_nid_t at_loc)
{
  if(loc + 1 < locations.size())
  {
    // 跳转到下一位置
    pc_updates[loc].push_back({at_loc, loc + 1});
  }
  else
  {
    // 程序结束，保持当前位置
    pc_updates[loc].push_back({at_loc, loc});
  }
}

unsigned goto_to_btor2_convertert::get_target_location(goto_programt::const_targett target)
{
  auto it = instruction_to_loc.find(&*target);
  if(it != instruction_to_loc.end())
    return it->second;
  return 0;
}
