/*******************************************************************\

Module: Goto 程序到 BTOR2 的转换 - 实现

Author: Based on CBMC project

\*******************************************************************/

#include "goto_btor2.h"
#include "goto_btor2_converter.h"
#include "btor2_type_utils.h"

#include <goto-programs/goto_functions.h>
#include <util/arith_tools.h>
#include <util/config.h>
#include <util/json.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <langapi/language_util.h>

#include <cmath>
#include <optional>
#include <sstream>

namespace
{

std::size_t pc_width(std::size_t num_locations)
{
  if(num_locations <= 1)
    return 1;
  // ceil(log2(n)) 计算表示 n 个值所需的位数
  return static_cast<std::size_t>(std::ceil(std::log2(num_locations)));
}


} // namespace

//===========================================================================
// Method implementations
//===========================================================================

void goto_to_btor2_convertert::warn(const std::string &msg)
{
  log.warning() << msg << messaget::eom;
  if(emit_warning_comments)
    builder.comment("WARNING: " + msg);
}

void goto_to_btor2_convertert::conversion_error(const std::string &msg)
{
  conversion_had_errors = true;
  log.error() << msg << messaget::eom;
  // Retain the diagnostic internally; failed conversions emit no model.
  builder.comment("ERROR: " + msg);
}

btor2_nid_t goto_to_btor2_convertert::fresh_unknown(
  const typet &type,
  const std::string &prefix)
{
  conversion_error("introduced unsupported fallback input " + prefix);
  btor2_nid_t sort = expr_converter.convert_type(type);
  if(sort == 0)
    return 0;

  return builder.input(
    sort, prefix + "$" + std::to_string(unknown_counter++));
}

btor2_nid_t goto_to_btor2_convertert::fresh_unknown_bool(
  const std::string &prefix)
{
  if(prefix.rfind("__unknown", 0) == 0)
    conversion_error("introduced unsupported fallback input " + prefix);
  return builder.input(
    builder.get_bool_sort(),
    prefix + "$" + std::to_string(unknown_counter++));
}

bool goto_to_btor2_convertert::convert(
  std::ostream &out, std::ostream *source_map)
{
  // 检查程序是否为空
  if(program.instructions.empty())
  {
    log.error() << "Empty program" << messaget::eom;
    return true;
  }

  // 添加注释头
  builder.comment("BTOR2 generated from goto-program");
  builder.comment("c2btor-proof-contract 1");
  builder.comment("");

  //-------------------------------------------------------------------------
  // 阶段 1: 收集变量和位置
  //-------------------------------------------------------------------------
  memory.collect(program);
  if(memory.failed)
    return true;
  if(!collect_variables())
    return true;

  if(!collect_locations())
    return true;

  memory.create_states();
  if(memory.failed)
    return true;
  expr_converter.set_memory(&memory);

  //-------------------------------------------------------------------------
  // 阶段 2: 创建 BTOR2 类型和状态
  //-------------------------------------------------------------------------
  create_sorts();
  create_states();
  memory.initialize_static();

  //-------------------------------------------------------------------------
  // 阶段 3: 创建程序计数器状态
  //-------------------------------------------------------------------------
  create_pc_state();

  //-------------------------------------------------------------------------
  // 阶段 4: 处理指令，收集状态更新
  //-------------------------------------------------------------------------
  process_instructions();

  //-------------------------------------------------------------------------
  // 阶段 5: 生成 next 状态转换函数
  //-------------------------------------------------------------------------
  generate_transitions();

  //-------------------------------------------------------------------------
  // 阶段 6: 生成属性（bad 和 constraint）
  //-------------------------------------------------------------------------
  generate_properties();

  if(array_encoding.bitvectors && builder.has_array_sorts())
    conversion_error(
      "--array bv encountered a residual Array Sort; no model emitted");

  if(heap_modeling_incomplete || memory.failed || conversion_had_errors ||
     expr_converter.has_conversion_errors())
  {
    log.error() << "BTOR2 conversion aborted: unsupported or incomplete "
                   "semantics; no model emitted"
                << messaget::eom;
    return true;
  }

  // 输出 BTOR2
  builder.write(out);
  const bool failed =
    conversion_had_errors || expr_converter.has_conversion_errors();
  if(!failed && source_map != nullptr)
    write_source_map(*source_map);
  if(!out || (source_map != nullptr && !*source_map))
  {
    log.error() << "Failed to write BTOR2 model or source map" << messaget::eom;
    return true;
  }
  if(failed)
    log.error() << "BTOR2 conversion completed with unsupported constructs; "
                   "diagnostic output was emitted"
                << messaget::eom;
  return failed;
}

void goto_to_btor2_convertert::create_sorts()
{
  builder.comment("");
  builder.comment("Sort definitions");

  for(const auto &id : variable_order)
  {
    auto &var = variables[id];
    if(var.scalarized_fixed_array)
      continue;
    var.sort_nid = expr_converter.convert_type(var.type);
  }
}

void goto_to_btor2_convertert::create_states()
{
  builder.comment("");
  builder.comment("State variables");

  // Pass 1: 创建状态变量并注册符号。BTOR2 要求操作数在使用前已定义，
  // 因此初始值节点在状态节点之前创建，确保 init 引用的操作数均已存在。
  for(const auto &id : variable_order)
  {
    auto &var = variables[id];
    if(var.scalarized_fixed_array)
      continue;
    if(var.sort_nid == 0)
      continue;

    if(var.type.id() != ID_array)
    {
      if(var.has_initializer)
      {
        var.init_nid = expr_converter.convert(var.initializer);
        if(var.init_nid == 0)
          var.init_nid = builder.zero(var.sort_nid);
      }
      else
      {
        var.init_nid = builder.zero(var.sort_nid);
      }
    }

    var.state_nid = builder.state(var.sort_nid, var.name, id2string(var.id));
    expr_converter.register_symbol(var.id, var.state_nid, var.type);

    // 数组类型不生成 init（保持无约束）
    if(var.type.id() == ID_array)
      continue;

    builder.init(var.sort_nid, var.state_nid, var.init_nid);
  }

  // Pass 2: 所有标量元素状态已创建，注册标量化数组。
  for(const auto &entry : variables)
  {
    const auto &var = entry.second;
    if(!var.scalarized_fixed_array)
      continue;

    std::vector<btor2_nid_t> element_nids;
    element_nids.reserve(var.scalar_element_ids.size());
    bool complete = true;
    for(const auto &elem_id : var.scalar_element_ids)
    {
      auto it = variables.find(elem_id);
      if(it == variables.end() || it->second.state_nid == 0)
      {
        complete = false;
        break;
      }
      element_nids.push_back(it->second.state_nid);
    }

    if(
      complete && var.type.id() == ID_array &&
      !var.scalar_element_ids.empty())
    {
      expr_converter.register_scalar_array(
        var.id,
        var.type,
        to_array_type(var.type).element_type(),
        element_nids);
    }
  }
}

void goto_to_btor2_convertert::create_pc_state()
{
  builder.comment("");
  builder.comment("Program counter");

  // 计算所需位宽
  pc_bits = pc_width(locations.size() + 1);
  pc_sort_nid = builder.get_or_create_bitvec_sort(pc_bits);

  // BTOR2 要求操作数节点在使用前已定义。
  // 由于 builder 按调用顺序递增分配 nid，先创建初始值再创建状态即可保证
  // init 引用的两个操作数在 init 节点之前已存在。
  btor2_nid_t pc_init = builder.zero(pc_sort_nid);
  pc_state_nid = builder.state(pc_sort_nid, "pc");

  // 初始化 PC 为 0（程序入口）
  builder.init(pc_sort_nid, pc_state_nid, pc_init);
}

btor2_nid_t goto_to_btor2_convertert::make_pc_const(unsigned loc)
{
  return builder.constd(pc_sort_nid, mp_integer(loc));
}

btor2_nid_t goto_to_btor2_convertert::make_pc_equals(unsigned loc)
{
  btor2_nid_t loc_const = make_pc_const(loc);
  return builder.eq(builder.get_bool_sort(), pc_state_nid, loc_const);
}

void goto_to_btor2_convertert::generate_transitions()
{
  builder.comment("");
  builder.comment("State transitions (next)");

  //--- 生成变量状态转换 ---
  for(const auto &id : variable_order)
  {
    const auto &var = variables[id];
    if(var.state_nid == 0)
      continue;

    auto it = state_updates.find(id);
    if(it == state_updates.end() || it->second.empty())
    {
      // 没有更新：变量保持不变
      // next <sort> <state> <state>
      builder.next(var.sort_nid, var.state_nid, var.state_nid);
    }
    else
    {
      // 构建 ITE 链：后面的更新有更高优先级
      // 从当前值开始，逆序应用更新。
      // 这样可保证"同一时刻多条可达更新"时，程序顺序靠后的写入覆盖前者，
      // 与顺序执行语义一致。
      btor2_nid_t next_val = var.state_nid; // 默认：保持当前值

      // 逆序遍历以构建正确的 ITE 链
      // if cond_n then val_n else (if cond_{n-1} then val_{n-1} else ...)
      for(auto rit = it->second.rbegin(); rit != it->second.rend(); ++rit)
      {
        next_val =
          builder.ite(var.sort_nid, rit->first, rit->second, next_val);
      }

      // 生成 next 指令
      auto stop = builder.lor(builder.get_bool_sort(), memory.heap.halted,
        memory.heap.faults());
      next_val = builder.ite(var.sort_nid, stop, var.state_nid, next_val);
      builder.next(var.sort_nid, var.state_nid, next_val);
    }
  }

  //--- 生成 PC 状态转换 ---
  builder.comment("");
  builder.comment("PC transition");

  btor2_nid_t pc_next = pc_state_nid; // 默认：保持当前位置

  // 逆序遍历所有位置的 PC 更新
  for(auto rit = location_order.rbegin(); rit != location_order.rend(); ++rit)
  {
    unsigned loc = *rit;
    auto it = pc_updates.find(loc);
    if(it != pc_updates.end())
    {
      // 与变量状态更新相同：后出现的 PC 更新优先级更高。
      // 为每个更新构建 ITE
      for(auto uit = it->second.rbegin(); uit != it->second.rend(); ++uit)
      {
        btor2_nid_t target_const = make_pc_const(uit->second);
        pc_next = builder.ite(pc_sort_nid, uit->first, target_const, pc_next);
      }
    }
  }

  // 生成 PC 的 next 指令
  auto stop = builder.lor(builder.get_bool_sort(), memory.heap.halted,
    memory.heap.faults());
  pc_next = builder.ite(pc_sort_nid, stop, pc_state_nid, pc_next);
  builder.next(pc_sort_nid, pc_state_nid, pc_next);
  memory.heap.finish();
}

void goto_to_btor2_convertert::generate_properties()
{
  struct selected_propertyt
  {
    std::optional<unsigned> pc;
    source_locationt source;
    btor2_nid_t condition;
    std::string name;
    std::string reason;
  };
  std::vector<selected_propertyt> selected;
  const auto bool_sort = builder.get_bool_sort();
  const auto is_selected = [this](const source_locationt &source) {
    return !property_options.reach_only ||
           source.get_property_class() == "unreach-call";
  };
  bool has_reach_property = false;
  builder.comment("Properties (bad states from selected assertions)");
  for(const auto &assertion : assertions)
  {
    const unsigned loc = assertion.loc_number;
    const auto &source = locations.at(loc).instruction->source_location();
    if(!is_selected(source))
      continue;
    has_reach_property |= source.get_property_class() == "unreach-call";
    auto cond = assertion.cond_nid;
    if(cond == 0)
      cond = expr_converter.convert(assertion.condition);
    if(cond == 0)
    {
      conversion_error("Failed to translate selected assertion");
      continue;
    }
    auto bad = builder.land(
      bool_sort, make_pc_equals(loc), builder.lnot(bool_sort, cond));
    bad = builder.land(bool_sort, bad, memory.heap.valid_at(loc));
    locations[loc].bad_condition_node = bad;
    selected.push_back({loc, source, bad, assertion.bad_name, ""});
  }

  // Retain queries removed by a successful reachability simplification. This
  // does not turn a failed/unsupported translation into a false property.
  for(const auto &source : property_options.unreachable_assertions)
  {
    if(!is_selected(source))
      continue;
    has_reach_property |= source.get_property_class() == "unreach-call";
    log.status() << "Property at " << source
                 << " was proved unreachable by constant folding; kept as "
                    "a trivially-unreachable bad state"
                 << messaget::eom;
    selected.push_back({
      {}, source, builder.zero(bool_sort),
      "property_unreachable_" + std::to_string(selected.size()),
      "unreachable_after_constant_folding"});
  }
  if(!property_options.error_function.empty() && !has_reach_property)
  {
    source_locationt source;
    source.set_property_class("unreach-call");
    source.set_comment("unreachable call to " + property_options.error_function);
    selected.push_back({
      {}, source, builder.zero(bool_sort), "property_unreach_call_empty",
      "no_target_call_in_inlined_entry"});
    log.status() << "No call to " << property_options.error_function
                 << " in the inlined entry; emitting an explicit false property"
                 << messaget::eom;
  }
  if(assertions.empty() && property_options.unreachable_assertions.empty() &&
     property_options.error_function.empty())
  {
    // Preserve the release branch's no-assertion placeholder, with metadata
    // identifying its origin. Translation errors still block model output.
    builder.comment(
      "NOTE: program contains no assertion and constant folding removed none");
    builder.comment(
      "NOTE: bad 'property_unreach_call' is a constant-false placeholder");
    log.warning() << "no verifiable property: emitting a constant-false "
                     "(vacuously safe) bad state"
                  << messaget::eom;
    selected.push_back({
      {}, {}, builder.zero(bool_sort), "property_unreach_call",
      "no_assertion_in_program"});
  }
  if(selected.empty() && memory.heap.properties.empty())
    conversion_error("No property to export after property selection");

  btor2_nid_t merged_bad = 0;
  if(property_options.merge && !selected.empty())
  {
    for(const auto &property : selected)
      builder.comment("merged disjunct: " + property.name);
    auto disjunction = selected.front().condition;
    for(std::size_t i = 1; i < selected.size(); ++i)
      disjunction = builder.lor(bool_sort, disjunction, selected[i].condition);
    merged_bad = builder.bad(
      disjunction, property_options.reach_only ? "property_unreach_call" :
                                               "property_assertions");
  }
  for(const auto &property : selected)
  {
    const auto node = merged_bad != 0 ? merged_bad :
      builder.bad(property.condition, property.name);
    if(property.pc.has_value())
      locations.at(*property.pc).bad_node = node;
    json_objectt entry;
    entry["bad_node"] = json_numbert(std::to_string(node));
    entry["condition_node"] = json_numbert(std::to_string(property.condition));
    if(property.pc.has_value())
      entry["pc"] = json_numbert(std::to_string(*property.pc));
    entry["property_id"] = json_stringt(id2string(property.source.get_property_id()));
    entry["property_class"] = json_stringt(id2string(property.source.get_property_class()));
    entry["elimination_reason"] = json_stringt(property.reason);
    json_objectt source;
    source["file_name"] = json_stringt(id2string(property.source.get_file()));
    source["line"] = json_stringt(id2string(property.source.get_line()));
    source["function"] = json_stringt(id2string(property.source.get_function()));
    entry["source"] = std::move(source);
    property_metadata.push_back(std::move(entry));
  }

  //--- 处理假设 ---
  if(!assumptions.empty())
  {
    builder.comment("");
    builder.comment("Constraints from assumptions");

    for(const auto &[loc, cond] : assumptions)
    {
      btor2_nid_t at_loc = make_pc_equals(loc);
      at_loc = builder.land(builder.get_bool_sort(), at_loc, memory.heap.valid_at(loc));
      btor2_nid_t cond_nid = expr_converter.convert(cond);

      if(cond_nid == 0)
        cond_nid = fresh_unknown_bool("__unknown_assume_constraint");

      btor2_nid_t bool_sort = builder.get_bool_sort();

      // 约束：如果在此位置，则条件必须为真
      // 等价于：!at_loc || condition
      btor2_nid_t not_at_loc = builder.lnot(bool_sort, at_loc);
      btor2_nid_t constraint_expr =
        builder.lor(bool_sort, not_at_loc, cond_nid);

      // 生成 constraint 指令
      builder.constraint(
        constraint_expr, "assume_at_loc_" + std::to_string(loc));
    }
  }
}

void goto_to_btor2_convertert::write_source_map(std::ostream &out) const
{
  // This is translation metadata, not a new counterexample format. A node
  // range records creation provenance; shared expressions and the final next
  // ITEs need not have a unique source instruction.
  auto number = [](std::size_t value) {
    return json_numbert(std::to_string(value));
  };
  json_objectt result;
  result["format_version"] = json_stringt("1");
  result["pc_node"] = number(pc_state_nid);
  result["source_properties"] = property_metadata;
  json_objectt selection;
  selection["error_function"] = json_stringt(property_options.error_function);
  selection["reach_only"] = jsont::json_boolean(property_options.reach_only);
  selection["merged"] = jsont::json_boolean(property_options.merge);
  selection["no_heap_guards"] =
    jsont::json_boolean(property_options.no_heap_guards);
  result["property_selection"] = std::move(selection);
  result["int_width"] = number(config.ansi_c.int_width);
  result["long_width"] = number(config.ansi_c.long_int_width);
  result["pointer_width"] = number(config.ansi_c.pointer_width);
  json_arrayt instructions;
  for(const auto loc : location_order)
  {
    const auto &info = locations.at(loc);
    const auto &instruction = *info.instruction;
    const auto &source = instruction.source_location();
    json_objectt entry;
    entry["pc"] = number(loc);
    entry["goto_location"] = number(instruction.location_number);
    entry["kind"] = json_stringt(instruction.to_string());
    std::ostringstream text;
    instruction.output(text);
    entry["instruction"] = json_stringt(text.str());
    entry["first_node"] = number(info.first_node);
    entry["last_node"] = number(info.last_node);
    entry["pc_guard_node"] = number(info.pc_guard);
    entry["bad_node"] = number(info.bad_node);
    entry["bad_condition_node"] = number(info.bad_condition_node);
    entry["property_id"] = json_stringt(id2string(source.get_property_id()));
    entry["property_class"] = json_stringt(id2string(source.get_property_class()));
    json_objectt location;
    location["file_name"] = json_stringt(id2string(source.get_file()));
    location["line"] = json_stringt(id2string(source.get_line()));
    location["column"] = json_stringt(id2string(source.get_column()));
    location["function"] = json_stringt(id2string(source.get_function()));
    entry["source"] = std::move(location);

    // Preserve each nondeterministic call event, including calls returning the
    // same value in successive loop iterations. Its result is in S[t+1].
    std::string nondet_function;
    const exprt *lhs = nullptr;
    if(instruction.is_assign())
    {
      const auto &rhs = instruction.assign_rhs();
      if(rhs.id() == ID_side_effect && rhs.get(ID_statement) == ID_nondet)
      {
        nondet_function = id2string(rhs.get(ID_C_identifier));
        lhs = &instruction.assign_lhs();
      }
    }
    else if(instruction.is_function_call() &&
            instruction.call_function().id() == ID_symbol)
    {
      nondet_function = id2string(
        to_symbol_expr(instruction.call_function()).get_identifier());
      lhs = &instruction.call_lhs();
    }
    if(nondet_function.rfind("__VERIFIER_nondet_", 0) == 0 &&
       lhs != nullptr && lhs->id() == ID_symbol)
    {
      auto variable = variables.find(to_symbol_expr(*lhs).get_identifier());
      if(variable != variables.end())
      {
        entry["nondet_function"] = json_stringt(nondet_function);
        entry["result_state_node"] = number(variable->second.state_nid);
        entry["result_type"] = json_stringt(id2string(lhs->type().id()));
        // Retain direct result data flow for multiple calls on one source
        // line. Inlining may duplicate a call site; execution order alone
        // cannot identify its source column.
        if(info.successors.size() == 1)
        {
          const auto next = locations.find(info.successors.front());
          if(next != locations.end())
          {
            const auto &consumer = *next->second.instruction;
            const auto &consumer_source = consumer.source_location();
            if(consumer.is_assign() && consumer.assign_rhs() == *lhs &&
               consumer.assign_lhs().id() == ID_symbol &&
               consumer_source.get_file() == source.get_file() &&
               consumer_source.get_line() == source.get_line() &&
               consumer_source.get_function() == source.get_function())
            {
              const symbolt *symbol = nullptr;
              const auto &id =
                to_symbol_expr(consumer.assign_lhs()).get_identifier();
              if(!ns.lookup(id, symbol) && symbol != nullptr)
                entry["result_destination"] =
                  json_stringt(id2string(symbol->base_name));
            }
          }
        }
      }
    }
    instructions.push_back(std::move(entry));
  }
  result["instructions"] = std::move(instructions);
  json_arrayt states;
  for(const auto &id : variable_order)
  {
    const auto &variable = variables.at(id);
    if(variable.state_nid == 0)
      continue;
    json_objectt state;
    state["node"] = number(variable.state_nid);
    state["symbol"] = json_stringt(id2string(id));
    state["type"] = json_stringt(from_type(ns, ID_main, variable.type));
    states.push_back(std::move(state));
  }
  result["states"] = std::move(states);
  result["memory"] = memory.heap.metadata();
  result.output(out);
  out << '\n';
}

//===========================================================================
// Public API
//===========================================================================

bool write_goto_btor2(
  const goto_modelt &goto_model,
  std::ostream &out,
  messaget &log,
  bool emit_warning_comments,
  std::ostream *source_map,
  unsigned heap_objects,
  array_encoding_optionst array_encoding,
  btor2_property_optionst properties)
{
  const auto &functions = goto_model.get_goto_functions().function_map;

  // 查找 main 函数
  auto it = functions.find(ID_main);
  if(it == functions.end())
  {
    log.error() << "No main function found" << messaget::eom;
    return true;
  }

  return write_goto_function_btor2(
    it->second,
    ID_main,
    goto_model.symbol_table,
    out,
    log,
    emit_warning_comments,
    source_map,
    heap_objects,
    array_encoding,
    std::move(properties));
}

bool write_goto_function_btor2(
  const goto_functionst::goto_functiont &function,
  const irep_idt &function_id,
  const symbol_tablet &symbol_table,
  std::ostream &out,
  messaget &log,
  bool emit_warning_comments,
  std::ostream *source_map,
  unsigned heap_objects,
  array_encoding_optionst array_encoding,
  btor2_property_optionst properties)
{
  // 检查函数是否有函数体
  if(!function.body_available())
  {
    log.error() << "Function " << function_id << " has no body" << messaget::eom;
    return true;
  }

  log.status() << "Converting function " << function_id << " to BTOR2"
               << messaget::eom;

  // 创建转换器并执行转换
  goto_to_btor2_convertert converter(
    function.body,
    symbol_table,
    log,
    emit_warning_comments,
    heap_objects,
    array_encoding,
    std::move(properties));
  return converter.convert(out, source_map);
}
