// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

/*******************************************************************\

Module: Goto 程序到 BTOR2 的转换 - 实现

Authors: C2BTOR contributors; CBMC attribution is retained in LICENSES/

\*******************************************************************/

#include "goto_btor2.h"
#include "goto_btor2_converter.h"
#include "btor2_type_utils.h"
#include "array_uniform_pruning.h"
#include "array_relation_pruning.h"

#include <goto-programs/goto_functions.h>
#include <util/arith_tools.h>
#include <util/config.h>
#include <util/json.h>
#include <util/json_irep.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <langapi/language_util.h>

#include <cmath>
#include <exception>
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

  if(optimizations.array_blocks &&
     (!optimizations.logical_arrays || !optimizations.scalar_blocks))
  {
    conversion_error(
      "array block optimization requires logical arrays and scalar blocks");
    return true;
  }
  if(optimizations.scalar_blocks && !large_block_encoding)
  {
    conversion_error("scalar block optimization requires LBE");
    return true;
  }
  if(optimizations.array_loop_summary &&
     (!optimizations.logical_arrays || !array_encoding.object_memory ||
      array_encoding.bitvectors))
  {
    conversion_error(
      "array loop summary requires logical arrays, object memory, and "
      "array or mixed encoding");
    return true;
  }

  // 添加注释头
  if(source_map != nullptr)
    expr_converter.enable_event_input_tracking();
  if(source_map != nullptr && !property_options.source_provenance.enabled)
    btor2_capture_source_events(
      program, ns, property_options.source_provenance,
      "converter-entry; caller did not provide an earlier frontend snapshot");
  builder.comment("BTOR2 generated from goto-program");
  builder.comment("c2btor-property-contract selected-assertions-only");
  builder.comment("");

  //-------------------------------------------------------------------------
  // 阶段 1: 收集变量和位置
  //-------------------------------------------------------------------------
  if(optimizations.state_projection)
  {
    pre_state_report = optimize_before_state(program, ns);
    btor2_record_source_transform(
      program, property_options.source_provenance, "pre-state-optimization");
    property_options.unreachable_assertions.insert(
      property_options.unreachable_assertions.end(),
      pre_state_report.unreachable_assertions.begin(),
      pre_state_report.unreachable_assertions.end());
    scalar_projection_report.forced_static_symbols =
      pre_state_report.forced_static_symbols;
    log.status() << "Pre-state optimization: " << pre_state_report.before
                 << " -> " << pre_state_report.after << " instructions; "
                 << pre_state_report.constants_replaced << " constant uses, "
                 << pre_state_report.removed_objects << " unused objects"
                 << messaget::eom;
    if(!pre_state_report.skipped_reason.empty())
      log.status() << "Pre-state optimization retained the original program: "
                   << pre_state_report.skipped_reason << messaget::eom;
  }
  if(optimizations.array_loop_summary)
  {
    array_summary_report = summarize_array_loops(program, ns);
    btor2_record_source_transform(
      program, property_options.source_provenance, "certified-array-loop-summary");
    uniform_array_reads_pruned = prune_uniform_array_reads(
      program, ns, array_summary_report.certified_arrays);
    btor2_record_source_transform(
      program, property_options.source_provenance, "uniform-array-read-pruning");
    equal_array_comparisons_pruned = prune_equal_array_comparisons(
      program, ns, array_summary_report.certified_arrays);
    btor2_record_source_transform(
      program, property_options.source_provenance, "equal-array-comparison-pruning");
    log.status() << "Array loop summary: " << array_summary_report.summarized
                 << "/" << array_summary_report.candidates
                 << " certified loops; " << uniform_array_reads_pruned
                 << " dominated uniform reads and "
                 << equal_array_comparisons_pruned
                 << " equal-array comparisons replaced" << messaget::eom;
    for(const auto &diagnostic : array_summary_report.diagnostics)
      log.status() << "Array loop certificate: " << diagnostic << messaget::eom;
  }
  const auto cleanup_after_summary = [&]()
  {
    const auto after_summary = optimize_before_state(program, ns);
    btor2_record_source_transform(
      program, property_options.source_provenance, "post-summary-pre-state-cleanup");
    property_options.unreachable_assertions.insert(
      property_options.unreachable_assertions.end(),
      after_summary.unreachable_assertions.begin(),
      after_summary.unreachable_assertions.end());
    pre_state_report.after = after_summary.after;
    pre_state_report.constants_replaced += after_summary.constants_replaced;
    pre_state_report.removed_objects += after_summary.removed_objects;
    pre_state_report.forced_static_symbols.insert(
      after_summary.forced_static_symbols.begin(),
      after_summary.forced_static_symbols.end());
    scalar_projection_report.forced_static_symbols.insert(
      after_summary.forced_static_symbols.begin(),
      after_summary.forced_static_symbols.end());
  };
  if(
    optimizations.state_projection &&
    (array_summary_report.summarized || uniform_array_reads_pruned ||
     equal_array_comparisons_pruned))
    cleanup_after_summary();
  if(optimizations.scalar_loop_summary)
  {
    // Array pruning can leave empty counted loops. Cleaning first exposes
    // these loops; repeating after each successful pass also exposes the
    // exact entry value of a subsequent signed reduction. Each successful
    // pass removes a back edge, so this process terminates.
    while(true)
    {
      auto pass = summarize_scalar_loops(program, ns);
      btor2_record_source_transform(
        program, property_options.source_provenance, "certified-scalar-loop-summary");
      scalar_summary_report.candidates += pass.candidates;
      scalar_summary_report.summarized += pass.summarized;
      scalar_summary_report.empty_loops += pass.empty_loops;
      scalar_summary_report.diagnostics.insert(
        scalar_summary_report.diagnostics.end(),
        pass.diagnostics.begin(),
        pass.diagnostics.end());
      if(!pass.summarized)
        break;
      if(optimizations.state_projection)
        cleanup_after_summary();
    }
    log.status() << "Scalar loop summary: " << scalar_summary_report.summarized
                 << " certified finite integer loops ("
                 << scalar_summary_report.empty_loops << " empty)"
                 << messaget::eom;
    for(const auto &diagnostic : scalar_summary_report.diagnostics)
      log.status() << "Scalar loop certificate: " << diagnostic
                   << messaget::eom;
  }
  if(scalar_projection != scalar_projection_modet::NONE)
  {
    const auto scanned = scan_pre_state_memory_symbols(program, ns);
    scalar_projection_report = project_dead_scalars(
      program, ns,
      [&](const irep_idt &id) {
        if(scanned.symbols.count(id))
          return true;
        const auto name = id2string(id);
        for(const auto &root : scanned.symbols)
        {
          const auto prefix = id2string(root);
          if(name.compare(0, prefix.size() + 1, prefix + ".") == 0 ||
             name.compare(0, prefix.size() + 6, prefix + "$elem$") == 0)
            return true;
        }
        return name.rfind("__heap_malloc$", 0) == 0;
      },
      scalar_projection);
    btor2_record_source_transform(
      program, property_options.source_provenance, "scalar-projection");
    scalar_projection_report.forced_static_symbols.insert(
      pre_state_report.forced_static_symbols.begin(),
      pre_state_report.forced_static_symbols.end());
    log.status() << "Scalar projection: " << scalar_projection_report.before
                 << " -> " << scalar_projection_report.after
                 << " instructions; removed "
                 << scalar_projection_report.assignments << " assignments, "
                 << scalar_projection_report.declarations << " declarations, "
                 << scalar_projection_report.lifetimes << " lifetimes"
                 << messaget::eom;
  }
  memory.collect(program);
  if(memory.failed)
    return true;
  if(memory.heap.uses_wide_pointer_offsets())
    expr_converter.set_pointer_value_width(memory.heap.pointer_value_bits);
  if(!collect_variables())
    return true;

  if(!collect_locations())
    return true;

  plan_blocks();
  if(optimizations.scalar_blocks)
    classify_block_states();

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
  if(source_map != nullptr ||
     (large_block_encoding && !optimizations.state_projection))
    emit_lbe_observations();
  if(source_map != nullptr)
    pc_output_nid = builder.observed_output(
      pc_sort_nid, pc_state_nid, "__c2btor_pc");

  //-------------------------------------------------------------------------
  // 阶段 5: 生成 next 状态转换函数
  //-------------------------------------------------------------------------
  generate_transitions();

  //-------------------------------------------------------------------------
  // 阶段 6: 生成属性（bad 和 constraint）
  //-------------------------------------------------------------------------
  generate_properties();
  if(source_map != nullptr)
    for(auto loc : location_order)
    {
      auto &info = locations.at(loc);
      if(info.bad_condition_node)
        info.bad_condition_output = builder.observed_output(
          builder.get_bool_sort(),
          info.bad_condition_node,
          "__c2btor_bad_" + std::to_string(loc));
    }
  if(source_map != nullptr)
    create_witness_counters();

  if(memory.heap.failed)
    conversion_error(memory.heap.failure_reason);
  if(heap_modeling_incomplete || memory.failed || conversion_had_errors ||
     expr_converter.has_conversion_errors())
  {
    log.error() << "BTOR2 conversion aborted: unsupported or incomplete "
                   "semantics; no model emitted"
                << messaget::eom;
    return true;
  }

  // 输出 BTOR2
  const auto simplified_initializers = builder.simplify_memory_initializers();
  if(simplified_initializers)
    log.status() << "Simplified " << simplified_initializers
                 << " internal memory initializers" << messaget::eom;
  if(optimizations.state_projection)
  {
    std::vector<btor2_nid_t> map_roots;
    if(source_map != nullptr)
    {
      map_roots.push_back(pc_state_nid);
      // The witness reader still uses result_state_node for singleton
      // nondeterministic calls in both map versions. Keep those post-states
      // when a map is requested, even if only a block-local copy is relevant.
      for(const auto loc : location_order)
      {
        const auto &info = locations.at(loc);
        const auto &instruction = *info.instruction;
        if(info.summary_input_node)
          map_roots.push_back(info.summary_input_node);
        if(info.witness_counter_node)
          map_roots.push_back(info.witness_counter_node);
        const exprt *lhs = nullptr;
        if(instruction.is_assign() &&
           instruction.assign_rhs().id() == ID_side_effect &&
           instruction.assign_rhs().get(ID_statement) == ID_nondet)
          lhs = &instruction.assign_lhs();
        else if(instruction.is_function_call())
          lhs = &instruction.call_lhs();
        if(lhs && lhs->id() == ID_symbol)
        {
          const auto variable =
            variables.find(to_symbol_expr(*lhs).get_identifier());
          if(variable != variables.end())
            map_roots.push_back(variable->second.state_nid);
        }
      }
    }
    try
    {
      dependency_report = builder.prune_dependencies(map_roots);
    }
    catch(const std::exception &error)
    {
      conversion_error(
        std::string("Cannot prune BTOR2 dependencies: ") + error.what());
      return true;
    }
    log.status() << "Model dependency pruning: "
                 << dependency_report.states_before << " -> "
                 << dependency_report.states_after << " states; "
                 << dependency_report.nodes_before << " -> "
                 << dependency_report.nodes_after << " nodes"
                 << messaget::eom;
  }
  if(array_encoding.bitvectors &&
     !array_encoding.symbolic_heap_bv_array_fallback && builder.has_array_sorts())
  {
    conversion_error(
      "--array bv encountered a residual Array Sort; no model emitted");
    return true;
  }
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

    if(block_liveness.local_symbols.count(id))
    {
      // Liveness proves every observable read is preceded by a definition
      // within this transition. DECL supplies the actual fresh value.
      var.local_nid = builder.zero(var.sort_nid);
      expr_converter.register_symbol(var.id, var.local_nid, var.type);
      continue;
    }

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
  pc_bits = pc_width(blocks.size() + 1);
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
  return builder.constd(pc_sort_nid, mp_integer(location_to_block.at(loc)));
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
  builder.next(pc_sort_nid, pc_state_nid, pc_next);
  memory.finish();
}

void goto_to_btor2_convertert::generate_properties()
{
  struct selected_propertyt
  {
    std::optional<unsigned> pc;
    source_locationt source;
    btor2_nid_t condition;
    // Alias retained for readers of older maps; identical to condition.
    btor2_nid_t pure_condition;
    std::string name;
    std::string reason;
  };
  std::vector<selected_propertyt> selected;
  const auto bool_sort = builder.get_bool_sort();
  builder.comment("Properties (bad states from selected assertions)");
  for(const auto &assertion : assertions)
  {
    const unsigned loc = assertion.loc_number;
    const auto &source = locations.at(loc).instruction->source_location();
    auto cond = assertion.cond_nid;
    if(cond == 0)
      cond = expr_converter.convert(assertion.condition);
    if(cond == 0)
    {
      conversion_error("Failed to translate selected assertion");
      continue;
    }
    // Pure source predicate: the program counter is at the assertion and its
    // condition evaluates to false. This node is the property being verified.
    auto pure =
      builder.land(
        bool_sort,
        optimizations.scalar_blocks ? locations.at(loc).pc_guard
                                    : make_pc_equals(loc),
        builder.lnot(bool_sort, cond));
    const auto bad = pure;
    locations[loc].bad_condition_node = bad;
    selected.push_back({loc, source, bad, pure, assertion.bad_name, ""});
  }

  // Retain queries removed by a successful reachability simplification. This
  // does not turn a failed/unsupported translation into a false property.
  for(const auto &source : property_options.unreachable_assertions)
  {
    log.status() << "Property at " << source
                 << " was proved unreachable by constant folding; kept as "
                    "a trivially-unreachable bad state"
                 << messaget::eom;
    const auto never = builder.zero(bool_sort);
    selected.push_back({
      {}, source, never, never,
      "property_unreachable_" + std::to_string(selected.size()),
      "unreachable_after_constant_folding"});
  }
  if(selected.empty())
    conversion_error("No selected source property; no model emitted");

  btor2_nid_t merged_bad = 0;
  if(property_options.merge && !selected.empty())
  {
    for(const auto &property : selected)
      builder.comment("merged disjunct: " + property.name);
    auto disjunction = selected.front().condition;
    for(std::size_t i = 1; i < selected.size(); ++i)
      disjunction = builder.lor(bool_sort, disjunction, selected[i].condition);
    source_disjunction_nid = disjunction;
    merged_bad = builder.bad(
      disjunction, "property_assertions");
  }
  for(const auto &property : selected)
  {
    const auto node =
      merged_bad != 0 ? merged_bad : builder.bad(property.condition, property.name);
    if(property.pc.has_value())
      locations.at(*property.pc).bad_node = node;
    json_objectt entry;
    entry["bad_node"] = json_numbert(std::to_string(node));
    entry["condition_node"] = json_numbert(std::to_string(property.condition));
    entry["pure_condition_node"] =
      json_numbert(std::to_string(property.pure_condition));
    if(property.pc.has_value())
      entry["pc"] = json_numbert(std::to_string(*property.pc));
    entry["property_id"] = json_stringt(id2string(property.source.get_property_id()));
    entry["property_class"] = json_stringt(id2string(property.source.get_property_class()));
    if(!property.source.get("c2btor_error_function").empty())
      entry["error_function"] =
        json_stringt(id2string(property.source.get("c2btor_error_function")));
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

    for(const auto &[loc, cond_nid] : assumptions)
    {
      btor2_nid_t at_loc = make_pc_equals(loc);
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

void goto_to_btor2_convertert::create_witness_counters()
{
  // Instrument the final encoding, after every GOTO optimization and block
  // decision. A retained instruction executes at most once per transition:
  // blocks have no internal back edge, and each encoded instruction has its
  // own guard. Cloned instances keep separate counters even when they share
  // an original source event ID. Eliminated summary calls get no counter.
  for(const auto loc : location_order)
  {
    auto &info = locations.at(loc);
    if(!btor2_source_nondet_call(*info.instruction, ns))
      continue;
    const auto sort = builder.get_or_create_bitvec_sort(8);
    const auto zero = builder.zero(sort);
    const auto one = builder.one(sort);
    info.witness_counter_node = builder.state(
      sort, "__c2btor_nondet_count_" + std::to_string(loc));
    builder.init(sort, info.witness_counter_node, zero);
    const auto incremented =
      builder.add(sort, info.witness_counter_node, one);
    builder.next(
      sort,
      info.witness_counter_node,
      builder.ite(
        sort, info.pc_guard, incremented, info.witness_counter_node));
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
  const auto memory_metadata = memory.metadata();
  result["schema_version"] = json_stringt("c2btor-source-map-1");
  result["format_version"] = json_stringt(large_block_encoding ? "2" : "1");
  result["witness_counter_format"] = json_stringt("post-counter-1");
  json_objectt configuration;
  configuration["array"] = json_stringt(
    array_encoding.bitvectors ? "bv" : array_encoding.mixed ? "mixed" : "array");
  configuration["memory"] =
    json_stringt(array_encoding.object_memory ? "object" : "global");
  configuration["lbe"] = jsont::json_boolean(large_block_encoding);
  configuration["optimize_state"] =
    jsont::json_boolean(optimizations.state_projection);
  configuration["logical_arrays"] =
    jsont::json_boolean(optimizations.logical_arrays);
  configuration["scalar_blocks"] =
    jsont::json_boolean(optimizations.scalar_blocks);
  configuration["array_blocks"] =
    jsont::json_boolean(optimizations.array_blocks);
  configuration["array_loop_summary"] =
    jsont::json_boolean(optimizations.array_loop_summary);
  configuration["scalar_loop_summary"] =
    jsont::json_boolean(optimizations.scalar_loop_summary);
  configuration["symbolic_heap"] =
    jsont::json_boolean(array_encoding.symbolic_heap);
  configuration["symbolic_heap_arrays"] =
    jsont::json_boolean(array_encoding.symbolic_heap_arrays);
  configuration["symbolic_heap_wide_offsets"] =
    jsont::json_boolean(array_encoding.symbolic_heap_wide_offsets);
  configuration["symbolic_heap_compact"] =
    jsont::json_boolean(array_encoding.symbolic_heap_compact);
  configuration["symbolic_heap_bv_array_fallback"] =
    jsont::json_boolean(array_encoding.symbolic_heap_bv_array_fallback);
  configuration["scalar_projection"] = json_stringt(
    scalar_projection == scalar_projection_modet::LIVENESS ? "liveness" :
    scalar_projection == scalar_projection_modet::DEAD ? "dead" : "none");
  configuration["merge_bads"] = jsont::json_boolean(property_options.merge);
  configuration["property_slicing"] = json_nullt{};
  for(const auto &pass : property_options.source_provenance.transformations)
    if(pass["pass"].value == "property-slicing")
      configuration["property_slicing"] = pass["enabled"];
  if(array_encoding.mixed)
    configuration["mixed_threshold_bits"] =
      number(array_encoding.mixed_threshold_bits);
  if(array_encoding.max_object_bytes)
    configuration["max_object_bytes"] = number(*array_encoding.max_object_bytes);
  result["optimization_config"] = std::move(configuration);
  if(large_block_encoding)
  {
    json_arrayt block_map;
    for(unsigned pc = 0; pc < blocks.size(); ++pc)
    {
      json_objectt block;
      block["pc"] = number(pc);
      block["entry_instruction"] = number(blocks[pc].front());
      json_arrayt members;
      for(auto loc : blocks[pc])
        members.push_back(number(loc));
      block["instructions"] = std::move(members);
      std::set<unsigned> exits;
      for(auto loc : blocks[pc])
        for(auto successor : locations.at(loc).successors)
          if(location_to_block.at(successor) != pc ||
             (optimizations.scalar_blocks && successor <= loc))
            exits.insert(successor);
      json_arrayt exit_targets;
      for(auto loc : exits)
        exit_targets.push_back(number(loc));
      block["exit_instructions"] = std::move(exit_targets);
      block_map.push_back(std::move(block));
    }
    result["blocks"] = std::move(block_map);
  }
  result["pc_node"] = number(pc_state_nid);
  if(pc_output_nid)
    result["pc_output"] = number(pc_output_nid);
  json_objectt observation_protocol;
  observation_protocol["version"] = json_stringt("c2btor-events-1");
  observation_protocol["event_id"] = json_stringt("instruction_id");
  observation_protocol["pc_symbol"] = json_stringt("__c2btor_pc");
  observation_protocol["execution_symbol_prefix"] = json_stringt("__c2btor_exec_");
  observation_protocol["value_symbol_prefix"] = json_stringt("__c2btor_value_");
  observation_protocol["bad_symbol_prefix"] = json_stringt("__c2btor_bad_");
  observation_protocol["frame"] = json_stringt("current-state-and-input");
  observation_protocol["value_semantics"] =
    json_stringt("evaluated-event-result; valid only when executed=1; bitvectors only");
  observation_protocol["bad_semantics"] =
    json_stringt("executed selected source assertion violation at this event");
  result["observations"] = std::move(observation_protocol);
  if(scalar_projection != scalar_projection_modet::NONE)
  {
    json_objectt projection;
    projection["mode"] = json_stringt(
      scalar_projection == scalar_projection_modet::LIVENESS ? "liveness" : "dead");
    projection["original_instructions"] = number(scalar_projection_report.before);
    projection["retained_instructions"] = number(scalar_projection_report.after);
    projection["assignments_removed"] = number(scalar_projection_report.assignments);
    projection["declarations_removed"] = number(scalar_projection_report.declarations);
    projection["lifetimes_removed"] = number(scalar_projection_report.lifetimes);
    projection["memory_plan"] = json_stringt("planned-after-scalar-projection");
    result["scalar_projection"] = std::move(projection);
  }
  if(optimizations.state_projection)
  {
    json_objectt optimization;
    optimization["pre_state"] = jsont::json_boolean(true);
    if(!pre_state_report.skipped_reason.empty())
      optimization["pre_state_skipped_reason"] =
        json_stringt(pre_state_report.skipped_reason);
    optimization["original_instructions"] = number(pre_state_report.before);
    optimization["retained_instructions"] = number(pre_state_report.after);
    optimization["unused_objects_removed"] = number(pre_state_report.removed_objects);
    optimization["constants_replaced"] = number(pre_state_report.constants_replaced);
    optimization["states_before"] = number(dependency_report.states_before);
    optimization["states_after"] = number(dependency_report.states_after);
    optimization["nodes_before"] = number(dependency_report.nodes_before);
    optimization["nodes_after"] = number(dependency_report.nodes_after);
    optimization["node_ranges"] =
      json_stringt("creation-provenance; retained IDs may have gaps");
    result["state_optimization"] = std::move(optimization);
  }
  if(optimizations.array_loop_summary)
  {
    json_objectt summary;
    summary["enabled"] = jsont::json_boolean(true);
    summary["certified_loops"] = number(array_summary_report.summarized);
    summary["fill_loops"] = number(array_summary_report.fills);
    summary["copy_loops"] = number(array_summary_report.copies);
    summary["nondet_initialization_loops"] =
      number(array_summary_report.nondet_initializations);
    summary["expansion_format"] = json_stringt("independent-array-input-1");
    json_arrayt nondet_summaries;
    for(const auto &certificate : array_summary_report.nondet_summaries)
    {
      json_objectt group;
      group["id"] = json_stringt(certificate.id);
      group["original_event_ids"] = btor2_original_event_ids_json(certificate.loop_source);
      group["source_event_recovery"] = json_stringt("independent-array-input-1");
      group["counter_initial"] = json_stringt(integer2string(certificate.initial));
      group["iterations"] = json_stringt(integer2string(certificate.iterations));
      json_objectt loop;
      loop["kind"] = json_stringt(id2string(certificate.loop_source.get("c2btor_loop_kind")));
      loop["file_name"] = json_stringt(id2string(certificate.loop_source.get("c2btor_loop_file")));
      loop["line"] = json_stringt(id2string(certificate.loop_source.get("c2btor_loop_line")));
      loop["column"] = json_stringt(id2string(certificate.loop_source.get("c2btor_loop_column")));
      loop["function"] = json_stringt(id2string(certificate.loop_source.get("c2btor_loop_function")));
      group["loop_condition_entry"] = std::move(loop);
      json_arrayt calls;
      for(const auto &sample : certificate.calls)
      {
        json_objectt call;
        call["array_symbol"] = json_stringt(id2string(sample.array));
        call["original_event_ids"] = btor2_original_event_ids_json(sample.source);
        call["index_coefficient"] =
          json_stringt(integer2string(sample.index_coefficient));
        call["index_constant"] =
          json_stringt(integer2string(sample.index_constant));
        call["event_order"] = number(sample.order);
        call["nondet_function"] = json_stringt(id2string(sample.function));
        call["result_type"] = json_stringt(id2string(sample.type.id()));
        call["result_width"] =
          number(expr_converter.get_width(sample.type).value_or(0));
        call["result_signed"] =
          jsont::json_boolean(sample.type.id() == ID_signedbv);
        json_objectt source;
        source["file_name"] = json_stringt(id2string(sample.source.get_file()));
        source["line"] = json_stringt(id2string(sample.source.get_line()));
        source["column"] = json_stringt(id2string(sample.source.get_column()));
        source["function"] = json_stringt(id2string(sample.source.get_function()));
        call["source"] = std::move(source);
        btor2_add_call_return_metadata(call, sample.source);
        calls.push_back(std::move(call));
      }
      group["calls"] = std::move(calls);
      nondet_summaries.push_back(std::move(group));
    }
    summary["nondet_summaries"] = std::move(nondet_summaries);
    summary["uniform_reads_replaced"] = number(uniform_array_reads_pruned);
    summary["equal_array_comparisons_replaced"] =
      number(equal_array_comparisons_pruned);
    summary["witness_expansion_required"] =
      jsont::json_boolean(array_summary_report.summarized != 0);
    json_arrayt certificates;
    for(const auto &diagnostic : array_summary_report.diagnostics)
      certificates.push_back(json_stringt(diagnostic));
    summary["certificates"] = std::move(certificates);
    result["array_loop_summary"] = std::move(summary);
  }
  if(optimizations.scalar_loop_summary)
  {
    json_objectt summary;
    summary["enabled"] = jsont::json_boolean(true);
    summary["certified_loops"] = number(scalar_summary_report.summarized);
    summary["empty_loops"] = number(scalar_summary_report.empty_loops);
    summary["witness_expansion_required"] =
      jsont::json_boolean(scalar_summary_report.summarized != 0);
    json_arrayt certificates;
    for(const auto &diagnostic : scalar_summary_report.diagnostics)
      certificates.push_back(json_stringt(diagnostic));
    summary["certificates"] = std::move(certificates);
    result["scalar_loop_summary"] = std::move(summary);
  }
  if(optimizations.scalar_blocks)
  {
    json_objectt blocks_metadata;
    blocks_metadata["enabled"] = jsont::json_boolean(true);
    blocks_metadata["local_scalars"] = number(block_liveness.local_symbols.size());
    blocks_metadata["runtime_blocks"] = number(blocks.size());
    blocks_metadata["assume_boundary"] = jsont::json_boolean(true);
    result["scalar_blocks"] = std::move(blocks_metadata);
  }
  if(optimizations.array_blocks)
  {
    json_objectt arrays_metadata;
    arrays_metadata["enabled"] = jsont::json_boolean(true);
    arrays_metadata["latest_storage_versions"] = jsont::json_boolean(true);
    result["array_blocks"] = std::move(arrays_metadata);
  }
  result["source_properties"] = property_metadata;
  json_objectt selection;
  selection["scope"] = json_stringt("all-goto-assertions");
  selection["merged"] = jsont::json_boolean(property_options.merge);
  selection["semantics"] = json_stringt("selected-assertions-only");
  selection["lifetime_top"] = json_stringt("none");
  if(source_disjunction_nid)
    selection["source_disjunction_node"] =
      json_numbert(std::to_string(source_disjunction_nid));
  result["property_selection"] = std::move(selection);
  result["int_width"] = number(config.ansi_c.int_width);
  result["long_width"] = number(config.ansi_c.long_int_width);
  result["long_long_width"] = number(config.ansi_c.long_long_int_width);
  result["pointer_width"] = number(config.ansi_c.pointer_width);
  json_arrayt instructions;
  for(const auto loc : location_order)
  {
    const auto &info = locations.at(loc);
    const auto &instruction = *info.instruction;
    const auto &source = instruction.source_location();
    json_objectt entry;
    entry["pc"] = number(location_to_block.at(loc));
    entry["instruction_id"] = number(loc);
    if(property_options.source_provenance.enabled)
    {
      entry["original_event_ids"] = btor2_original_event_ids_json(source);
      json_objectt relation;
      bool unchanged = false;
      const auto origins = btor2_original_event_ids(source);
      const auto summary_kind = id2string(source.get("c2btor_summary_kind"));
      if(!summary_kind.empty())
      {
        relation["kind"] = json_stringt("certified-summary; many-to-many");
        relation["summary_kind"] = json_stringt(summary_kind);
        relation["summary_id"] = json_stringt(id2string(source.get("c2btor_summary_id")));
        relation["source_event_recovery"] = json_stringt(summary_kind == "array-nondet"
          ? "independent-array-input-1 certificate and concrete input samples"
          : "unsupported; original events retained as metadata, no dynamic expansion exported");
      }
      else
      {
        unchanged = origins.size() == 1;
        if(unchanged)
        {
          const auto original = property_options.source_provenance.original_signatures.find(*origins.begin());
          unchanged = original != property_options.source_provenance.original_signatures.end() &&
                      original->second == btor2_event_signature(instruction);
        }
        relation["kind"] = json_stringt(origins.empty() ? "lowering-created-unattributed"
          : unchanged ? "retained-goto-origin; runtime frame may be block-compressed" : "rewritten-or-derived-goto-origin");
        relation["source_event_recovery"] = json_stringt("optimized event observations; no eliminated-value reconstruction implied");
      }
      relation["time_domain"] = json_stringt("optimized transition frame");
      entry["origin_relation"] = std::move(relation);
      if(unchanged)
        entry["typed_ir_original_event"] = number(*origins.begin());
      else
      {
        const json_irept typed_ir(false);
        entry["code_ir"] = typed_ir.convert_from_irep(instruction.code());
        if(instruction.has_condition())
          entry["condition_ir"] = typed_ir.convert_from_irep(instruction.condition());
      }
    }
    if(info.executed_output)
    {
      entry["executed_output"] = number(info.executed_output);
      if(info.value_output)
      {
        entry["value_output"] = number(info.value_output);
      }
    }
    if(info.value_node && builder.contains_node(info.value_node))
    {
      entry["value_node"] = number(info.value_node);
      entry["value_sort"] = number(info.value_sort);
      entry["value_relation"] = json_stringt("evaluation of this optimized event; defined only when executed=1");
    }
    if(info.witness_counter_node)
    {
      entry["counter_node"] = number(info.witness_counter_node);
      entry["counter_width"] = number(8);
      // Direct expressions also cover the last witness frame, where there
      // need not be a following state assignment to observe the increment.
      entry["executed_node"] = number(info.pc_guard);
    }
    json_arrayt event_inputs;
    for(const auto node : info.input_nodes)
      if(builder.contains_node(node))
        event_inputs.push_back(number(node));
    if(!event_inputs.empty())
      entry["input_nodes"] = std::move(event_inputs);
    json_arrayt successors;
    for(const auto successor : info.successors)
      successors.push_back(number(successor));
    entry["successors"] = std::move(successors);
    if(instruction.is_decl() || instruction.is_dead())
      entry[instruction.is_decl() ? "decl_symbol" : "dead_symbol"] =
        json_stringt(id2string(
          instruction.is_decl() ? instruction.decl_symbol().get_identifier()
                                : instruction.dead_symbol().get_identifier()));
    if(instruction.is_assign() && instruction.assign_lhs().id() == ID_symbol)
      entry["assign_symbol"] = json_stringt(
        id2string(to_symbol_expr(instruction.assign_lhs()).get_identifier()));
    if(!source.get("c2btor_loop_kind").empty())
    {
      json_objectt loop;
      loop["kind"] = json_stringt(id2string(source.get("c2btor_loop_kind")));
      loop["file_name"] =
        json_stringt(id2string(source.get("c2btor_loop_file")));
      loop["line"] = json_stringt(id2string(source.get("c2btor_loop_line")));
      loop["column"] = json_stringt(id2string(source.get("c2btor_loop_column")));
      loop["function"] =
        json_stringt(id2string(source.get("c2btor_loop_function")));
      entry["loop_condition_entry"] = std::move(loop);
    }
    entry["goto_location"] = number(instruction.location_number);
    entry["kind"] = json_stringt(instruction.to_string());
    std::ostringstream text;
    instruction.output(text);
    entry["instruction"] = json_stringt(text.str());
    entry["first_node"] = number(info.first_node);
    entry["last_node"] = number(info.last_node);
    entry["pc_guard_node"] =
      number(builder.contains_node(info.pc_guard) ? info.pc_guard : 0);
    entry["bad_node"] =
      number(builder.contains_node(info.bad_node) ? info.bad_node : 0);
    entry["bad_condition_node"] =
      number(builder.contains_node(info.bad_condition_node)
               ? info.bad_condition_node : 0);
    if(info.bad_condition_output)
      entry["bad_condition_output"] = number(info.bad_condition_output);
    entry["property_id"] = json_stringt(id2string(source.get_property_id()));
    entry["property_class"] = json_stringt(id2string(source.get_property_class()));
    if(!source.get("c2btor_error_function").empty())
      entry["error_function"] =
        json_stringt(id2string(source.get("c2btor_error_function")));
    json_objectt location;
    location["file_name"] = json_stringt(id2string(source.get_file()));
    location["line"] = json_stringt(id2string(source.get_line()));
    location["column"] = json_stringt(id2string(source.get_column()));
    location["function"] = json_stringt(id2string(source.get_function()));
    entry["source"] = std::move(location);
    btor2_add_call_return_metadata(entry, source);
    if(!source.get("c2btor_nondet_summary_group").empty())
    {
      json_objectt summary;
      summary["group_id"] =
        json_stringt(id2string(source.get("c2btor_nondet_summary_group")));
      summary["array_symbol"] =
        json_stringt(id2string(source.get("c2btor_nondet_summary_array")));
      summary["input_node"] = number(
        builder.contains_node(info.summary_input_node) ? info.summary_input_node : 0);
      entry["nondet_summary"] = std::move(summary);
    }

    // The observed RHS can represent a source return only after checking the
    // declared return type and every wrapper cast. In particular CBMC models
    // _Bool as internal bool1 -> canonical C c_bool; narrowing integer casts
    // must never be reported as the original source function's return value.
    if(const auto call = btor2_source_nondet_call(instruction, ns))
    {
      entry["nondet_function"] = json_stringt(call->function);
      if(!call->value_preserving)
        entry["nondet_return_unsupported"] = json_stringt(call->unsupported_reason);
      else
      {
        btor2_nid_t result_state = 0;
        if(call->lhs->id() == ID_symbol)
        {
          const auto variable = variables.find(to_symbol_expr(*call->lhs).get_identifier());
          if(variable != variables.end() && builder.contains_node(variable->second.state_nid))
            result_state = variable->second.state_nid;
        }
        entry["result_state_node"] = number(result_state);
        entry["result_type"] = json_stringt(id2string(call->return_type.id()));
        entry["result_width"] = number(expr_converter.get_width(call->return_type).value_or(0));
        entry["result_signed"] = jsont::json_boolean(call->return_type.id() == ID_signedbv);
        entry["nondet_return_relation"] = json_stringt("event value equals declared source return; identity or canonical bool-to-c_bool casts only");
      }
      // Destination disambiguation is certified at the original snapshot,
      // before callback/alias simplification can rewrite pointer stores.
      const auto origins = btor2_original_event_ids(source);
      const auto &destinations = property_options.source_provenance.original_result_destinations;
      if(origins.size() == 1)
      {
        const auto destination = destinations.find(*origins.begin());
        if(destination != destinations.end())
        {
          entry["result_destination"] = destination->second.find("canonical")->second;
          entry["result_destination_designator"] = destination->second;
        }
      }
    }
    instructions.push_back(std::move(entry));
  }
  result["instructions"] = std::move(instructions);
  if(property_options.source_provenance.enabled)
  {
    const auto &captured = property_options.source_provenance;
    json_objectt provenance;
    provenance["version"] = json_stringt("c2btor-goto-origins-1");
    provenance["snapshot_stage"] = json_stringt(captured.stage);
    provenance["ir_comment_policy"] = json_stringt("structural typed code/condition IR; source once per event; complete variable and nondet-result type metadata retained separately");
    provenance["order_semantics"] = json_stringt("captured GOTO-list order and CFG successors; not source-line or runtime order");
    provenance["original_events"] = captured.original_events;
    provenance["original_symbols"] = captured.original_symbols;
    provenance["transformations"] = captured.transformations;
    std::map<std::size_t, std::vector<unsigned>> origin_targets;
    std::set<std::size_t> summarized_origins;
    for(const auto loc : location_order)
    {
      const auto &source = locations.at(loc).instruction->source_location();
      for(const auto original_id : btor2_original_event_ids(source))
      {
        origin_targets[original_id].push_back(loc);
        if(!source.get("c2btor_summary_kind").empty())
          summarized_origins.insert(original_id);
      }
    }
    json_arrayt relations;
    for(const auto &[original_id, signature] : captured.original_signatures)
    {
      (void)signature;
      json_objectt relation;
      relation["original_event_id"] = number(original_id);
      json_arrayt targets;
      for(const auto loc : origin_targets[original_id])
        targets.push_back(number(loc));
      const bool summarized = summarized_origins.count(original_id) != 0;
      const bool eliminated = targets.empty();
      relation["optimized_instruction_ids"] = std::move(targets);
      relation["status"] = json_stringt(eliminated ? "eliminated" : summarized ? "summary-related" : "origin-related");
      if(eliminated)
      {
        const auto pass = captured.removed_by.find(original_id);
        relation["removed_by"] = json_stringt(pass == captured.removed_by.end() ? "not-attributed" : pass->second);
        relation["source_event_recovery"] = json_stringt("unsupported; execution/value not present in optimized model");
      }
      relations.push_back(std::move(relation));
    }
    provenance["event_relations"] = std::move(relations);
    std::map<std::string, jsont> logical_bindings, object_bindings, packed_bindings;
    for(const auto &key : {"logical_arrays", "object_storage", "packed_layout"})
    {
      const auto entries = memory_metadata.find(key);
      if(entries == memory_metadata.end())
        continue;
      for(const auto &value : to_json_array(entries->second))
      {
        const auto &object = to_json_object(value);
        const auto identity = object.find(std::string(key) == "logical_arrays" ? "symbol" : "tag");
        if(identity != object.end())
          (std::string(key) == "logical_arrays" ? logical_bindings
           : std::string(key) == "object_storage" ? object_bindings : packed_bindings)
            .emplace(identity->second.value, value);
      }
    }
    json_arrayt symbols;
    for(const auto &symbol : captured.original_symbol_ids)
    {
      json_objectt relation;
      relation["original_symbol"] = json_stringt(id2string(symbol));
      const auto encoded = variables.find(symbol);
      if(encoded != variables.end() && encoded->second.state_nid && builder.contains_node(encoded->second.state_nid))
      {
        relation["state_node"] = number(encoded->second.state_nid);
        relation["relation"] = json_stringt("same retained symbol encoding in optimized-transition time domain");
      }
      else if(logical_bindings.count(id2string(symbol)))
      {
        relation["memory_binding"] = logical_bindings.at(id2string(symbol));
        relation["relation"] = json_stringt("logical element encoding; decode source element type using memory metadata");
      }
      else if(memory.heap.objects.count(symbol))
      {
        const auto tag = memory.heap.objects.at(symbol).tag;
        relation["object_tag"] = number(tag);
        const auto key = std::to_string(tag);
        if(object_bindings.count(key))
          relation["memory_binding"] = object_bindings.at(key);
        if(packed_bindings.count(key))
          relation["packed_binding"] = packed_bindings.at(key);
        const auto global = memory_metadata.find("memory_state");
        if(global != memory_metadata.end())
          relation["memory_state"] = global->second;
        relation["relation"] = json_stringt("addressable source object; decode by object tag/byte offset and exported memory representation");
      }
      else
        relation["relation"] = json_stringt("no retained state/storage; eliminated source value reconstruction unsupported");
      symbols.push_back(std::move(relation));
    }
    provenance["symbol_relations"] = std::move(symbols);
    provenance["expression_relations"] = json_stringt("optimized code_ir/condition_ir and observed value_node; creation ranges are not one-to-one expression certificates");
    provenance["input_relations"] = json_stringt("nondet event evaluated value and certified summary input_node; no invented inputs for eliminated events");
    provenance["source_branch_polarity"] = json_stringt("not certified for generic GOTO guards; only existing summary loop certificates identify source conditions");
    result["source_provenance"] = std::move(provenance);
  }
  json_arrayt states;
  for(const auto &id : variable_order)
  {
    const auto &variable = variables.at(id);
    if(variable.state_nid == 0 || !builder.contains_node(variable.state_nid))
      continue;
    json_objectt state;
    state["node"] = number(variable.state_nid);
    state["symbol"] = json_stringt(id2string(id));
    state["type"] = json_stringt(from_type(ns, ID_main, variable.type));
    state["type_id"] = json_stringt(id2string(variable.logical_type.id()));
    state["volatile"] =
      jsont::json_boolean(variable.logical_type.get_bool(ID_C_volatile));
    const symbolt *symbol = nullptr;
    if(!ns.lookup(id, symbol) && symbol != nullptr)
    {
      state["source_name"] = json_stringt(id2string(symbol->base_name));
      state["source_function"] =
        json_stringt(id2string(symbol->location.get_function()));
      state["auxiliary"] = jsont::json_boolean(symbol->is_auxiliary);
      state["static_lifetime"] =
        jsont::json_boolean(symbol->is_static_lifetime);
    }
    state["has_initializer"] = jsont::json_boolean(variable.has_initializer);
    states.push_back(std::move(state));
  }
  result["states"] = std::move(states);
  result["memory"] = memory_metadata;
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
  btor2_property_optionst properties,
  bool large_block_encoding,
  scalar_projection_modet scalar_projection,
  btor2_optimization_optionst optimizations)
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
    std::move(properties),
    large_block_encoding,
    scalar_projection,
    optimizations);
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
  btor2_property_optionst properties,
  bool large_block_encoding,
  scalar_projection_modet scalar_projection,
  btor2_optimization_optionst optimizations)
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
    std::move(properties),
    large_block_encoding,
    scalar_projection,
    optimizations);
  return converter.convert(out, source_map);
}
