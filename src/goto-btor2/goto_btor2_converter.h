/*******************************************************************\

Module: Goto 程序到 BTOR2 的转换 - 转换器类声明

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// goto_to_btor2_convertert 类声明
///
/// 本文件声明了 goto 程序到 BTOR2 的核心转换器类。该类将一个完整的
/// goto 函数体（通常为内联后的 main 函数）转换为 BTOR2 有限状态机。
///
/// 转换过程分为六个阶段：
/// 1. collect_variables + collect_locations: 收集变量并分配 PC 位置
/// 2. create_sorts + create_states: 创建 BTOR2 类型和状态变量
/// 3. create_pc_state: 创建程序计数器状态
/// 4. process_instructions: 处理每条指令，收集条件状态更新
/// 5. generate_transitions: 生成 ITE 链式的 next 转换函数
/// 6. generate_properties: 生成 bad（断言违反）和 constraint（假设）

#ifndef CPROVER_GOTO_BTOR2_GOTO_BTOR2_CONVERTER_H
#define CPROVER_GOTO_BTOR2_GOTO_BTOR2_CONVERTER_H

#include "btor2_builder.h"
#include "expr_to_btor2.h"
#include "memory_access.h"
#include "property_options.h"

#include <goto-programs/goto_program.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <cctype>
#include <functional>
#include <map>
#include <optional>
#include <unordered_map>
#include <vector>

#include <util/mp_arith.h>

/// Strip the qualifying "::..." prefix from a property identifier and replace
/// characters that are illegal in BTOR2 symbols with '_'.
inline std::string btor2_normalize_property_name(const irep_idt &id)
{
  std::string name = id2string(id);
  std::string::size_type pos = name.rfind("::");
  if(pos != std::string::npos)
    name = name.substr(pos + 2);
  for(char &ch : name)
  {
    if(!std::isalnum(static_cast<unsigned char>(ch)) && ch != '_')
      ch = '_';
  }
  return name;
}

/// Derive the BTOR2 bad-state symbol for a goto assertion from its
/// source-location property id (preferred) or property class.
inline std::string btor2_make_bad_property_name(
  unsigned loc,
  const source_locationt &source_location)
{
  const irep_idt &property_id = source_location.get_property_id();
  if(!property_id.empty())
    return "property_" + btor2_normalize_property_name(property_id);

  const irep_idt &property_class = source_location.get_property_class();
  if(!property_class.empty())
  {
    return "property_" + btor2_normalize_property_name(property_class) +
           "_at_loc_" + std::to_string(loc);
  }

  return "assertion_at_loc_" + std::to_string(loc);
}

/// 变量信息：存储单个程序变量在 BTOR2 中的映射信息
struct variable_infot
{
  irep_idt id;                    ///< 变量的符号标识符
  std::string name;               ///< 规范化后的 BTOR2 变量名
  typet type;                     ///< BTOR2 存储类型（展平后）
  typet logical_type;             ///< 逻辑类型（展平前）
  btor2_nid_t sort_nid = 0;       ///< BTOR2 类型节点 ID
  btor2_nid_t state_nid = 0;      ///< BTOR2 状态变量节点 ID
  btor2_nid_t init_nid = 0;       ///< BTOR2 初始值节点 ID
  bool has_initializer = false;   ///< 是否有静态初始值
  exprt initializer;              ///< 初始值表达式
  bool scalarized_fixed_array = false;  ///< 是否已被标量化拆分
  std::vector<irep_idt> scalar_element_ids; ///< 标量化后的逐元素变量 ID
};

/// 位置信息：存储单个 goto 指令的 PC 位置和后继信息
struct location_infot
{
  unsigned loc_number;                          ///< PC 位置编号
  goto_programt::const_targett instruction;     ///< 对应的 goto 指令
  std::vector<unsigned> successors;             ///< 后继位置列表
  bool is_loop_head = false;                    ///< 是否为循环头
  bool is_target = false;                       ///< 是否为跳转目标
  btor2_nid_t first_node = 0;
  btor2_nid_t last_node = 0;
  btor2_nid_t pc_guard = 0;
  btor2_nid_t bad_node = 0;
  btor2_nid_t bad_condition_node = 0;
};

/// 断言信息：存储断言的条件、位置和属性名称
struct assertion_infot
{
  unsigned loc_number;      ///< PC 位置编号
  exprt condition;          ///< 断言条件表达式
  std::string bad_name;     ///< BTOR2 bad 属性名称
  btor2_nid_t cond_nid = 0; ///< 已转换的条件节点 ID（0 表示尚未转换）
};

/// Goto 程序到 BTOR2 的核心转换器类
class goto_to_btor2_convertert
{
public:
  goto_to_btor2_convertert(
    const goto_programt &_program,
    const symbol_tablet &_symbol_table,
    messaget &_log,
    bool _emit_warning_comments,
    unsigned heap_objects,
    array_encoding_optionst _array_encoding,
    btor2_property_optionst _properties)
    : program(_program),
      ns(_symbol_table),
      log(_log),
      emit_warning_comments(_emit_warning_comments),
      array_encoding(_array_encoding),
      property_options(std::move(_properties)),
      expr_converter(builder, ns, log, _emit_warning_comments),
      memory(builder, expr_converter, ns, log, heap_objects, _array_encoding)
  {
    memory.heap.emit_guard_properties = !property_options.no_heap_guards;
    memory.heap.emit_bad_properties = !property_options.reach_only;
  }

  /// 执行完整的转换流程，将 BTOR2 输出到 out
  bool convert(std::ostream &out, std::ostream *source_map = nullptr);

private:
  const goto_programt &program;  ///< 要转换的 goto 程序
  const namespacet ns;           ///< 命名空间
  messaget &log;                 ///< 消息处理器

  bool emit_warning_comments = false; ///< 是否在 BTOR2 中输出警告注释
  bool conversion_had_errors = false; ///< 不完整语义阻止 BTOR2 输出
  array_encoding_optionst array_encoding;
  btor2_property_optionst property_options;
  json_arrayt property_metadata;
  btor2_buildert builder;            ///< BTOR2 指令构建器
  expr_to_btor2t expr_converter;     ///< 表达式转换器

  memory_accesst memory;

  bool process_sprintf_hex(unsigned, btor2_nid_t, const goto_programt::instructiont &);
  void warn(const std::string &msg);
  void conversion_error(const std::string &msg);
  void write_source_map(std::ostream &out) const;

  std::map<irep_idt, variable_infot> variables;  ///< 收集到的所有变量
  std::vector<irep_idt> variable_order;           ///< 变量声明顺序

  std::map<unsigned, location_infot> locations;   ///< 所有 PC 位置
  std::vector<unsigned> location_order;            ///< 位置编号顺序
  std::unordered_map<const goto_programt::instructiont *, unsigned>
    instruction_to_loc;  ///< 指令指针 → 位置编号映射

  btor2_nid_t pc_sort_nid = 0;   ///< PC 类型的节点 ID
  btor2_nid_t pc_state_nid = 0;  ///< PC 状态变量的节点 ID
  std::size_t pc_bits = 0;       ///< PC 的位宽

  std::vector<assertion_infot> assertions;                 ///< 所有断言
  std::vector<std::pair<unsigned, exprt>> assumptions;     ///< 所有假设

  /// 条件状态更新映射：变量 → [(条件, 新值), ...]
  /// 逆序遍历构建 ITE 链以保留"后者覆盖前者"的语义
  std::map<irep_idt, std::vector<std::pair<btor2_nid_t, btor2_nid_t>>>
    state_updates;
  /// PC 条件更新映射：位置 → [(条件, 目标位置), ...]
  std::map<unsigned, std::vector<std::pair<btor2_nid_t, unsigned>>> pc_updates;
  /// 非确定性输入变量映射
  std::map<irep_idt, btor2_nid_t> nondet_inputs;

  /// Dynamic heap modelling failed for a malloc/allocate result. Once this is
  /// set, the converter must not emit a usable BTOR2 model because heap-backed
  /// assertions may otherwise be silently proven on missing heap state.
  bool heap_modeling_incomplete = false;

  std::size_t unknown_counter = 0;

  btor2_nid_t fresh_unknown(const typet &type, const std::string &prefix);
  btor2_nid_t fresh_unknown_bool(const std::string &prefix);

  bool collect_variables();
  bool collect_locations();

  void create_sorts();
  void create_states();
  void create_pc_state();

  btor2_nid_t make_pc_const(unsigned loc);
  btor2_nid_t make_pc_equals(unsigned loc);

  void process_instructions();
  void process_assign(
    unsigned loc,
    btor2_nid_t at_loc,
    const goto_programt::instructiont &instr);
  void process_function_call(
    unsigned loc,
    btor2_nid_t at_loc,
    const goto_programt::instructiont &instr);
  void process_goto(
    unsigned loc,
    btor2_nid_t at_loc,
    const goto_programt::instructiont &instr);
  void process_assert(
    unsigned loc,
    btor2_nid_t at_loc,
    const goto_programt::instructiont &instr);
  void process_assume(
    unsigned loc,
    btor2_nid_t at_loc,
    const goto_programt::instructiont &instr);

  void add_pc_fallthrough(unsigned loc, btor2_nid_t at_loc);
  unsigned get_target_location(goto_programt::const_targett target);

  void generate_transitions();
  void generate_properties();
};

#endif // CPROVER_GOTO_BTOR2_GOTO_BTOR2_CONVERTER_H
