/*******************************************************************\

Module: Goto 程序到 BTOR2 的转换

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// Goto 程序到 BTOR2 的转换
///
/// 本模块实现了将 CBMC 的 goto 程序（中间表示）转换为 BTOR2 格式的功能。
/// BTOR2 是一种用于硬件模型检查的格式，描述有限状态转换系统。
///
/// 转换过程概述：
/// ================
///
/// 1. 变量收集与位置分配：
///    - collect_variables: 遍历指令，收集变量、展平结构体/数组、
///      处理 malloc 堆对象
///    - collect_locations: 为每条指令分配 PC 位置编号
///
/// 2. BTOR2 类型和状态创建：
///    - create_sorts: 创建位向量/数组类型
///    - create_states: 创建状态变量和 init 初始化
///    - create_pc_state: 创建程序计数器状态
///
/// 3. 指令处理：
///    - process_instructions: 遍历每条指令，收集条件状态更新
///      和 PC 更新到 state_updates / pc_updates 映射
///
/// 4. 转换函数生成：
///    - generate_transitions: 逆序遍历更新，构建 ITE 链式的 next
///    - generate_properties: 生成 bad（断言违反）和 constraint（假设）
///



#ifndef CPROVER_GOTO_BTOR2_GOTO_BTOR2_H
#define CPROVER_GOTO_BTOR2_GOTO_BTOR2_H

#include <goto-programs/goto_model.h>
#include <util/message.h>

#include <iosfwd>
#include "array_encoding.h"
#include "property_options.h"

/// 将 goto 模型转换为 BTOR2 格式
///
/// 这是主要的转换入口点。它将完整的 goto 模型（包含多个函数）
/// 转换为单一的 BTOR2 有限状态机。
///
/// 转换步骤（与 convert() 的 6 个阶段一一对应）：
/// 1. collect_variables + collect_locations: 收集变量并分配 PC 位置
/// 2. create_sorts + create_states: 创建 BTOR2 类型和状态变量
/// 3. create_pc_state: 创建程序计数器状态
/// 4. process_instructions: 处理每条指令，收集条件状态更新
/// 5. generate_transitions: 生成 ITE 链式的 next 转换函数
/// 6. generate_properties: 生成 bad（断言违反）和 constraint（假设）
///
/// @param goto_model 要转换的 goto 模型
/// @param out BTOR2 输出流
/// @param log 消息处理器（用于警告和错误）
/// @param source_map optional JSON translation metadata (written on success)
/// @param properties 源属性选择/合并、辅助属性输出和已折叠断言的位置
/// @return 错误返回 true，成功返回 false
bool write_goto_btor2(
  const goto_modelt &goto_model,
  std::ostream &out,
  messaget &log,
  bool emit_warning_comments = false,
  std::ostream *source_map = nullptr,
  unsigned heap_objects = 32,
  array_encoding_optionst array_encoding = {},
  btor2_property_optionst properties = {});

/// 将单个 goto 函数转换为 BTOR2 格式
///
/// 这对于分析单个函数很有用。函数必须已经被内联
/// （即没有函数调用），因为 BTOR2 不支持过程调用。
///
/// @param function 要转换的函数
/// @param function_id 函数标识符
/// @param symbol_table 符号表（用于类型信息）
/// @param out BTOR2 输出流
/// @param log 消息处理器
/// @param source_map optional JSON translation metadata (written on success)
/// @param properties 源属性选择/合并、辅助属性输出和已折叠断言的位置
/// @return 错误返回 true，成功返回 false
bool write_goto_function_btor2(
  const goto_functionst::goto_functiont &function,
  const irep_idt &function_id,
  const symbol_tablet &symbol_table,
  std::ostream &out,
  messaget &log,
  bool emit_warning_comments = false,
  std::ostream *source_map = nullptr,
  unsigned heap_objects = 32,
  array_encoding_optionst array_encoding = {},
  btor2_property_optionst properties = {});

#endif // CPROVER_GOTO_BTOR2_GOTO_BTOR2_H
