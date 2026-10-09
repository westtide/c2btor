/*******************************************************************\

Module: Goto 程序常量界循环展开 - 声明

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// 有界循环展开：仅对"循环体包含 malloc/allocate 且有静态已知常数界"
/// 的 counted loop 做 full-unroll。
///
/// 每个展开后的 allocate 指令获得独立对象身份。仍在循环中的分配点
/// 由转换器拒绝；共享一个 summary 对象不是一般成立的过近似。
///
/// 安全边界：仅处理直线入口常量、无整数回绕、无计数变量别名、且每条
/// 回边路径必经单次计数更新的循环；不能确定完整界限时跳过。

#ifndef CPROVER_GOTO_BTOR2_GOTO_BTOR2_UNROLL_H
#define CPROVER_GOTO_BTOR2_GOTO_BTOR2_UNROLL_H

#include <goto-programs/goto_model.h>
#include <util/message.h>

#include <cstddef>

/// 在 main 函数体上反复扫描 counted loop 并做常量界 full-unroll。
/// 仅展开循环体含 malloc/allocate 的循环。返回实际展开的循环数。
std::size_t unroll_malloc_counted_loops(goto_modelt &goto_model,
                                        messaget &log);

#endif // CPROVER_GOTO_BTOR2_GOTO_BTOR2_UNROLL_H
