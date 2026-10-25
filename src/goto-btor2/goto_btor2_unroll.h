// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

/*******************************************************************\

Module: Goto 程序常量界循环展开 - 声明

Authors: C2BTOR contributors; CBMC attribution is retained in LICENSES/

\*******************************************************************/

/// \file
/// 容量分析辅助：仅在私有分析副本上，对"循环体包含 malloc/allocate 且有
/// 有可靠有限上界"的 counted loop 做权重摘要，不修改输出 CFG/PC。
///
/// 副本中的 allocate 权重用于推导 fresh 对象身份所需的存储槽位。
/// 无法证明分配总次数的程序仍由转换器拒绝。
///
/// 安全边界：仅处理直线入口常量、无整数回绕、无计数变量别名、且每条
/// 回边路径有同向正进度的循环；无更新的内部环和早退路径可保留。

#ifndef CPROVER_GOTO_BTOR2_GOTO_BTOR2_UNROLL_H
#define CPROVER_GOTO_BTOR2_GOTO_BTOR2_UNROLL_H

#include <goto-programs/goto_program.h>
#include <util/message.h>

#include <cstddef>

/// Summarize bounded counted loops on a private analysis copy for allocation sizing.
/// Returns the number of summarized loops. Never pass the output program here.
std::size_t unroll_malloc_counted_loops(
  goto_programt &program,
  const namespacet &ns,
  messaget &log);

#endif // CPROVER_GOTO_BTOR2_GOTO_BTOR2_UNROLL_H
