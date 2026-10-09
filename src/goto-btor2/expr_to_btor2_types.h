/*******************************************************************\

Module: 表达式到 BTOR2 转换 - 辅助类型定义

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// 表达式到 BTOR2 转换所需的辅助数据类型
///
/// 本文件定义了 expr_to_btor2t 在处理标量化数组和指针目标解析时
/// 使用的共享数据结构。将这些类型放在独立头文件中可以避免循环依赖。

#ifndef CPROVER_GOTO_BTOR2_EXPR_TO_BTOR2_TYPES_H
#define CPROVER_GOTO_BTOR2_EXPR_TO_BTOR2_TYPES_H

#include "btor2_builder.h"

#include <util/expr.h>
#include <util/mp_arith.h>

#include <vector>
#include <utility>

/// 标量化数组信息
///
/// 小型固定大小数组被拆分为逐元素的 BTOR2 状态变量，
/// 以避免某些下游模型检查器（如 IC3）对 BTOR2 数组类型的处理困难。
/// 例如 int a[4] 会被拆分为 a$elem$0, a$elem$1, a$elem$2, a$elem$3
/// 四个独立的 BTOR2 状态变量。
struct scalar_array_infot
{
  typet storage_type;                    ///< 原始数组的 BTOR2 存储类型
  typet element_type;                    ///< 数组元素类型
  std::vector<btor2_nid_t> element_nids; ///< 逐元素状态变量的 BTOR2 节点 ID
};

/// 指针目标描述
///
/// 描述一个指针指向的具体内存对象。在 BTOR2 中没有原生指针类型，
/// 指针被建模为 (对象 ID, 元素索引) 对，其中：
/// - array_id 标识指针指向的后备数组对象
/// - index 表示在该数组中的元素偏移量
struct pointer_targett
{
  irep_idt array_id;         ///< 后备数组对象的符号标识符
  exprt index;               ///< 元素偏移索引（以元素为单位）
  typet element_type;        ///< 指针指向的元素类型
  typet storage_type;        ///< 后备对象的 BTOR2 存储类型
  exprt element_stride;      ///< 每个元素包含的展平后子元素数（用于多维数组）
  exprt object_size_bytes;   ///< 对象总大小（字节数），用于 object_size 谓词
};

/// 条件指针目标描述
///
/// 用于处理条件指针赋值，如 `p = cond ? &a[0] : &b[0]`。
/// 每个守卫-目标对表示"在 guard 为真时，指针指向 target"。
/// 对 *(p + i) 的解引用会被下推为 ITE(guard, read(a, i), read(b, i))。
struct conditional_pointer_targett
{
  /// 守卫条件与指针目标的对应列表
  std::vector<std::pair<exprt, pointer_targett>> guarded_targets;
};

#endif // CPROVER_GOTO_BTOR2_EXPR_TO_BTOR2_TYPES_H
