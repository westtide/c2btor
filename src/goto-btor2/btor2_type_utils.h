/*******************************************************************\

Module: BTOR2 类型工具

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// BTOR2 类型工具函数
///
/// 本文件提供了 CBMC 类型系统到 BTOR2 类型系统的辅助工具函数，包括：
/// - tag 类型解析（struct_tag/union_tag/c_enum_tag → 具体类型）
/// - 灵活数组成员检测（C99 flexible array member）
/// - 多维数组维度提取
/// - 嵌套数组类型展平
/// - 多维数组索引线性化

#ifndef CPROVER_GOTO_BTOR2_BTOR2_TYPE_UTILS_H
#define CPROVER_GOTO_BTOR2_BTOR2_TYPE_UTILS_H

#include <util/namespace.h>
#include <util/std_types.h>
#include <util/expr.h>
#include <util/simplify_expr.h>

#include <optional>
#include <vector>

/// 单个数组维度的信息
struct array_dimt
{
  typet index_type; ///< 索引类型（如 signedbv_typet(32)）
  exprt size;       ///< 数组大小表达式（可能为 nil 表示未知大小）
};

/// 解析 tag 类型为具体类型
/// 将 struct_tag → struct, union_tag → union, c_enum_tag → c_enum
/// @param type 输入类型
/// @param ns 命名空间
/// @return 解析后的具体类型，非 tag 类型原样返回
typet follow_tag_type(const typet &type, const namespacet &ns);

/// 检测结构体成员是否为灵活数组成员（C99 flexible array member）
/// 灵活数组成员的特征是大小为 0 或 nil 的数组类型
/// @param component 结构体成员
/// @param ns 命名空间
/// @return 如果是灵活数组成员返回 true
bool is_flexible_array_member_component(
  const struct_typet::componentt &component,
  const namespacet &ns);

/// 递归提取（可能嵌套的）数组类型的所有维度信息
/// 例如 array(array(int, M), N) 会提取出 [N, M] 两个维度
/// @param type 输入类型
/// @param ns 命名空间
/// @param dims 输出：提取到的维度列表（从外到内）
/// @param leaf_type 输出：最内层非数组元素类型
void get_array_dimensions(
  const typet &type,
  const namespacet &ns,
  std::vector<array_dimt> &dims,
  typet &leaf_type);

/// 将嵌套的多维数组类型展平为一维数组类型
/// 例如 array(array(int, M), N) → array(int, N*M)
/// @param type 输入类型
/// @param ns 命名空间
/// @return 展平后的类型（一维数组或原始标量类型）
typet flatten_array_type(const typet &type, const namespacet &ns);

/// 将多维数组的多个索引线性化为单个一维索引
/// 例如 a[i][j] 在 array(array(T, M), N) 中 → i * M + j
/// @param type 数组的逻辑类型
/// @param indices 各维度的索引表达式（从外到内）
/// @param ns 命名空间
/// @return 线性化后的索引表达式，失败返回 nullopt
std::optional<exprt> linearize_array_indices(
  const typet &type,
  const std::vector<exprt> &indices,
  const namespacet &ns);

#endif // CPROVER_GOTO_BTOR2_BTOR2_TYPE_UTILS_H
