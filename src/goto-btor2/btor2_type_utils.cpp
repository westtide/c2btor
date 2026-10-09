/*******************************************************************\

Module: BTOR2 类型工具 - 实现

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// BTOR2 类型工具函数实现
///
/// 本文件实现了 CBMC 类型到 BTOR2 类型的辅助转换函数，包括 tag 类型解析、
/// 灵活数组成员检测、多维数组展平和索引线性化。

#include "btor2_type_utils.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_offset_size.h>
#include <util/std_types.h>

typet follow_tag_type(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_struct_tag)
    return ns.follow_tag(to_struct_tag_type(type));
  if(type.id() == ID_union_tag)
    return ns.follow_tag(to_union_tag_type(type));
  if(type.id() == ID_c_enum_tag)
    return ns.follow_tag(to_c_enum_tag_type(type));
  return type;
}

bool is_flexible_array_member_component(
  const struct_typet::componentt &component,
  const namespacet &ns)
{
  const typet t = follow_tag_type(component.type(), ns);
  if(t.id() != ID_array)
    return false;

  const auto &array_type = to_array_type(t);
  const auto declared_size = numeric_cast<mp_integer>(array_type.size());
  return array_type.size().is_nil() ||
         (declared_size.has_value() && *declared_size == 0);
}

void get_array_dimensions(
  const typet &type,
  const namespacet &ns,
  std::vector<array_dimt> &dims,
  typet &leaf_type)
{
  typet current = follow_tag_type(type, ns);
  while(current.id() == ID_array)
  {
    const auto &array_type = to_array_type(current);
    dims.push_back(array_dimt{array_type.index_type(), array_type.size()});
    current = follow_tag_type(array_type.element_type(), ns);
  }

  leaf_type = current;
}

typet flatten_array_type(const typet &type, const namespacet &ns)
{
  std::vector<array_dimt> dims;
  typet leaf_type;
  get_array_dimensions(type, ns, dims, leaf_type);

  if(dims.empty())
    return follow_tag_type(type, ns);

  if(dims.size() == 1)
  {
    array_typet result = to_array_type(follow_tag_type(type, ns));
    result.element_type() = leaf_type;
    return result;
  }

  const typet &index_type = dims.front().index_type;
  exprt total_size = from_integer(1, index_type);

  for(const auto &dim : dims)
  {
    if(dim.size.is_nil())
    {
      array_typet result(leaf_type, nil_exprt());
      result.index_type_nonconst() = index_type;
      return result;
    }

    exprt cast_size =
      simplify_expr(typecast_exprt::conditional_cast(dim.size, index_type), ns);
    total_size = mult_exprt(total_size, cast_size);
    total_size.type() = index_type;
    total_size = simplify_expr(total_size, ns);
  }

  array_typet result(leaf_type, total_size);
  result.index_type_nonconst() = index_type;
  return result;
}

std::optional<exprt> linearize_array_indices(
  const typet &type,
  const std::vector<exprt> &indices,
  const namespacet &ns)
{
  std::vector<array_dimt> dims;
  typet leaf_type;
  get_array_dimensions(type, ns, dims, leaf_type);

  if(dims.empty() || indices.empty() || indices.size() > dims.size())
    return std::nullopt;

  if(dims.size() > 1 && indices.size() < dims.size())
    return std::nullopt;

  const typet &index_type = dims.front().index_type;
  exprt linear = from_integer(0, index_type);

  for(std::size_t i = 0; i < indices.size(); ++i)
  {
    exprt idx =
      simplify_expr(typecast_exprt::conditional_cast(indices[i], index_type), ns);

    exprt multiplier = from_integer(1, index_type);
    for(std::size_t j = i + 1; j < dims.size(); ++j)
    {
      if(dims[j].size.is_nil())
        return std::nullopt;

      exprt cast_size = simplify_expr(
        typecast_exprt::conditional_cast(dims[j].size, index_type), ns);
      multiplier = mult_exprt(multiplier, cast_size);
      multiplier.type() = index_type;
      multiplier = simplify_expr(multiplier, ns);
    }

    exprt term = idx;
    auto multiplier_value = numeric_cast<mp_integer>(multiplier);
    if(!(multiplier_value.has_value() && *multiplier_value == 1))
    {
      term = mult_exprt(idx, multiplier);
      term.type() = index_type;
      term = simplify_expr(term, ns);
    }

    linear = plus_exprt(linear, term);
    linear.type() = index_type;
    linear = simplify_expr(linear, ns);
  }

  return linear;
}
