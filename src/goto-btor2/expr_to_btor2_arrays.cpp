/*******************************************************************\

Module: Expression-to-BTOR2 conversion -- array operations

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// 数组相关表达式到 BTOR2 的转换
///
/// 本翻译单元包含 expr_to_btor2t 中数组操作的转换方法：
/// - convert_index: 数组索引（read），包括标量化数组的 ITE mux 读取
/// - convert_array: 数组字面量
/// - convert_array_of: 重复填充数组
/// - convert_with: 数组更新（write）
/// - read_scalar_array: 从标量化数组中通过 ITE 链读取元素
///
/// 数组访问经过多层解析：
/// 1. 首先尝试通过指针目标解析直接读取标量化数组的元素
/// 2. 然后尝试将复合表达式（如 (*p)[i]、s.field[i]）分解为符号访问
/// 3. 最后回退到通用的 BTOR2 read 操作

#include "expr_to_btor2.h"
#include "btor2_type_utils.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol.h>

#include <functional>

namespace
{

static irep_idt append_member_path(
  const irep_idt &base_id,
  const std::vector<irep_idt> &member_path)
{
  std::string flat_id = id2string(base_id);
  for(const auto &member : member_path)
    flat_id += "." + id2string(member);
  return irep_idt(flat_id);
}

struct array_view_infot
{
  exprt base_index;
  typet referent_type;
};

static std::optional<typet> project_member_type_through_arrays(
  const typet &root_type,
  const std::vector<irep_idt> &member_path,
  const namespacet &ns)
{
  std::function<std::optional<typet>(const typet &, std::size_t)> project =
    [&](const typet &type, std::size_t idx) -> std::optional<typet> {
    if(idx >= member_path.size())
      return follow_tag_type(type, ns);

    const typet current = follow_tag_type(type, ns);
    if(current.id() == ID_array)
    {
      const auto &array_type = to_array_type(current);
      auto projected_elem = project(array_type.element_type(), idx);
      if(!projected_elem.has_value())
        return std::nullopt;
      array_typet projected = array_type;
      projected.element_type() = *projected_elem;
      return projected;
    }

    if(current.id() != ID_struct && current.id() != ID_union)
      return std::nullopt;

    const auto &components =
      current.id() == ID_struct
        ? to_struct_type(current).components()
        : to_union_type(current).components();
    const irep_idt want = member_path[idx];
    for(const auto &component : components)
    {
      if(
        component.get_bool(ID_C_is_padding) &&
        !is_flexible_array_member_component(component, ns))
        continue;

      if(component.get_name() == want)
        return project(component.type(), idx + 1);
    }

    return std::nullopt;
  };

  return project(root_type, 0);
}

struct decomposed_symbol_accesst
{
  irep_idt root_id;
  typet root_type;
  std::vector<irep_idt> member_path;
  std::vector<exprt> indices;
};

static std::optional<decomposed_symbol_accesst> decompose_symbol_access(
  const exprt &expr,
  const namespacet &ns)
{
  std::function<std::optional<decomposed_symbol_accesst>(const exprt &)> decompose =
    [&](const exprt &current) -> std::optional<decomposed_symbol_accesst> {
    if(current.id() == ID_symbol)
    {
      const auto &symbol = to_symbol_expr(current);
      return decomposed_symbol_accesst{
        symbol.get_identifier(),
        follow_tag_type(symbol.type(), ns),
        {},
        {}};
    }

    if(current.id() == ID_member)
    {
      const auto &member = to_member_expr(current);
      auto base = decompose(member.compound());
      if(!base.has_value())
        return std::nullopt;
      base->member_path.push_back(member.get_component_name());
      return base;
    }

    if(current.id() == ID_index)
    {
      const auto &index = to_index_expr(current);
      auto base = decompose(index.array());
      if(!base.has_value())
        return std::nullopt;
      base->indices.push_back(index.index());
      return base;
    }

    return std::nullopt;
  };

  return decompose(expr);
}

static std::optional<array_view_infot> compute_array_view(
  const typet &type,
  const std::vector<exprt> &indices,
  const namespacet &ns)
{
  std::vector<array_dimt> dims;
  typet leaf_type;
  get_array_dimensions(type, ns, dims, leaf_type);

  if(indices.size() > dims.size())
    return std::nullopt;

  const typet &index_type =
    dims.empty() ? signedbv_typet(64) : dims.front().index_type;
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

  typet referent_type = follow_tag_type(type, ns);
  for(std::size_t i = 0; i < indices.size(); ++i)
  {
    if(referent_type.id() != ID_array)
      return std::nullopt;
    referent_type = follow_tag_type(
      to_array_type(referent_type).element_type(), ns);
  }

  return array_view_infot{linear, referent_type};
}

} // namespace

btor2_nid_t expr_to_btor2t::read_scalar_array(
  const irep_idt &id,
  const exprt &index_expr,
  const typet &target_type)
{
  auto it = scalar_array_map.find(id);
  if(it == scalar_array_map.end())
    return 0;

  const auto &info = it->second;
  if(info.storage_type.id() != ID_array || info.element_nids.empty())
    return 0;

  const auto &array_type = to_array_type(info.storage_type);
  exprt cast_index = simplify_expr(
    typecast_exprt::conditional_cast(index_expr, array_type.index_type()),
    ns);
  btor2_nid_t index_nid = convert(cast_index);
  btor2_nid_t elem_sort = convert_type(info.element_type);
  btor2_nid_t target_sort = convert_type(target_type);
  if(index_nid == 0 || elem_sort == 0 || target_sort == 0 || elem_sort != target_sort)
    return 0;

  btor2_nid_t value = builder.input(
    elem_sort,
    "__scalar_array_read_default$" + std::to_string(nondet_counter++));
  const btor2_nid_t bool_sort = builder.get_bool_sort();
  for(std::size_t i = info.element_nids.size(); i-- > 0;)
  {
    btor2_nid_t idx_const =
      builder.constd(convert_type(array_type.index_type()), mp_integer(i));
    btor2_nid_t is_match = builder.eq(bool_sort, index_nid, idx_const);
    value = builder.ite(elem_sort, is_match, info.element_nids[i], value);
  }

  return value;
}

btor2_nid_t expr_to_btor2t::convert_index(const index_exprt &expr)
{
  // Union and byte-level accesses are commonly represented as an index into
  // an array-valued byte_extract expression, for example
  //   byte_extract_big_endian(word, 0, unsigned char[4])[i].
  // Materialising that intermediate array is unnecessary and was previously
  // unsupported, causing assertion conditions to fall back to fresh
  // nondeterministic booleans.  Decode each finite element directly from the
  // source bit-vector and mux on the runtime index.
  if(
    expr.array().id() == ID_byte_extract_little_endian ||
    expr.array().id() == ID_byte_extract_big_endian)
  {
    const exprt &byte_extract = expr.array();
    const auto &extract_ops = to_binary_expr(byte_extract);
    const exprt &source = extract_ops.op0();
    const exprt &offset_expr = extract_ops.op1();
    const auto source_width = get_width(source.type());
    const auto element_width = get_width(expr.type());
    const auto offset = numeric_cast<mp_integer>(offset_expr);
    const auto &array_type = to_array_type(byte_extract.type());
    const auto length_mp = numeric_cast<mp_integer>(array_type.size());
    const auto length =
      length_mp.has_value() && *length_mp >= 0
        ? numeric_castt<std::size_t>{}(*length_mp)
        : std::optional<std::size_t>{};

    if(
      source_width.has_value() && element_width.has_value() &&
      offset.has_value() && *offset >= 0 && length.has_value())
    {
      const mp_integer base_bits = *offset * 8;
      const mp_integer total_bits = *length * *element_width;
      if(base_bits + total_bits <= *source_width)
      {
        btor2_nid_t source_nid = convert(source);
        exprt index_expr = simplify_expr(
          typecast_exprt::conditional_cast(
            expr.index(), array_type.index_type()),
          ns);
        btor2_nid_t index_nid = convert(index_expr);
        btor2_nid_t index_sort = convert_type(array_type.index_type());
        btor2_nid_t element_sort = convert_type(expr.type());
        if(
          source_nid != 0 && index_nid != 0 && index_sort != 0 &&
          element_sort != 0)
        {
          btor2_nid_t value = builder.input(
            element_sort,
            "__byte_extract_index_default$" +
              std::to_string(nondet_counter++));
          const btor2_nid_t bool_sort = builder.get_bool_sort();
          for(std::size_t i = *length; i-- > 0;)
          {
            mp_integer low = base_bits + i * *element_width;
            if(byte_extract.id() == ID_byte_extract_big_endian)
            {
              low = *source_width - base_bits -
                    (mp_integer(i) + 1) * *element_width;
            }
            const unsigned low_bit = numeric_cast_v<unsigned>(low);
            const unsigned high_bit =
              numeric_cast_v<unsigned>(low + *element_width - 1);
            btor2_nid_t element = builder.slice(
              element_sort, source_nid, high_bit, low_bit);
            btor2_nid_t is_index = builder.eq(
              bool_sort,
              index_nid,
              builder.constd(index_sort, mp_integer(i)));
            value = builder.ite(element_sort, is_index, element, value);
          }
          return value;
        }
      }
    }
  }

  // First try to resolve the indexed expression as an addressable scalar
  // element of some backing object. This bypasses intermediate array-valued
  // nodes such as `(*row)[0]` or `m.data[0][1]` and lets scalarized storage
  // answer the read directly from its flattened element states.
  auto direct_target = resolve_pointer_target(address_of_exprt(expr));
  if(direct_target.has_value())
  {
    btor2_nid_t scalar_read =
      read_scalar_array(direct_target->array_id, direct_target->index, expr.type());
    if(scalar_read != 0)
      return scalar_read;
  }

  auto convert_pointer_backed_array_index =
    [&](const exprt &array_expr) -> btor2_nid_t {
    address_of_exprt array_addr(array_expr);
    auto target_opt = resolve_pointer_target(array_addr);
    if(!target_opt.has_value())
      return 0;

    const auto &target = *target_opt;
    const typet access_type = follow_tag_type(array_expr.type(), ns);
    auto base_nid_opt = lookup_symbol(target.array_id);
    auto storage_type_opt =
      target.storage_type.is_nil()
        ? lookup_symbol_type(target.array_id)
        : std::optional<typet>{target.storage_type};

    if(
      !storage_type_opt.has_value() || storage_type_opt->id() != ID_array ||
      access_type.id() != ID_array)
      return 0;

    std::vector<exprt> inner_indices{expr.index()};
    auto view_opt = compute_array_view(access_type, inner_indices, ns);
    if(!view_opt.has_value())
      return 0;

    const auto &base_storage = to_array_type(*storage_type_opt);
    exprt inner_index = simplify_expr(
      typecast_exprt::conditional_cast(view_opt->base_index, target.index.type()),
      ns);
    exprt actual_index = plus_exprt(target.index, inner_index);
    actual_index.type() = target.index.type();
    actual_index = simplify_expr(actual_index, ns);

    exprt index_cast = simplify_expr(
      typecast_exprt::conditional_cast(actual_index, base_storage.index_type()),
      ns);
    btor2_nid_t scalar_read =
      read_scalar_array(target.array_id, index_cast, expr.type());
    if(scalar_read != 0)
      return scalar_read;

    if(!base_nid_opt.has_value())
      return 0;

    btor2_nid_t index_nid = convert(index_cast);
    btor2_nid_t elem_sort = convert_type(expr.type());
    if(index_nid == 0 || elem_sort == 0)
      return 0;

    return builder.read(elem_sort, *base_nid_opt, index_nid);
  };

  if(expr.array().id() == ID_dereference || expr.array().id() == ID_member)
  {
    btor2_nid_t pointer_backed_read =
      convert_pointer_backed_array_index(expr.array());
    if(pointer_backed_read != 0)
      return pointer_backed_read;
  }

  auto decomposed_opt = decompose_symbol_access(expr, ns);
  if(decomposed_opt.has_value())
  {
    const auto &decomposed = *decomposed_opt;
    const irep_idt var_id =
      decomposed.member_path.empty()
        ? decomposed.root_id
        : append_member_path(decomposed.root_id, decomposed.member_path);

    typet logical_type = decomposed.root_type;
    if(!decomposed.member_path.empty())
    {
      auto projected_opt = project_member_type_through_arrays(
        decomposed.root_type, decomposed.member_path, ns);
      if(projected_opt.has_value())
        logical_type = *projected_opt;
    }

    auto flat_index_opt =
      logical_type.id() == ID_array
        ? linearize_array_indices(logical_type, decomposed.indices, ns)
        : std::nullopt;
    if(flat_index_opt.has_value())
    {
      btor2_nid_t scalar_read = read_scalar_array(var_id, *flat_index_opt, expr.type());
      if(scalar_read != 0)
        return scalar_read;

      auto base_nid_opt = lookup_symbol(var_id);
      if(base_nid_opt.has_value())
      {
        const typet storage_type = flatten_array_type(logical_type, ns);
        if(storage_type.id() == ID_array)
        {
          const auto &storage_array_type = to_array_type(storage_type);
          exprt index_expr = simplify_expr(
            typecast_exprt::conditional_cast(
              *flat_index_opt, storage_array_type.index_type()),
            ns);
          btor2_nid_t index_nid = convert(index_expr);
          btor2_nid_t elem_sort = convert_type(expr.type());
          if(index_nid != 0 && elem_sort != 0)
            return builder.read(elem_sort, *base_nid_opt, index_nid);
        }
      }
    }
  }

  // Pass the complete access p->array[i] to the runtime member dispatcher.
  // Converting p->array first would ask its scalarized element mux to produce
  // an array value, creating an ill-sorted BTOR2 ite/read.
  const exprt *root = &expr;
  bool has_member = false;
  while(root->id() == ID_index || root->id() == ID_member)
  {
    if(root->id() == ID_member)
    {
      has_member = true;
      root = &to_member_expr(*root).compound();
    }
    else
      root = &to_index_expr(*root).array();
  }
  if(has_member && root->id() == ID_dereference)
    return convert_member(expr);

  typet array_type_raw = expr.array().type();
  if(array_type_raw.id() != ID_array)
    return 0;
  const auto &array_type = to_array_type(array_type_raw);

  btor2_nid_t array_nid = convert(expr.array());
  exprt index_expr =
    typecast_exprt::conditional_cast(expr.index(), array_type.index_type());
  btor2_nid_t index_nid = convert(index_expr);

  if(array_nid == 0 || index_nid == 0)
    return 0;

  btor2_nid_t elem_sort = convert_type(array_type.element_type());
  if(elem_sort == 0)
    return 0;

  btor2_nid_t read_nid = builder.read(elem_sort, array_nid, index_nid);

  btor2_nid_t target_sort = convert_type(expr.type());
  if(target_sort == 0)
    return 0;
  if(target_sort == elem_sort)
    return read_nid;

  index_exprt read_expr(expr.array(), index_expr, array_type.element_type());
  typecast_exprt cast_expr(read_expr, expr.type());
  return convert_typecast(cast_expr);
}

btor2_nid_t expr_to_btor2t::convert_array(const array_exprt &expr)
{
  if(expr.type().id() != ID_array)
    return 0;

  btor2_nid_t array_sort = convert_type(expr.type());
  if(array_sort == 0)
    return 0;

  const auto &array_type = to_array_type(expr.type());
  auto len_mp_opt = numeric_cast<mp_integer>(array_type.size());
  if(!len_mp_opt.has_value() || *len_mp_opt < 0)
    return 0;

  const auto len_opt = numeric_castt<std::size_t>{}(*len_mp_opt);
  if(!len_opt.has_value())
    return 0;

  btor2_nid_t index_sort = convert_type(array_type.index_type());
  btor2_nid_t elem_sort = convert_type(array_type.element_type());
  if(index_sort == 0 || elem_sort == 0)
    return 0;

  btor2_nid_t array_nid = builder.input(
    array_sort,
    "__array_literal_base$" + std::to_string(array_literal_counter++));
  btor2_nid_t zero_elem = builder.zero(elem_sort);

  for(std::size_t i = 0; i < *len_opt; ++i)
  {
    btor2_nid_t idx = builder.constd(index_sort, mp_integer(i));
    array_nid = builder.write(array_sort, array_nid, idx, zero_elem);
  }

  const std::size_t bound = std::min(*len_opt, expr.operands().size());
  for(std::size_t i = 0; i < bound; ++i)
  {
    const exprt &op = expr.operands()[i];
    if(op.is_nil())
      continue;

    exprt value_expr =
      typecast_exprt::conditional_cast(op, array_type.element_type());
    btor2_nid_t value_nid = convert(value_expr);
    if(value_nid == 0)
      return 0;

    btor2_nid_t idx = builder.constd(index_sort, mp_integer(i));
    array_nid = builder.write(array_sort, array_nid, idx, value_nid);
  }

  return array_nid;
}

btor2_nid_t expr_to_btor2t::convert_array_of(const array_of_exprt &expr)
{
  if(expr.type().id() != ID_array)
    return 0;

  btor2_nid_t array_sort = convert_type(expr.type());
  if(array_sort == 0)
    return 0;

  const auto &array_type = to_array_type(expr.type());
  auto len_mp_opt = numeric_cast<mp_integer>(array_type.size());
  if(!len_mp_opt.has_value() || *len_mp_opt < 0)
    return 0;

  const auto len_opt = numeric_castt<std::size_t>{}(*len_mp_opt);
  if(!len_opt.has_value())
    return 0;

  btor2_nid_t index_sort = convert_type(array_type.index_type());
  btor2_nid_t elem_sort = convert_type(array_type.element_type());
  if(index_sort == 0 || elem_sort == 0)
    return 0;

  exprt value_expr =
    typecast_exprt::conditional_cast(expr.what(), array_type.element_type());
  btor2_nid_t value_nid = convert(value_expr);
  if(value_nid == 0)
    return 0;

  btor2_nid_t array_nid = builder.input(
    array_sort,
    "__array_of_base$" + std::to_string(array_literal_counter++));

  for(std::size_t i = 0; i < *len_opt; ++i)
  {
    btor2_nid_t idx = builder.constd(index_sort, mp_integer(i));
    array_nid = builder.write(array_sort, array_nid, idx, value_nid);
  }

  return array_nid;
}

btor2_nid_t expr_to_btor2t::convert_with(const with_exprt &expr)
{
  btor2_nid_t array_nid = convert(expr.old());

  if(array_nid == 0)
    return 0;

  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  if(expr.type().id() != ID_array)
    return 0;

  const auto &array_type = to_array_type(expr.type());
  const typet &index_type = array_type.index_type();
  const typet &element_type = array_type.element_type();

  // 处理更新操作对：(index, value)
  // with 表达式格式: with(old_array, index1, value1, index2, value2, ...)
  for(std::size_t i = 1; i + 1 < expr.operands().size(); i += 2)
  {
    exprt index_expr =
      typecast_exprt::conditional_cast(expr.operands()[i], index_type);
    exprt value_expr =
      typecast_exprt::conditional_cast(expr.operands()[i + 1], element_type);

    btor2_nid_t index_nid = convert(index_expr);
    btor2_nid_t value_nid = convert(value_expr);

    if(index_nid == 0 || value_nid == 0)
      return 0;

    // 连续写入操作
    array_nid = builder.write(sort, array_nid, index_nid, value_nid);
  }

  return array_nid;
}
