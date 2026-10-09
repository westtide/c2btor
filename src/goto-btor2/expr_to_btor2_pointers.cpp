/*******************************************************************\

Module: Expression-to-BTOR2 conversion -- pointer operations

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// 指针相关表达式到 BTOR2 的转换
///
/// 本翻译单元实现了指针操作的 BTOR2 转换。BTOR2 没有原生指针类型，
/// 指针通过以下模型表示：
///
/// 指针表示模型：
/// - 每个可寻址对象（全局变量、局部数组、malloc 分配的堆对象）对应
///   一个唯一的对象 ID（正整数常量）
/// - 指针值 = 对象 ID（存储为位向量常量）
/// - 解引用通过 resolve_pointer_target 找到后备 BTOR2 数组，然后用
///   read 操作读取对应索引位置的值
///
/// 包含的转换方法：
/// - resolve_pointer_target: 将指针表达式解析为 (array_id, index) 对
/// - resolve_conditional_pointer_target: 处理条件指针（如 p = c ? &a : &b）
/// - convert_address_of: 取地址 → 对象 ID 常量
/// - convert_dereference: 解引用 → BTOR2 read
/// - convert_pointer_object: pointer_object() → 对象 ID
/// - convert_pointer_offset: pointer_offset() → 字节偏移
/// - convert_object_size: object_size() → 对象大小
/// - convert_is_invalid_pointer / convert_is_dynamic_object: 指针谓词
/// - convert_prophecy_r_or_w_ok: prophecy 读/写合法性检查
/// - convert_member: 结构体成员访问（展平后的符号查找）
/// - get_object_id: 获取或分配对象 ID

#include "expr_to_btor2.h"
#include "btor2_type_utils.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol.h>
#include <util/string_constant.h>

#include <algorithm>
#include <functional>

namespace
{

// Character arrays share the same bit-vector storage regardless of signedness.
// In particular, the memcpy model's signed char temporary must remain visible
// through the unsigned char pointers used by byte-operation lowering.
static bool same_pointer_storage_type(
  const typet &lhs,
  const typet &rhs,
  const namespacet &ns)
{
  const typet left = follow_tag_type(lhs, ns);
  const typet right = follow_tag_type(rhs, ns);
  const auto is_character_storage = [](const typet &type) {
    return (type.id() == ID_signedbv || type.id() == ID_unsignedbv) &&
           to_bitvector_type(type).get_width() == config.ansi_c.char_width;
  };
  return left == right ||
         (is_character_storage(left) && is_character_storage(right));
}

static bool is_zero_integer_expr(const exprt &expr)
{
  if(!expr.is_constant())
    return false;

  mp_integer value;
  return !to_integer(to_constant_expr(expr), value) && value == 0;
}

static exprt zero_pointer_index()
{
  return from_integer(0, signedbv_typet(64));
}

static std::optional<typet> project_member_type(
  const typet &root_type,
  const std::vector<irep_idt> &member_path,
  const namespacet &ns)
{
  typet current = follow_tag_type(root_type, ns);

  for(const auto &member : member_path)
  {
    if(current.id() != ID_struct && current.id() != ID_union)
      return std::nullopt;

    const auto &components =
      current.id() == ID_struct
        ? to_struct_type(current).components()
        : to_union_type(current).components();
    bool found = false;
    for(const auto &component : components)
    {
      if(
        component.get_bool(ID_C_is_padding) &&
        !is_flexible_array_member_component(component, ns))
        continue;

      if(component.get_name() == member)
      {
        current = follow_tag_type(component.type(), ns);
        found = true;
        break;
      }
    }

    if(!found)
      return std::nullopt;
  }

  return current;
}

static irep_idt append_member_path(
  const irep_idt &base_id,
  const std::vector<irep_idt> &member_path)
{
  std::string flat_id = id2string(base_id);
  for(const auto &member : member_path)
    flat_id += "." + id2string(member);
  return irep_idt(flat_id);
}

static typet project_member_storage_type(
  const typet &storage_type,
  const typet &leaf_type,
  const namespacet &ns)
{
  const typet t = follow_tag_type(storage_type, ns);
  if(t.id() != ID_array)
    return leaf_type;

  std::vector<typet> index_types;
  std::vector<exprt> sizes;

  typet current = t;
  while(current.id() == ID_array)
  {
    const auto &array_type = to_array_type(current);
    index_types.push_back(array_type.index_type());
    sizes.push_back(array_type.size());
    current = follow_tag_type(array_type.element_type(), ns);
  }

  typet current_leaf = follow_tag_type(leaf_type, ns);
  while(current_leaf.id() == ID_array)
  {
    const auto &array_type = to_array_type(current_leaf);
    index_types.push_back(array_type.index_type());
    sizes.push_back(array_type.size());
    current_leaf = follow_tag_type(array_type.element_type(), ns);
  }

  if(index_types.empty())
    return current_leaf;

  if(index_types.size() == 1)
  {
    array_typet result(current_leaf, sizes.front());
    result.index_type_nonconst() = index_types.front();
    return result;
  }

  const typet &index_type = index_types.front();
  exprt total_size = from_integer(1, index_type);
  for(const auto &size : sizes)
  {
    if(size.is_nil())
    {
      array_typet result(current_leaf, nil_exprt());
      result.index_type_nonconst() = index_type;
      return result;
    }

    exprt cast_size =
      simplify_expr(typecast_exprt::conditional_cast(size, index_type), ns);
    total_size = mult_exprt(total_size, cast_size);
    total_size.type() = index_type;
    total_size = simplify_expr(total_size, ns);
  }

  array_typet result(current_leaf, total_size);
  result.index_type_nonconst() = index_type;
  return result;
}

struct array_view_infot
{
  exprt base_index;
  typet referent_type;
};

static exprt flattened_element_count(const typet &type, const namespacet &ns)
{
  const typet flattened = flatten_array_type(type, ns);
  if(flattened.id() != ID_array)
    return from_integer(1, signedbv_typet(64));

  const auto &array_type = to_array_type(flattened);
  if(!array_type.size().is_nil())
    return array_type.size();

  return nil_exprt();
}

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

static bool same_follow_type(
  const typet &lhs,
  const typet &rhs,
  const namespacet &ns)
{
  return follow_tag_type(lhs, ns) == follow_tag_type(rhs, ns);
}

} // namespace

std::optional<pointer_targett>
expr_to_btor2t::resolve_pointer_target(const exprt &expr) const
{
  // Canonical target form used by BTOR2 lowering:
  //   pointer_expr  ==>  (base_array_symbol, element_index, element_type)
  // This lets dereference/address-of/pointer predicates be translated through
  // BTOR2 read/write + object-id constants without native pointer sorts.
  auto make_target = [&](const irep_idt &object_id,
                         const exprt &index,
                         const typet &element_type,
                         const typet &object_type,
                         const typet &storage_type) -> pointer_targett {
    auto size_opt = size_of_expr(object_type, ns);
    exprt object_size_bytes = nil_exprt();
    if(size_opt.has_value())
      object_size_bytes = *size_opt;
    else if(follow_tag_type(object_type, ns).id() == ID_code)
      object_size_bytes = from_integer(0, signedbv_typet(64));

    // Pointer arithmetic scales by the pointed-to type, not by the size of the
    // whole backing object. We keep `object_type` for object_size reasoning,
    // but `element_stride` must follow `element_type` so `&a[0] + 1` advances
    // one element and `row + 1` advances one whole row.
    exprt element_stride = flattened_element_count(element_type, ns);

    return pointer_targett{
      object_id,
      index,
      element_type,
      storage_type,
      element_stride,
      object_size_bytes};
  };

  auto resolve_member_target =
    [&](const member_exprt &member_expr, auto &&self) -> std::optional<pointer_targett> {
    std::vector<irep_idt> member_path;
    const exprt *cur = &member_expr;
    while(cur->id() == ID_member)
    {
      const auto &m = to_member_expr(*cur);
      member_path.push_back(m.get_component_name());
      cur = &m.compound();
    }
    std::reverse(member_path.begin(), member_path.end());

    exprt field_index = zero_pointer_index();
    irep_idt storage_id;
    typet storage_type;
    typet root_type;

    auto initialize_from_base_target =
      [&](const pointer_targett &base_target) -> bool {
      storage_id = base_target.array_id;
      field_index = base_target.index;

      // Synthetic heap objects used by malloc lowering do not live in the
      // symbol table. In that case we must carry their logical storage type
      // through pointer_targett instead of re-discovering it via ns.lookup().
      if(!base_target.storage_type.is_nil())
        storage_type = follow_tag_type(base_target.storage_type, ns);
      else
      {
        const symbolt *storage_symbol = nullptr;
        if(ns.lookup(storage_id, storage_symbol) || storage_symbol == nullptr)
          return false;
        storage_type = follow_tag_type(storage_symbol->type, ns);
      }

      const typet logical_storage_type = follow_tag_type(storage_type, ns);
      root_type =
        logical_storage_type.id() != ID_array ? logical_storage_type
                                              : follow_tag_type(base_target.element_type, ns);
      return true;
    };

    if(cur->id() == ID_symbol && cur->type().id() == ID_pointer)
    {
      auto base_target = resolve_pointer_target(*cur);
      if(!base_target.has_value() || !initialize_from_base_target(*base_target))
        return std::nullopt;
    }
    else if(cur->id() == ID_symbol)
    {
      const auto &sym = to_symbol_expr(*cur);
      storage_id = sym.get_identifier();
      storage_type = follow_tag_type(sym.type(), ns);
      root_type = storage_type;
    }
    else if(cur->id() == ID_dereference)
    {
      auto base_target =
        resolve_pointer_target(to_dereference_expr(*cur).pointer());
      if(!base_target.has_value() || !initialize_from_base_target(*base_target))
        return std::nullopt;
    }
    else if(cur->id() == ID_index)
    {
      address_of_exprt base_addr(*cur);
      auto base_target = resolve_pointer_target(base_addr);
      if(!base_target.has_value() || !initialize_from_base_target(*base_target))
        return std::nullopt;
    }
    else
    {
      auto base_target = resolve_pointer_target(*cur);
      if(!base_target.has_value() || !initialize_from_base_target(*base_target))
        return std::nullopt;
    }

    auto leaf_type_opt = project_member_type(root_type, member_path, ns);
    if(!leaf_type_opt.has_value())
      return std::nullopt;

    const irep_idt leaf_id = append_member_path(storage_id, member_path);
    const typet leaf_storage_type =
      project_member_storage_type(storage_type, *leaf_type_opt, ns);
    return make_target(
      leaf_id, field_index, *leaf_type_opt, *leaf_type_opt, leaf_storage_type);
  };

  if(expr.id() == ID_typecast)
  {
    auto target = resolve_pointer_target(to_typecast_expr(expr).op());
    if(
      target.has_value() && expr.type().id() == ID_pointer &&
      to_pointer_type(expr.type()).base_type().id() != ID_empty)
    {
      target->element_type =
        follow_tag_type(to_pointer_type(expr.type()).base_type(), ns);
      target->element_stride =
        flattened_element_count(target->element_type, ns);
    }
    return target;
  }

  if(expr.id() == ID_dereference)
  {
    auto container_target = resolve_pointer_target(to_dereference_expr(expr).pointer());
    if(!container_target.has_value())
      return std::nullopt;

    const symbolt *symbol = nullptr;
    if(
      !ns.lookup(container_target->array_id, symbol) && symbol != nullptr &&
      follow_tag_type(symbol->type, ns).id() == ID_pointer &&
      is_zero_integer_expr(container_target->index))
    {
      auto it = pointer_targets.find(container_target->array_id);
      if(it != pointer_targets.end())
      {
        auto target = it->second;
        if(
          expr.type().id() == ID_pointer &&
          to_pointer_type(expr.type()).base_type().id() != ID_empty)
        {
          target.element_type =
            follow_tag_type(to_pointer_type(expr.type()).base_type(), ns);
          target.element_stride =
            flattened_element_count(target.element_type, ns);
        }
        return target;
      }
    }

    auto target = *container_target;
    target.element_type = follow_tag_type(expr.type(), ns);
    target.element_stride = flattened_element_count(target.element_type, ns);
    return target;
  }

  if(expr.id() == ID_symbol)
  {
    const irep_idt &sym_id = to_symbol_expr(expr).get_identifier();
    // A collected pointer symbol is runtime state. A flow-insensitive static
    // target (even when it names one object) cannot determine its current
    // byte offset after loop iterations or assignments such as p=p->next.
    if(expr.type().id() == ID_pointer && lookup_symbol(sym_id).has_value())
      return std::nullopt;
    // If the pointer has been observed to target more than one distinct
    // backing array across the program, the single-entry pointer_targets
    // map (last-write-wins) is unsound.  Return nullopt so callers fall
    // back to a sound over-approximation.
    if(is_ambiguous_pointer(sym_id))
      return std::nullopt;
    auto it = pointer_targets.find(sym_id);
    if(it != pointer_targets.end())
      return it->second;
  }

  if(expr.id() == ID_member)
  {
    // A pointer-typed member used as an rvalue is the pointer value stored in
    // that field, not the address of the field's storage. Address-of(member)
    // is handled separately by the ID_address_of branch above.
    if(expr.type().id() == ID_pointer)
      return std::nullopt;
    const auto &member_expr = to_member_expr(expr);
    auto target = resolve_member_target(member_expr, resolve_member_target);
    if(target.has_value())
      return target;
  }

  if(expr.id() == ID_index)
  {
    const auto &ie = to_index_expr(expr);
    auto base_target = resolve_pointer_target(ie.array());
    if(base_target.has_value())
    {
      const typet base_element_type =
        follow_tag_type(base_target->element_type, ns);
      exprt actual_index = base_target->index;
      typet referent_type;

      if(same_follow_type(expr.type(), base_element_type, ns))
      {
        exprt offset = simplify_expr(
          typecast_exprt::conditional_cast(ie.index(), base_target->index.type()),
          ns);
        auto stride_value = numeric_cast<mp_integer>(base_target->element_stride);
        if(!(stride_value.has_value() && *stride_value == 1))
        {
          exprt stride_cast = simplify_expr(
            typecast_exprt::conditional_cast(
              base_target->element_stride, base_target->index.type()),
            ns);
          offset = mult_exprt(offset, stride_cast);
          offset.type() = base_target->index.type();
          offset = simplify_expr(offset, ns);
        }

        actual_index = plus_exprt(base_target->index, offset);
        actual_index.type() = base_target->index.type();
        actual_index = simplify_expr(actual_index, ns);
        referent_type = base_element_type;
      }
      else if(base_element_type.id() == ID_array)
      {
        std::vector<exprt> indices{ie.index()};
        auto view_opt = compute_array_view(base_element_type, indices, ns);
        if(!view_opt.has_value())
          return std::nullopt;

        exprt offset = simplify_expr(
          typecast_exprt::conditional_cast(
            view_opt->base_index, base_target->index.type()),
          ns);
        actual_index = plus_exprt(base_target->index, offset);
        actual_index.type() = base_target->index.type();
        actual_index = simplify_expr(actual_index, ns);
        referent_type = view_opt->referent_type;
      }
      else
      {
        return std::nullopt;
      }

      return make_target(
        base_target->array_id,
        actual_index,
        referent_type,
        referent_type,
        base_target->storage_type);
    }
  }

  if(expr.id() == ID_address_of)
  {
    const auto &obj = to_address_of_expr(expr).object();

    auto decomposed_opt = decompose_symbol_access(obj, ns);
    if(decomposed_opt.has_value())
    {
      const auto &decomposed = *decomposed_opt;
      typet logical_type = decomposed.root_type;
      const irep_idt storage_id =
        decomposed.member_path.empty()
          ? decomposed.root_id
          : append_member_path(decomposed.root_id, decomposed.member_path);

      if(!decomposed.member_path.empty())
      {
        auto projected_opt = project_member_type_through_arrays(
          decomposed.root_type, decomposed.member_path, ns);
        if(projected_opt.has_value())
          logical_type = *projected_opt;
      }

      const typet object_type = follow_tag_type(obj.type(), ns);
      if(logical_type.id() == ID_array)
      {
        auto view_opt = compute_array_view(logical_type, decomposed.indices, ns);
        if(view_opt.has_value())
        {
          const typet storage_type = flatten_array_type(logical_type, ns);
          // `&a[i]` still points into the same backing array object `a`, so
          // object_size/pointer_offset predicates must use the full array
          // object, not the single element type of `a[i]`.
          return make_target(
            storage_id,
            view_opt->base_index,
            view_opt->referent_type,
            logical_type,
            storage_type);
        }
      }
      else if(decomposed.indices.empty())
      {
        return make_target(
          storage_id,
          zero_pointer_index(),
          object_type,
          object_type,
          object_type);
      }
    }

    if(obj.id() == ID_string_constant)
    {
      const auto &sc = to_string_constant(obj);
      const typet object_type = follow_tag_type(sc.type(), ns);
      if(object_type.id() == ID_array)
      {
        const auto &arr = to_array_type(object_type);
        const irep_idt str_id = "__string_literal$" + id2string(sc.value());
        return make_target(
          str_id,
          from_integer(0, arr.index_type()),
          arr.element_type(),
          object_type,
          flatten_array_type(object_type, ns));
      }
    }

    if(obj.id() == ID_dereference)
      return resolve_pointer_target(to_dereference_expr(obj).pointer());

    if(obj.id() == ID_member)
    {
      auto target = resolve_member_target(to_member_expr(obj), resolve_member_target);
      if(target.has_value())
        return target;
    }

    if(obj.id() == ID_index)
    {
      const auto &ie = to_index_expr(obj);
      if(ie.array().id() == ID_string_constant)
      {
        const auto &sc = to_string_constant(ie.array());
        const typet object_type = follow_tag_type(sc.type(), ns);
        if(object_type.id() == ID_array)
        {
          const auto &arr = to_array_type(object_type);
          const irep_idt str_id = "__string_literal$" + id2string(sc.value());
          exprt base_index =
            simplify_expr(
              typecast_exprt::conditional_cast(ie.index(), arr.index_type()), ns);
          return make_target(
            str_id,
            base_index,
            arr.element_type(),
            object_type,
            flatten_array_type(object_type, ns));
        }
      }

      auto base_target = resolve_pointer_target(ie.array());
      if(base_target.has_value())
      {
        const typet access_type = follow_tag_type(base_target->element_type, ns);
        if(access_type.id() == ID_array)
        {
          std::vector<exprt> indices{ie.index()};
          auto view_opt = compute_array_view(access_type, indices, ns);
          if(view_opt.has_value())
          {
            exprt offset = simplify_expr(
              typecast_exprt::conditional_cast(
                view_opt->base_index, base_target->index.type()),
              ns);
            exprt actual_index = plus_exprt(base_target->index, offset);
            actual_index.type() = base_target->index.type();
            actual_index = simplify_expr(actual_index, ns);

            return make_target(
              base_target->array_id,
              actual_index,
              view_opt->referent_type,
              view_opt->referent_type,
              base_target->storage_type);
          }
        }
      }

      const auto &array = ie.array();
      if(array.id() == ID_symbol)
      {
        const irep_idt array_id = to_symbol_expr(array).get_identifier();
        const typet array_type = follow_tag_type(array.type(), ns);
        if(array_type.id() == ID_array)
        {
          const typet elem_type = to_array_type(array_type).element_type();
          return make_target(
            array_id,
            ie.index(),
            elem_type,
            elem_type,
            flatten_array_type(array_type, ns));
        }
      }
    }

    if(obj.id() == ID_symbol)
    {
      const auto &sym = to_symbol_expr(obj);
      const typet object_type = follow_tag_type(sym.type(), ns);
      if(object_type.id() == ID_array)
      {
        const auto &arr = to_array_type(object_type);
        exprt zero = from_integer(0, arr.index_type());
        return make_target(
          sym.get_identifier(),
          zero,
          arr.element_type(),
          object_type,
          flatten_array_type(object_type, ns));
      }

      if(
        is_supported_type(object_type) || object_type.id() == ID_struct ||
        object_type.id() == ID_code)
      {
        return make_target(
          sym.get_identifier(),
          zero_pointer_index(),
          object_type,
          object_type,
          object_type);
      }
    }
  }

  if(expr.id() == ID_plus)
  {
    if(expr.operands().size() < 2)
      return std::nullopt;

    std::optional<pointer_targett> base;
    std::size_t base_index = static_cast<std::size_t>(-1);
    for(std::size_t i = 0; i < expr.operands().size(); ++i)
    {
      auto cand = resolve_pointer_target(expr.operands()[i]);
      if(cand.has_value())
      {
        if(base.has_value())
          return std::nullopt;
        base = cand;
        base_index = i;
      }
    }

    if(!base.has_value())
      return std::nullopt;

    bool has_offset = false;
    exprt offset_sum;
    for(std::size_t i = 0; i < expr.operands().size(); ++i)
    {
      if(i == base_index)
        continue;
      exprt offset_cast =
        typecast_exprt::conditional_cast(expr.operands()[i], base->index.type());
      if(!has_offset)
      {
        offset_sum = offset_cast;
        has_offset = true;
      }
      else
      {
        offset_sum = plus_exprt(offset_sum, offset_cast);
        offset_sum.type() = base->index.type();
      }
    }

    exprt new_index = base->index;
    if(has_offset)
    {
      exprt scaled_offset = offset_sum;
      auto stride_value = numeric_cast<mp_integer>(base->element_stride);
      if(!(stride_value.has_value() && *stride_value == 1))
      {
        exprt stride_cast = simplify_expr(
          typecast_exprt::conditional_cast(base->element_stride, base->index.type()),
          ns);
        scaled_offset = mult_exprt(offset_sum, stride_cast);
        scaled_offset.type() = base->index.type();
        scaled_offset = simplify_expr(scaled_offset, ns);
      }

      new_index = plus_exprt(base->index, scaled_offset);
      new_index.type() = base->index.type();
    }

    return pointer_targett{
      base->array_id,
      new_index,
      base->element_type,
      base->storage_type,
      base->element_stride,
      base->object_size_bytes};
  }

  if(expr.id() == ID_minus)
  {
    if(expr.operands().size() < 2)
      return std::nullopt;

    auto base = resolve_pointer_target(expr.operands()[0]);
    if(!base.has_value())
      return std::nullopt;

    bool has_offset = false;
    exprt offset_sum;
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
    {
      exprt offset_cast =
        typecast_exprt::conditional_cast(expr.operands()[i], base->index.type());
      if(!has_offset)
      {
        offset_sum = offset_cast;
        has_offset = true;
      }
      else
      {
        offset_sum = plus_exprt(offset_sum, offset_cast);
        offset_sum.type() = base->index.type();
      }
    }

    exprt new_index = base->index;
    if(has_offset)
    {
      exprt scaled_offset = offset_sum;
      auto stride_value = numeric_cast<mp_integer>(base->element_stride);
      if(!(stride_value.has_value() && *stride_value == 1))
      {
        exprt stride_cast = simplify_expr(
          typecast_exprt::conditional_cast(base->element_stride, base->index.type()),
          ns);
        scaled_offset = mult_exprt(offset_sum, stride_cast);
        scaled_offset.type() = base->index.type();
        scaled_offset = simplify_expr(scaled_offset, ns);
      }

      new_index = minus_exprt(base->index, scaled_offset);
      new_index.type() = base->index.type();
    }

    return pointer_targett{
      base->array_id,
      new_index,
      base->element_type,
      base->storage_type,
      base->element_stride,
      base->object_size_bytes};
  }

  return std::nullopt;
}

std::optional<conditional_pointer_targett>
expr_to_btor2t::resolve_conditional_pointer_target(const exprt &expr) const
{
  auto apply_pointer_cast =
    [&](conditional_pointer_targett target, const typet &pointer_type) {
    if(
      pointer_type.id() == ID_pointer &&
      to_pointer_type(pointer_type).base_type().id() != ID_empty)
    {
      const typet base_type =
        follow_tag_type(to_pointer_type(pointer_type).base_type(), ns);
      for(auto &guarded_target : target.guarded_targets)
      {
        guarded_target.second.element_type = base_type;
        guarded_target.second.element_stride =
          flattened_element_count(base_type, ns);
      }
    }
    return target;
  };

  auto add_offset = [&](pointer_targett target, const exprt &offset) {
    exprt offset_cast =
      typecast_exprt::conditional_cast(offset, target.index.type());
    exprt scaled_offset = offset_cast;
    auto stride_value = numeric_cast<mp_integer>(target.element_stride);
    if(!(stride_value.has_value() && *stride_value == 1))
    {
      exprt stride_cast = simplify_expr(
        typecast_exprt::conditional_cast(
          target.element_stride, target.index.type()),
        ns);
      scaled_offset = mult_exprt(offset_cast, stride_cast);
      scaled_offset.type() = target.index.type();
      scaled_offset = simplify_expr(scaled_offset, ns);
    }

    exprt new_index = plus_exprt(target.index, scaled_offset);
    new_index.type() = target.index.type();
    target.index = simplify_expr(new_index, ns);
    return target;
  };

  auto subtract_offset = [&](pointer_targett target, const exprt &offset) {
    exprt offset_cast =
      typecast_exprt::conditional_cast(offset, target.index.type());
    exprt scaled_offset = offset_cast;
    auto stride_value = numeric_cast<mp_integer>(target.element_stride);
    if(!(stride_value.has_value() && *stride_value == 1))
    {
      exprt stride_cast = simplify_expr(
        typecast_exprt::conditional_cast(
          target.element_stride, target.index.type()),
        ns);
      scaled_offset = mult_exprt(offset_cast, stride_cast);
      scaled_offset.type() = target.index.type();
      scaled_offset = simplify_expr(scaled_offset, ns);
    }

    exprt new_index = minus_exprt(target.index, scaled_offset);
    new_index.type() = target.index.type();
    target.index = simplify_expr(new_index, ns);
    return target;
  };

  if(expr.id() == ID_typecast)
  {
    auto target = resolve_conditional_pointer_target(to_typecast_expr(expr).op());
    if(target.has_value())
      return apply_pointer_cast(*target, expr.type());
    return std::nullopt;
  }

  if(expr.id() == ID_symbol)
  {
    auto it =
      conditional_pointer_targets.find(to_symbol_expr(expr).get_identifier());
    if(it != conditional_pointer_targets.end())
      return it->second;
  }

  if(expr.id() == ID_if)
  {
    const auto &if_expr = to_if_expr(expr);
    conditional_pointer_targett result;

    auto append_branch =
      [&](const exprt &branch, const exprt &branch_guard) -> bool {
      auto normal_target = resolve_pointer_target(branch);
      if(normal_target.has_value())
      {
        result.guarded_targets.push_back({branch_guard, *normal_target});
        return true;
      }

      auto conditional_target = resolve_conditional_pointer_target(branch);
      if(!conditional_target.has_value())
        return false;

      for(const auto &guarded_target : conditional_target->guarded_targets)
      {
        result.guarded_targets.push_back(
          {and_exprt(branch_guard, guarded_target.first),
           guarded_target.second});
      }
      return true;
    };

    if(
      append_branch(if_expr.true_case(), if_expr.cond()) &&
      append_branch(if_expr.false_case(), not_exprt(if_expr.cond())) &&
      !result.guarded_targets.empty())
    {
      return result;
    }
  }

  if(expr.id() == ID_plus)
  {
    if(expr.operands().size() < 2)
      return std::nullopt;

    std::optional<conditional_pointer_targett> base;
    std::size_t base_index = static_cast<std::size_t>(-1);
    for(std::size_t i = 0; i < expr.operands().size(); ++i)
    {
      auto cand = resolve_conditional_pointer_target(expr.operands()[i]);
      if(cand.has_value())
      {
        if(base.has_value())
          return std::nullopt;
        base = cand;
        base_index = i;
      }
    }

    if(!base.has_value())
      return std::nullopt;

    bool has_offset = false;
    exprt offset_sum;
    for(std::size_t i = 0; i < expr.operands().size(); ++i)
    {
      if(i == base_index)
        continue;

      exprt offset_cast =
        typecast_exprt::conditional_cast(
          expr.operands()[i],
          base->guarded_targets.front().second.index.type());
      if(!has_offset)
      {
        offset_sum = offset_cast;
        has_offset = true;
      }
      else
      {
        offset_sum = plus_exprt(offset_sum, offset_cast);
        offset_sum.type() = base->guarded_targets.front().second.index.type();
      }
    }

    if(has_offset)
    {
      for(auto &guarded_target : base->guarded_targets)
        guarded_target.second = add_offset(guarded_target.second, offset_sum);
    }

    return base;
  }

  if(expr.id() == ID_minus)
  {
    if(expr.operands().size() < 2)
      return std::nullopt;

    auto base = resolve_conditional_pointer_target(expr.operands()[0]);
    if(!base.has_value())
      return std::nullopt;

    bool has_offset = false;
    exprt offset_sum;
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
    {
      exprt offset_cast =
        typecast_exprt::conditional_cast(
          expr.operands()[i],
          base->guarded_targets.front().second.index.type());
      if(!has_offset)
      {
        offset_sum = offset_cast;
        has_offset = true;
      }
      else
      {
        offset_sum = plus_exprt(offset_sum, offset_cast);
        offset_sum.type() = base->guarded_targets.front().second.index.type();
      }
    }

    if(has_offset)
    {
      for(auto &guarded_target : base->guarded_targets)
        guarded_target.second =
          subtract_offset(guarded_target.second, offset_sum);
    }

    return base;
  }

  return std::nullopt;
}

mp_integer expr_to_btor2t::get_object_id(const irep_idt &array_id)
{
  auto it = object_ids.find(array_id);
  if(it != object_ids.end())
    return it->second;

  if(addressable_objects_frozen)
  {
    conversion_had_errors = true;
    log.error() << "Addressable object discovered after tag table was frozen: "
                << array_id << messaget::eom;
    if(emit_warning_comments)
      builder.comment(
        "ERROR: late addressable object " + id2string(array_id));
    return 0;
  }

  mp_integer current = next_object_id;
  const mp_integer max_objects =
    mp_integer(1) << config.bv_encoding.object_bits;
  if(current >= max_objects)
  {
    conversion_had_errors = true;
    log.error() << "Pointer object tag capacity exceeded while registering "
                << array_id << messaget::eom;
    if(emit_warning_comments)
      builder.comment("ERROR: pointer object tag capacity exceeded");
    return 0;
  }
  object_ids[array_id] = current;
  next_object_id += 1;
  return current;
}

void expr_to_btor2t::register_addressable_object(
  const irep_idt &object_id,
  const typet &object_type,
  const exprt &object_size_bytes)
{
  const mp_integer id = get_object_id(object_id);
  if(id == 0)
    return;

  auto it = addressable_object_sizes.find(object_id);
  if(it == addressable_object_sizes.end() || it->second.is_nil())
    addressable_object_sizes[object_id] = object_size_bytes;
  addressable_object_types.emplace(object_id, follow_tag_type(object_type, ns));
}

void expr_to_btor2t::freeze_addressable_objects()
{
  addressable_objects_frozen = true;
}

btor2_nid_t expr_to_btor2t::encode_pointer_target(
  const pointer_targett &target,
  const typet &pointer_type)
{
  const auto width_opt = get_width(pointer_type);
  if(!width_opt.has_value() || config.bv_encoding.object_bits >= *width_opt)
    return 0;

  const std::size_t offset_bits =
    *width_opt - config.bv_encoding.object_bits;
  const mp_integer object = get_object_id(target.array_id);
  const mp_integer max_objects = mp_integer(1) << config.bv_encoding.object_bits;
  if(object >= max_objects)
    return 0;

  const btor2_nid_t pointer_sort = convert_type(pointer_type);
  if(pointer_sort == 0)
    return 0;

  const mp_integer object_base = object << offset_bits;
  btor2_nid_t base_nid = builder.constd(pointer_sort, object_base);

  auto size_opt = size_of_expr(target.element_type, ns);
  if(!size_opt.has_value())
    return 0;
  exprt element_size = typecast_exprt::conditional_cast(
    *size_opt, target.index.type());
  exprt byte_offset = mult_exprt(target.index, element_size);
  byte_offset.type() = target.index.type();
  byte_offset = simplify_expr(byte_offset, ns);
  const unsignedbv_typet offset_type(*width_opt);
  btor2_nid_t offset_nid = convert(
    typecast_exprt::conditional_cast(byte_offset, offset_type));
  if(offset_nid == 0)
    return 0;

  return builder.add(pointer_sort, base_nid, offset_nid);
}

btor2_nid_t expr_to_btor2t::pointer_matches_object(
  btor2_nid_t pointer_nid,
  const typet &pointer_type,
  const irep_idt &object_id)
{
  const auto width_opt = get_width(pointer_type);
  if(!width_opt.has_value() || config.bv_encoding.object_bits >= *width_opt)
    return 0;
  const std::size_t offset_bits =
    *width_opt - config.bv_encoding.object_bits;
  btor2_nid_t tag_sort =
    builder.get_or_create_bitvec_sort(config.bv_encoding.object_bits);
  btor2_nid_t tag = builder.slice(
    tag_sort, pointer_nid, *width_opt - 1, offset_bits);
  btor2_nid_t expected = builder.constd(tag_sort, get_object_id(object_id));
  return builder.eq(builder.get_bool_sort(), tag, expected);
}

btor2_nid_t expr_to_btor2t::pointer_access_guard(
  btor2_nid_t pointer_nid,
  const typet &pointer_type,
  const irep_idt &object_id,
  const typet &access_type)
{
  const auto width_opt = get_width(pointer_type);
  if(
    !width_opt.has_value() ||
    config.bv_encoding.object_bits >= *width_opt ||
    pointer_type.id() != ID_pointer)
    return 0;

  const typet pointer_base =
    follow_tag_type(to_pointer_type(pointer_type).base_type(), ns);
  const typet access = follow_tag_type(access_type, ns);
  if(pointer_base != access)
    return 0;

  auto object_type_it = addressable_object_types.find(object_id);
  if(object_type_it == addressable_object_types.end())
    return 0;
  typet contained_type = follow_tag_type(object_type_it->second, ns);
  const bool exact_type_compatible = contained_type == access;
  bool type_compatible = same_pointer_storage_type(contained_type, access, ns);
  while(!type_compatible && contained_type.id() == ID_array)
  {
    contained_type = follow_tag_type(
      to_array_type(contained_type).element_type(), ns);
    type_compatible = same_pointer_storage_type(contained_type, access, ns);
  }
  if(!type_compatible)
    return 0;

  auto size_opt = size_of_expr(access, ns);
  auto access_size = size_opt.has_value()
                       ? numeric_cast<mp_integer>(*size_opt)
                       : std::optional<mp_integer>{};
  auto object_size_it = addressable_object_sizes.find(object_id);
  const exprt *object_size_expr =
    object_size_it != addressable_object_sizes.end()
      ? &object_size_it->second
      : nullptr;
  auto object_size = object_size_expr != nullptr
                       ? numeric_cast<mp_integer>(*object_size_expr)
                       : std::optional<mp_integer>{};
  if(exact_type_compatible && object_size.has_value())
  {
    access_size = object_size;
  }
  if(!access_size.has_value() || *access_size <= 0)
  {
    conversion_had_errors = true;
    log.error() << "Cannot establish typed pointer access bounds for object "
                << object_id << messaget::eom;
    if(emit_warning_comments)
      builder.comment(
        "ERROR: missing pointer access bounds for " + id2string(object_id));
    return 0;
  }

  const std::size_t offset_bits =
    *width_opt - config.bv_encoding.object_bits;
  if(object_size.has_value())
  {
    if(*object_size < *access_size)
    {
      conversion_had_errors = true;
      log.error() << "Cannot establish typed pointer access bounds for object "
                  << object_id << messaget::eom;
      if(emit_warning_comments)
        builder.comment(
          "ERROR: missing pointer access bounds for " + id2string(object_id));
      return 0;
    }

    const mp_integer offset_capacity = mp_integer(1) << offset_bits;
    if(*object_size > offset_capacity)
    {
      conversion_had_errors = true;
      log.error() << "Pointer offset field is too small for object "
                  << object_id << " (size " << *object_size << " bytes)"
                  << messaget::eom;
      if(emit_warning_comments)
        builder.comment(
          "ERROR: pointer offset capacity exceeded for " +
          id2string(object_id));
      return 0;
    }
  }

  const btor2_nid_t pointer_sort = convert_type(pointer_type);
  const btor2_nid_t bool_sort = builder.get_bool_sort();
  if(pointer_sort == 0)
    return 0;

  const mp_integer object = get_object_id(object_id);
  if(object == 0)
    return 0;
  const mp_integer base = object << offset_bits;
  const btor2_nid_t bytes = builder.sub(
    pointer_sort, pointer_nid, builder.constd(pointer_sort, base));
  const btor2_nid_t tag_guard =
    pointer_matches_object(pointer_nid, pointer_type, object_id);
  if(tag_guard == 0)
    return 0;

  const btor2_nid_t access_size_nid =
    builder.constd(pointer_sort, *access_size);
  const btor2_nid_t aligned = builder.eq(
    bool_sort,
    builder.urem(pointer_sort, bytes, access_size_nid),
    builder.zero(pointer_sort));

  btor2_nid_t object_size_nid = 0;
  if(object_size.has_value())
    object_size_nid = builder.constd(pointer_sort, *object_size);
  else if(object_size_expr != nullptr && !object_size_expr->is_nil())
  {
    object_size_nid = convert(
      typecast_exprt::conditional_cast(*object_size_expr, pointer_type));
  }
  if(object_size_nid == 0)
  {
    conversion_had_errors = true;
    log.error() << "Cannot establish typed pointer access bounds for object "
                << object_id << messaget::eom;
    if(emit_warning_comments)
      builder.comment(
        "ERROR: missing pointer access bounds for " + id2string(object_id));
    return 0;
  }

  const btor2_nid_t has_access_size =
    builder.ugte(bool_sort, object_size_nid, access_size_nid);
  const btor2_nid_t max_offset =
    builder.sub(pointer_sort, object_size_nid, access_size_nid);
  const btor2_nid_t in_bounds =
    builder.land(bool_sort, has_access_size,
      builder.ulte(bool_sort, bytes, max_offset));
  return builder.land(
    bool_sort, tag_guard, builder.land(bool_sort, aligned, in_bounds));
}

btor2_nid_t expr_to_btor2t::pointer_element_index(
  btor2_nid_t pointer_nid,
  const typet &pointer_type,
  const irep_idt &object_id,
  const typet &element_type,
  const typet &index_type)
{
  const auto width_opt = get_width(pointer_type);
  const auto index_width_opt = get_width(index_type);
  if(
    !width_opt.has_value() || !index_width_opt.has_value() ||
    config.bv_encoding.object_bits >= *width_opt)
    return 0;
  const std::size_t offset_bits =
    *width_opt - config.bv_encoding.object_bits;
  const btor2_nid_t pointer_sort = convert_type(pointer_type);
  const btor2_nid_t index_sort = convert_type(index_type);
  if(pointer_sort == 0 || index_sort == 0)
    return 0;

  const mp_integer base = get_object_id(object_id) << offset_bits;
  btor2_nid_t bytes = builder.sub(
    pointer_sort, pointer_nid, builder.constd(pointer_sort, base));
  auto size_opt = size_of_expr(element_type, ns);
  auto size_value = size_opt.has_value()
                      ? numeric_cast<mp_integer>(*size_opt)
                      : std::optional<mp_integer>{};
  auto object_type_it = addressable_object_types.find(object_id);
  auto object_size_it = addressable_object_sizes.find(object_id);
  if(
    object_type_it != addressable_object_types.end() &&
    object_size_it != addressable_object_sizes.end() &&
    follow_tag_type(object_type_it->second, ns) ==
      follow_tag_type(element_type, ns))
  {
    auto object_size_value = numeric_cast<mp_integer>(object_size_it->second);
    if(object_size_value.has_value())
      size_value = object_size_value;
  }
  if(!size_value.has_value() || *size_value <= 0)
    return 0;
  bytes = builder.udiv(
    pointer_sort, bytes, builder.constd(pointer_sort, *size_value));
  if(*index_width_opt == *width_opt)
    return bytes;
  if(*index_width_opt < *width_opt)
    return builder.slice(index_sort, bytes, *index_width_opt - 1, 0);
  return builder.uext(index_sort, bytes, *index_width_opt - *width_opt);
}

btor2_nid_t expr_to_btor2t::convert_address_of(const address_of_exprt &expr)
{
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  auto target = resolve_pointer_target(expr);
  if(target.has_value())
    return encode_pointer_target(*target, expr.type());

  // Dynamic projection through a runtime struct pointer, for example
  // &p->nodes[p->used-1]. Structs are stored as projected field arrays, so
  // select the concrete root object by p's runtime tag and return a pointer
  // into that root's projected member array.
  const exprt *cur = &expr.object();
  std::vector<exprt> indices;
  while(cur->id() == ID_index)
  {
    const auto &index = to_index_expr(*cur);
    indices.push_back(index.index());
    cur = &index.array();
  }
  std::reverse(indices.begin(), indices.end());

  std::vector<irep_idt> member_path;
  while(cur->id() == ID_member)
  {
    const auto &member = to_member_expr(*cur);
    member_path.push_back(member.get_component_name());
    cur = &member.compound();
  }
  std::reverse(member_path.begin(), member_path.end());

  if(cur->id() == ID_dereference && !member_path.empty())
  {
    const exprt &runtime_pointer = to_dereference_expr(*cur).pointer();
    if(runtime_pointer.type().id() == ID_pointer)
    {
      const typet root_type = follow_tag_type(
        to_pointer_type(runtime_pointer.type()).base_type(), ns);
      auto member_type_opt = project_member_type(root_type, member_path, ns);
      auto view_opt = member_type_opt.has_value()
                        ? compute_array_view(*member_type_opt, indices, ns)
                        : std::optional<array_view_infot>{};
      btor2_nid_t pointer_nid = convert(runtime_pointer);
      if(view_opt.has_value() && pointer_nid != 0)
      {
        btor2_nid_t value = unsupported_pointer_input(
          sort,
          "__runtime_member_address_default$" +
            std::to_string(nondet_counter++));
        bool matched_any_object = false;
        const auto addressable_objects = get_addressable_objects();
        for(const auto &root_id : addressable_objects)
        {
          const symbolt *root_symbol = nullptr;
          if(ns.lookup(root_id, root_symbol) || root_symbol == nullptr)
            continue;
          if(!same_follow_type(root_symbol->type, root_type, ns))
            continue;

          const irep_idt projected_id =
            append_member_path(root_id, member_path);
          auto object_size_opt = size_of_expr(*member_type_opt, ns);
          pointer_targett projected_target{
            projected_id,
            view_opt->base_index,
            view_opt->referent_type,
            flatten_array_type(*member_type_opt, ns),
            flattened_element_count(view_opt->referent_type, ns),
            object_size_opt.has_value() ? *object_size_opt : nil_exprt()};
          btor2_nid_t projected_pointer =
            encode_pointer_target(projected_target, expr.type());
          btor2_nid_t root_guard = pointer_matches_object(
            pointer_nid, runtime_pointer.type(), root_id);
          if(projected_pointer == 0 || root_guard == 0)
            continue;
          value = builder.ite(sort, root_guard, projected_pointer, value);
          matched_any_object = true;
        }

        if(matched_any_object)
          return value;
      }
    }
  }

  return unsupported_pointer_input(
    sort,
    "__nondet_address_of$" + std::to_string(nondet_counter++));
}

btor2_nid_t expr_to_btor2t::convert_dereference(const dereference_exprt &expr)
{
  btor2_nid_t target_sort = convert_type(expr.type());
  if(target_sort == 0)
    return 0;

  const exprt *pointer_source = &expr.pointer();
  while(pointer_source->id() == ID_typecast)
    pointer_source = &to_typecast_expr(*pointer_source).op();
  const bool reads_stored_pointer = pointer_source->id() == ID_symbol;

  auto direct_target = reads_stored_pointer
                         ? std::optional<pointer_targett>{}
                         : resolve_pointer_target(address_of_exprt(expr));
  if(direct_target.has_value())
  {
    btor2_nid_t scalar_read =
      read_scalar_array(direct_target->array_id, direct_target->index, expr.type());
    if(scalar_read != 0)
      return scalar_read;
  }

  auto read_target = [&](const pointer_targett &target) -> btor2_nid_t {
    auto array_nid_opt = lookup_symbol(target.array_id);
    if(!array_nid_opt.has_value())
    {
      const std::string prefix = "__string_literal$";
      const std::string target_id = id2string(target.array_id);
      if(target_id.compare(0, prefix.size(), prefix) == 0)
      {
        const std::string value = target_id.substr(prefix.size());
        const string_constantt string_constant{irep_idt(value)};
        const array_exprt string_array = string_constant.to_array_expr();
        const auto &array_type = to_array_type(string_array.type());

        exprt index_expr = simplify_expr(
          typecast_exprt::conditional_cast(
            target.index, array_type.index_type()),
          ns);
        btor2_nid_t index_nid = convert(index_expr);
        btor2_nid_t index_sort = convert_type(array_type.index_type());
        if(index_nid == 0 || index_sort == 0)
          return 0;

        btor2_nid_t value_nid = unsupported_pointer_input(
          target_sort,
          "__string_literal_read_default$" +
            std::to_string(nondet_counter++));
        const btor2_nid_t bool_sort = builder.get_bool_sort();
        for(std::size_t i = string_array.operands().size(); i-- > 0;)
        {
          exprt char_expr = typecast_exprt::conditional_cast(
            string_array.operands()[i], expr.type());
          btor2_nid_t char_nid = convert(char_expr);
          if(char_nid == 0)
            return 0;

          btor2_nid_t idx_const =
            builder.constd(index_sort, mp_integer(i));
          btor2_nid_t is_match =
            builder.eq(bool_sort, index_nid, idx_const);
          value_nid =
            builder.ite(target_sort, is_match, char_nid, value_nid);
        }

        return value_nid;
      }
    }

    if(!array_nid_opt.has_value())
    {
      btor2_nid_t scalar_read =
        read_scalar_array(target.array_id, target.index, expr.type());
      if(scalar_read != 0)
        return scalar_read;
    }

    if(!array_nid_opt.has_value())
    {
      btor2_nid_t sort = convert_type(expr.type());
      if(sort != 0)
        return unsupported_pointer_input(
          sort,
          "__missing_target$" + std::to_string(unknown_symbol_counter++));

      log.warning() << "Symbol not found in BTOR2 conversion: "
                    << target.array_id << messaget::eom;
      return 0;
    }

    const symbolt *array_symbol = nullptr;
    auto storage_type_opt =
      target.storage_type.is_nil()
        ? lookup_symbol_type(target.array_id)
        : std::optional<typet>{target.storage_type};

    exprt simplified_target_index = simplify_expr(target.index, ns);
    bool synthetic_storage = false;
    auto elem_size_opt = size_of_expr(target.element_type, ns);
    const bool singleton_storage =
      !target.object_size_bytes.is_nil() && elem_size_opt.has_value() &&
      elem_size_opt->is_constant() && target.object_size_bytes.is_constant() &&
      *elem_size_opt == target.object_size_bytes;
    typet object_type_raw;
    if(ns.lookup(target.array_id, array_symbol) || array_symbol == nullptr)
    {
      synthetic_storage = true;
      if(storage_type_opt.has_value())
      {
        object_type_raw = *storage_type_opt;
      }
      else
      {
        bool scalar_like =
          is_zero_integer_expr(simplified_target_index) && singleton_storage;

        if(scalar_like)
        {
          object_type_raw = target.element_type;
        }
        else
        {
          array_typet reconstructed(target.element_type, nil_exprt());
          reconstructed.index_type_nonconst() = target.index.type();
          object_type_raw = reconstructed;
        }
      }
    }
    else
    {
      if(storage_type_opt.has_value())
      {
        object_type_raw = *storage_type_opt;
      }
      else
      {
        const typet symbol_type = follow_tag_type(array_symbol->type, ns);
        const typet flattened_type = flatten_array_type(symbol_type, ns);
        if(
          flattened_type.id() == ID_array &&
          same_follow_type(
            to_array_type(flattened_type).element_type(),
            target.element_type,
            ns))
        {
          object_type_raw = flattened_type;
        }
        else
        {
          object_type_raw = array_symbol->type;
        }
      }
    }

    auto physical_storage_type_opt = lookup_symbol_type(target.array_id);
    if(physical_storage_type_opt.has_value())
    {
      const typet physical_storage_type =
        follow_tag_type(*physical_storage_type_opt, ns);
      if(
        physical_storage_type.id() == ID_array &&
        object_type_raw.id() != ID_array)
      {
        const auto &physical_array_type = to_array_type(physical_storage_type);
        exprt physical_index = simplify_expr(
          typecast_exprt::conditional_cast(
            simplified_target_index, physical_array_type.index_type()),
          ns);
        btor2_nid_t index_nid = convert(physical_index);
        btor2_nid_t elem_sort =
          convert_type(physical_array_type.element_type());
        if(index_nid == 0 || elem_sort == 0)
          return 0;

        btor2_nid_t read_nid =
          builder.read(elem_sort, *array_nid_opt, index_nid);
        if(target_sort == elem_sort)
          return read_nid;

        symbol_exprt array_sym(target.array_id, physical_storage_type);
        index_exprt read_expr(
          array_sym, physical_index, physical_array_type.element_type());
        typecast_exprt cast_expr(read_expr, expr.type());
        return convert_typecast(cast_expr);
      }
    }

    if(object_type_raw.id() != ID_array)
    {
      btor2_nid_t object_sort = convert_type(object_type_raw);
      if(object_sort == 0)
        return 0;

      if(singleton_storage && object_sort == target_sort)
      {
        exprt index_expr = simplify_expr(
          typecast_exprt::conditional_cast(
            simplified_target_index, simplified_target_index.type()),
          ns);

        if(is_zero_integer_expr(index_expr))
          return *array_nid_opt;

        if(get_width(object_type_raw).has_value())
        {
          exprt zero_index = from_integer(0, index_expr.type());
          btor2_nid_t index_nid = convert(index_expr);
          btor2_nid_t zero_index_nid = convert(zero_index);
          if(index_nid == 0 || zero_index_nid == 0)
            return 0;

          btor2_nid_t is_zero =
            builder.eq(builder.get_bool_sort(), index_nid, zero_index_nid);
          btor2_nid_t default_nid = unsupported_pointer_input(
            object_sort,
            "__singleton_ptr_read_default$" +
              std::to_string(nondet_counter++));
          return builder.ite(object_sort, is_zero, *array_nid_opt, default_nid);
        }
      }

      if(!is_zero_integer_expr(simplified_target_index))
      {
        return 0;
      }

      if(object_sort == target_sort)
        return *array_nid_opt;

      symbol_exprt object_sym(target.array_id, object_type_raw);
      typecast_exprt cast_expr(object_sym, expr.type());
      return convert_typecast(cast_expr);
    }

    const auto &array_type = to_array_type(object_type_raw);

    exprt index_expr =
      simplify_expr(
        typecast_exprt::conditional_cast(
          simplified_target_index, array_type.index_type()),
        ns);
    btor2_nid_t index_nid = convert(index_expr);
    if(index_nid == 0)
      return 0;

    btor2_nid_t elem_sort = convert_type(array_type.element_type());
    if(elem_sort == 0)
      return 0;

    btor2_nid_t read_nid = 0;
    if(!storage_type_opt.has_value() && synthetic_storage && singleton_storage)
    {
      if(is_zero_integer_expr(index_expr))
      {
        read_nid = *array_nid_opt;
      }
      else if(get_width(array_type.element_type()).has_value())
      {
        exprt zero_index = from_integer(0, array_type.index_type());
        btor2_nid_t zero_index_nid = convert(zero_index);
        if(zero_index_nid == 0)
          return 0;

        btor2_nid_t is_zero =
          builder.eq(builder.get_bool_sort(), index_nid, zero_index_nid);
        btor2_nid_t default_nid = unsupported_pointer_input(
          elem_sort,
          "__singleton_array_read_default$" +
            std::to_string(nondet_counter++));
        read_nid = builder.ite(elem_sort, is_zero, *array_nid_opt, default_nid);
      }
      else
      {
        return 0;
      }
    }
    else
    {
      read_nid = builder.read(elem_sort, *array_nid_opt, index_nid);
    }

    if(target_sort == elem_sort)
      return read_nid;

    symbol_exprt array_sym(target.array_id, object_type_raw);
    index_exprt read_expr(array_sym, index_expr, array_type.element_type());
    typecast_exprt cast_expr(read_expr, expr.type());
    return convert_typecast(cast_expr);
  };

  auto target = reads_stored_pointer
                  ? std::optional<pointer_targett>{}
                  : resolve_pointer_target(expr.pointer());
  if(target.has_value())
  {
    btor2_nid_t result = read_target(*target);
    if(result != 0)
      return result;
  }

  auto conditional_target =
    reads_stored_pointer
      ? std::optional<conditional_pointer_targett>{}
      : resolve_conditional_pointer_target(expr.pointer());
  if(conditional_target.has_value())
  {
    btor2_nid_t value = unsupported_pointer_input(
      target_sort,
      "__conditional_ptr_read_default$" + std::to_string(nondet_counter++));
    bool any_failed = false;
    for(const auto &guarded_target : conditional_target->guarded_targets)
    {
      btor2_nid_t guard_nid = convert(guarded_target.first);
      btor2_nid_t target_nid = read_target(guarded_target.second);
      if(guard_nid == 0 || target_nid == 0)
      {
        any_failed = true;
        break;
      }
      value = builder.ite(target_sort, guard_nid, target_nid, value);
    }
    if(!any_failed)
      return value;
  }

  // Runtime pointer state cannot be resolved by the flow-insensitive target
  // map. Decode its object tag and byte offset, then dispatch to every
  // compatible addressable object. This is the normal path for *p and p[i]
  // when p is a function parameter or is updated in a loop.
  if(expr.pointer().type().id() == ID_pointer)
  {
    btor2_nid_t pointer_nid = convert(expr.pointer());
    if(pointer_nid != 0)
    {
      btor2_nid_t value = unsupported_pointer_input(
        target_sort,
        "__runtime_ptr_read_default$" + std::to_string(nondet_counter++));
      bool matched_any_object = false;
      const btor2_nid_t bool_sort = builder.get_bool_sort();

      for(const auto &object_entry : object_ids)
      {
        const irep_idt &object_id = object_entry.first;
        btor2_nid_t object_value = 0;

        auto scalar_array_it = scalar_array_map.find(object_id);
        if(scalar_array_it != scalar_array_map.end())
        {
          const auto &array_info = scalar_array_it->second;
          if(!same_pointer_storage_type(
               array_info.element_type, expr.type(), ns))
            continue;

          const typet storage_type = follow_tag_type(array_info.storage_type, ns);
          if(storage_type.id() != ID_array)
            continue;
          const auto &array_type = to_array_type(storage_type);
          btor2_nid_t index_nid = pointer_element_index(
            pointer_nid,
            expr.pointer().type(),
            object_id,
            array_info.element_type,
            array_type.index_type());
          btor2_nid_t index_sort = convert_type(array_type.index_type());
          if(index_nid == 0 || index_sort == 0)
            continue;

          object_value = unsupported_pointer_input(
            target_sort,
            "__runtime_ptr_array_read_default$" +
              std::to_string(nondet_counter++));
          for(std::size_t i = array_info.element_nids.size(); i-- > 0;)
          {
            btor2_nid_t is_index = builder.eq(
              bool_sort,
              index_nid,
              builder.constd(index_sort, mp_integer(i)));
            object_value = builder.ite(
              target_sort,
              is_index,
              array_info.element_nids[i],
              object_value);
          }
        }
        else
        {
          auto storage_type_opt = lookup_symbol_type(object_id);
          auto object_nid_opt = lookup_symbol(object_id);
          if(!storage_type_opt.has_value() || !object_nid_opt.has_value())
            continue;

          const typet storage_type = follow_tag_type(*storage_type_opt, ns);
          if(storage_type.id() == ID_array)
          {
            const auto &array_type = to_array_type(storage_type);
            if(!same_pointer_storage_type(
                 array_type.element_type(), expr.type(), ns))
              continue;
            btor2_nid_t index_nid = pointer_element_index(
              pointer_nid,
              expr.pointer().type(),
              object_id,
              array_type.element_type(),
              array_type.index_type());
            if(index_nid == 0)
              continue;
            object_value = builder.read(
              target_sort, *object_nid_opt, index_nid);
          }
          else
          {
            if(!same_pointer_storage_type(storage_type, expr.type(), ns))
              continue;
            btor2_nid_t valid_access = pointer_access_guard(
              pointer_nid,
              expr.pointer().type(),
              object_id,
              expr.type());
            if(valid_access == 0)
              continue;
            value = builder.ite(
              target_sort, valid_access, *object_nid_opt, value);
            matched_any_object = true;
            continue;
          }
        }

        if(object_value == 0)
          continue;
        btor2_nid_t valid_access = pointer_access_guard(
          pointer_nid,
          expr.pointer().type(),
          object_id,
          expr.type());
        if(valid_access == 0)
          continue;
        value = builder.ite(target_sort, valid_access, object_value, value);
        matched_any_object = true;
      }

      if(matched_any_object)
        return value;
    }
  }

  return unsupported_pointer_input(
    target_sort,
    "__nondet_deref$" + std::to_string(nondet_counter++));
}

btor2_nid_t expr_to_btor2t::convert_pointer_object(
  const pointer_object_exprt &expr)
{
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  const exprt &ptr = expr.op();
  if(ptr.is_constant() && to_constant_expr(ptr).is_null_pointer())
    return builder.zero(sort);

  auto target = resolve_pointer_target(ptr);
  if(target.has_value())
  {
    mp_integer obj_id = get_object_id(target->array_id);
    return builder.constd(sort, obj_id);
  }

  if(ptr.type().id() == ID_pointer)
  {
    const auto pointer_width_opt = get_width(ptr.type());
    const auto result_width_opt = get_width(expr.type());
    if(
      pointer_width_opt.has_value() && result_width_opt.has_value() &&
      config.bv_encoding.object_bits < *pointer_width_opt)
    {
      btor2_nid_t pointer_nid = convert(ptr);
      if(pointer_nid != 0)
      {
        const std::size_t offset_bits =
          *pointer_width_opt - config.bv_encoding.object_bits;
        btor2_nid_t tag_sort =
          builder.get_or_create_bitvec_sort(config.bv_encoding.object_bits);
        btor2_nid_t tag = builder.slice(
          tag_sort, pointer_nid, *pointer_width_opt - 1, offset_bits);
        if(*result_width_opt == config.bv_encoding.object_bits)
          return tag;
        if(*result_width_opt < config.bv_encoding.object_bits)
          return builder.slice(sort, tag, *result_width_opt - 1, 0);
        return builder.uext(
          sort, tag, *result_width_opt - config.bv_encoding.object_bits);
      }
    }
  }

  log.warning() << "Unsupported expression for BTOR2: pointer_object"
                << messaget::eom;
  if(emit_warning_comments)
    builder.comment("WARNING: Unsupported expression for BTOR2: pointer_object");
  return 0;
}

btor2_nid_t expr_to_btor2t::convert_pointer_offset(
  const pointer_offset_exprt &expr)
{
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  auto target = resolve_pointer_target(expr.op());
  if(!target.has_value())
  {
    const exprt &ptr = expr.op();
    if(ptr.type().id() != ID_pointer)
      return 0;
    const auto pointer_width_opt = get_width(ptr.type());
    const auto result_width_opt = get_width(expr.type());
    if(
      !pointer_width_opt.has_value() || !result_width_opt.has_value() ||
      config.bv_encoding.object_bits >= *pointer_width_opt)
    {
      return 0;
    }
    btor2_nid_t pointer_nid = convert(ptr);
    if(pointer_nid == 0)
      return 0;

    const std::size_t offset_bits =
      *pointer_width_opt - config.bv_encoding.object_bits;
    btor2_nid_t offset_sort =
      builder.get_or_create_bitvec_sort(offset_bits);
    btor2_nid_t offset =
      builder.slice(offset_sort, pointer_nid, offset_bits - 1, 0);
    if(*result_width_opt == offset_bits)
      return offset;
    if(*result_width_opt < offset_bits)
      return builder.slice(sort, offset, *result_width_opt - 1, 0);
    return builder.uext(sort, offset, *result_width_opt - offset_bits);
  }

  if(follow_tag_type(target->element_type, ns).id() == ID_code)
    return builder.zero(sort);

  auto elem_size_opt = size_of_expr(target->element_type, ns);
  if(!elem_size_opt.has_value() || !elem_size_opt->is_constant())
    return 0;

  mp_integer elem_size;
  if(to_integer(to_constant_expr(*elem_size_opt), elem_size))
    return 0;

  exprt elem_size_expr = from_integer(elem_size, expr.type());
  exprt index_cast = typecast_exprt::conditional_cast(target->index, expr.type());
  exprt offset_expr = mult_exprt(index_cast, elem_size_expr);
  offset_expr.type() = expr.type();

  return convert(offset_expr);
}

btor2_nid_t expr_to_btor2t::convert_object_size(const object_size_exprt &expr)
{
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  auto target = resolve_pointer_target(expr.op());
  if(!target.has_value())
  {
    const exprt &ptr = expr.op();
    if(ptr.type().id() != ID_pointer)
      return 0;
    btor2_nid_t pointer_nid = convert(ptr);
    if(pointer_nid == 0)
      return 0;

    btor2_nid_t result = builder.zero(sort);
    bool matched_any = false;
    for(const auto &object_id : get_addressable_objects())
    {
      exprt object_size = nil_exprt();
      auto size_it = addressable_object_sizes.find(object_id);
      if(size_it != addressable_object_sizes.end())
      {
        object_size = size_it->second;
      }
      else
      {
        const symbolt *symbol = nullptr;
        if(ns.lookup(object_id, symbol) || symbol == nullptr)
          continue;
        auto size_opt = size_of_expr(symbol->type, ns);
        if(!size_opt.has_value())
          continue;
        object_size = *size_opt;
      }

      btor2_nid_t object_size_nid =
        convert(typecast_exprt::conditional_cast(object_size, expr.type()));
      btor2_nid_t matches =
        pointer_matches_object(pointer_nid, ptr.type(), object_id);
      if(object_size_nid == 0 || matches == 0)
        continue;
      result = builder.ite(sort, matches, object_size_nid, result);
      matched_any = true;
    }
    if(matched_any)
      return result;
    return 0;
  }

  if(!target->object_size_bytes.is_nil())
  {
    exprt size_cast =
      typecast_exprt::conditional_cast(target->object_size_bytes, expr.type());
    return convert(size_cast);
  }

  const symbolt *symbol = nullptr;
  if(ns.lookup(target->array_id, symbol) || symbol == nullptr)
    return 0;

  auto size_opt = size_of_expr(symbol->type, ns);
  if(!size_opt.has_value())
    return 0;

  exprt size_cast = typecast_exprt::conditional_cast(*size_opt, expr.type());
  return convert(size_cast);
}

btor2_nid_t expr_to_btor2t::convert_is_invalid_pointer(
  const unary_exprt &expr)
{
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  const exprt &ptr = expr.op();
  if(ptr.is_constant() && to_constant_expr(ptr).is_null_pointer())
    return builder.zero(sort);

  auto target = resolve_pointer_target(expr.op());
  if(target.has_value())
    return builder.zero(sort);

  if(ptr.type().id() == ID_pointer)
  {
    const auto width_opt = get_width(ptr.type());
    if(
      width_opt.has_value() &&
      config.bv_encoding.object_bits < *width_opt)
    {
      btor2_nid_t pointer_nid = convert(ptr);
      btor2_nid_t pointer_sort = convert_type(ptr.type());
      if(pointer_nid != 0 && pointer_sort != 0)
      {
        const btor2_nid_t bool_sort = builder.get_bool_sort();
        btor2_nid_t valid =
          builder.eq(bool_sort, pointer_nid, builder.zero(pointer_sort));
        bool matched_any_object = false;

        for(const auto &object_id : get_addressable_objects())
        {
          btor2_nid_t matches =
            pointer_matches_object(pointer_nid, ptr.type(), object_id);
          if(matches == 0)
            continue;
          valid = builder.lor(bool_sort, valid, matches);
          matched_any_object = true;
        }

        if(matched_any_object)
          return builder.lnot(bool_sort, valid);
      }
    }
  }

  log.warning() << "Unsupported expression for BTOR2: is_invalid_pointer"
                << messaget::eom;
  if(emit_warning_comments)
    builder.comment(
      "WARNING: Unsupported expression for BTOR2: is_invalid_pointer");
  return 0;
}

btor2_nid_t expr_to_btor2t::convert_is_dynamic_object(
  const unary_exprt &expr)
{
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  const exprt &ptr = expr.op();
  if(ptr.is_constant() && to_constant_expr(ptr).is_null_pointer())
    return builder.zero(sort);

  auto target = resolve_pointer_target(ptr);
  if(target.has_value())
  {
    const std::string array_name = id2string(target->array_id);
    if(array_name.rfind("__heap_malloc$", 0) == 0)
      return builder.one(sort);
    return builder.zero(sort);
  }

  // Dynamic aliases (including free's argument) must query the runtime tag,
  // not a flow-insensitive guess of the pointed-to allocation site.
  if(ptr.type().id() == ID_pointer)
  {
    const auto pointer_nid = convert(ptr);
    if(pointer_nid != 0)
    {
      auto result = builder.zero(sort);
      for(const auto &object : get_addressable_objects())
      {
        if(id2string(object).rfind("__heap_malloc$", 0) != 0)
          continue;
        const auto matches = pointer_matches_object(pointer_nid, ptr.type(), object);
        if(matches == 0)
          return 0;
        result = builder.lor(sort, result, matches);
      }
      return result;
    }
  }

  log.warning() << "Unsupported expression for BTOR2: is_dynamic_object"
                << messaget::eom;
  if(emit_warning_comments)
    builder.comment(
      "WARNING: Unsupported expression for BTOR2: is_dynamic_object");
  return 0;
}

btor2_nid_t expr_to_btor2t::convert_prophecy_r_or_w_ok(
  const prophecy_r_or_w_ok_exprt &expr)
{
  btor2_nid_t sort = builder.get_bool_sort();

  const exprt &ptr = expr.pointer();
  if(ptr.is_constant() && to_constant_expr(ptr).is_null_pointer())
    return builder.zero(sort);

  auto target = resolve_pointer_target(ptr);
  if(!target.has_value())
  {
    log.warning() << "Unsupported expression for BTOR2: " << expr.id()
                  << messaget::eom;
    if(emit_warning_comments)
      builder.comment(
        "WARNING: Unsupported expression for BTOR2: " + id2string(expr.id()));
    return 0;
  }

  exprt lowered = expr.lower(ns);
  return convert(lowered);
}

btor2_nid_t expr_to_btor2t::convert_member(const exprt &expr)
{
  // __builtin_*_overflow returns a value/overflow pair. In particular,
  // calloc uses the multiplication pair to compute its allocation size.
  // This is a value expression, not an addressable struct object.
  const auto &member = to_member_expr(expr);
  const auto &compound = member.compound();
  irep_idt operation, overflow;
  if(compound.id() == ID_overflow_result_plus)
  {
    operation = ID_plus;
    overflow = ID_overflow_plus;
  }
  else if(compound.id() == ID_overflow_result_minus)
  {
    operation = ID_minus;
    overflow = ID_overflow_minus;
  }
  else if(compound.id() == ID_overflow_result_mult)
  {
    operation = ID_mult;
    overflow = ID_overflow_mult;
  }
  if(!operation.empty())
  {
    const auto &pair = to_overflow_result_expr(compound);
    if(member.get_component_name() == ID_value)
      return convert(binary_exprt(
        pair.op0(), operation, pair.op1(), pair.op0().type()));
    return convert(binary_overflow_exprt(pair.op0(), overflow, pair.op1()));
  }

  // We model structs by flattening them into per-field state variables in the
  // goto→BTOR2 frontend. A member expression `s.a` is translated to the symbol
  // `s.a` (with `.` as a separator), and arrays-of-struct are translated to
  // per-field arrays (e.g. `sa[i].a` becomes `read(sa.a, i)`).

  auto decomposed_opt = decompose_symbol_access(expr, ns);
  if(decomposed_opt.has_value())
  {
    const auto &decomposed = *decomposed_opt;
    auto member_type_opt = project_member_type_through_arrays(
      decomposed.root_type, decomposed.member_path, ns);
    if(!member_type_opt.has_value())
    {
      log.warning() << "Struct member access not fully supported in BTOR2"
                    << messaget::eom;
      return 0;
    }

    const irep_idt var_id =
      append_member_path(decomposed.root_id, decomposed.member_path);
    auto base_nid_opt = lookup_symbol(var_id);

    if(!base_nid_opt.has_value() && !decomposed.indices.empty())
    {
      auto flat_index_opt =
        linearize_array_indices(*member_type_opt, decomposed.indices, ns);
      if(flat_index_opt.has_value())
      {
        btor2_nid_t scalar_read =
          read_scalar_array(var_id, *flat_index_opt, expr.type());
        if(scalar_read != 0)
          return scalar_read;
      }
    }

    if(!base_nid_opt.has_value())
    {
      btor2_nid_t sort = convert_type(expr.type());
      if(sort != 0)
      {
        btor2_nid_t unknown = unsupported_pointer_input(
          sort,
          "__missing_member$" + std::to_string(unknown_symbol_counter++));
        register_symbol(var_id, unknown, expr.type());
        return unknown;
      }

      log.warning() << "Symbol not found in BTOR2 conversion: " << var_id
                    << messaget::eom;
      return 0;
    }

    if(decomposed.indices.empty())
      return *base_nid_opt;

    auto flat_index_opt =
      linearize_array_indices(*member_type_opt, decomposed.indices, ns);
    if(!flat_index_opt.has_value())
    {
      log.warning() << "Struct member access not fully supported in BTOR2"
                    << messaget::eom;
      return 0;
    }

    btor2_nid_t scalar_read =
      read_scalar_array(var_id, *flat_index_opt, expr.type());
    if(scalar_read != 0)
      return scalar_read;

    const typet storage_type = flatten_array_type(*member_type_opt, ns);
    if(storage_type.id() != ID_array)
      return 0;

    const auto &array_type = to_array_type(storage_type);
    exprt index_expr = simplify_expr(
      typecast_exprt::conditional_cast(*flat_index_opt, array_type.index_type()),
      ns);
    btor2_nid_t index_nid = convert(index_expr);
    btor2_nid_t target_sort = convert_type(expr.type());
    if(index_nid == 0 || target_sort == 0)
      return 0;

    return builder.read(target_sort, *base_nid_opt, index_nid);
  }

  std::vector<irep_idt> member_path;
  std::vector<exprt> indices;

  const exprt *cur = &expr;
  while(cur->id() == ID_member || cur->id() == ID_index)
  {
    if(cur->id() == ID_member)
    {
      const auto &m = to_member_expr(*cur);
      member_path.push_back(m.get_component_name());
      cur = &m.compound();
    }
    else
    {
      const auto &ie = to_index_expr(*cur);
      indices.push_back(ie.index());
      cur = &ie.array();
    }
  }

  if(cur->id() != ID_symbol)
  {
    address_of_exprt addr(expr);
    auto target = resolve_pointer_target(addr);
    if(target.has_value())
    {
      btor2_nid_t scalar_read =
        read_scalar_array(target->array_id, target->index, expr.type());
      if(scalar_read != 0)
        return scalar_read;

      auto base_nid_opt = lookup_symbol(target->array_id);
      if(!base_nid_opt.has_value())
      {
        btor2_nid_t sort = convert_type(expr.type());
        if(sort != 0)
          return unsupported_pointer_input(
            sort,
            "__missing_target$" + std::to_string(unknown_symbol_counter++));

        log.warning() << "Symbol not found in BTOR2 conversion: "
                      << target->array_id << messaget::eom;
        return 0;
      }

      if(!is_zero_integer_expr(target->index))
      {
        log.warning() << "Struct member access not fully supported in BTOR2"
                      << messaget::eom;
        return 0;
      }

      btor2_nid_t object_sort = convert_type(expr.type());
      auto storage_type_opt =
        target->storage_type.is_nil()
          ? lookup_symbol_type(target->array_id)
          : std::optional<typet>{target->storage_type};
      if(object_sort == 0)
        return 0;

      if(storage_type_opt.has_value())
      {
        btor2_nid_t storage_sort = convert_type(*storage_type_opt);
        if(storage_sort == object_sort)
          return *base_nid_opt;

        symbol_exprt object_sym(target->array_id, *storage_type_opt);
        typecast_exprt cast_expr(object_sym, expr.type());
        return convert_typecast(cast_expr);
      }

      return *base_nid_opt;
    }

    if(cur->id() == ID_dereference && !member_path.empty())
    {
      if(expr.type().id() == ID_array)
      {
        conversion_had_errors = true;
        log.error() << "Unsupported array-valued runtime member view"
                    << messaget::eom;
        return 0;
      }
      std::reverse(member_path.begin(), member_path.end());
      std::reverse(indices.begin(), indices.end());

      const exprt &pointer_expr = to_dereference_expr(*cur).pointer();
      btor2_nid_t pointer_nid = convert(pointer_expr);
      btor2_nid_t pointer_sort = convert_type(pointer_expr.type());
      btor2_nid_t target_sort = convert_type(expr.type());
      if(pointer_nid == 0 || pointer_sort == 0 || target_sort == 0)
        return 0;

      btor2_nid_t value = unsupported_pointer_input(
        target_sort,
        "__runtime_member_read_default$" + std::to_string(nondet_counter++));
      bool matched_any_object = false;

      for(const auto &object_entry : object_ids)
      {
        const irep_idt field_id =
          append_member_path(object_entry.first, member_path);
        auto field_type_opt = lookup_symbol_type(field_id);
        if(!field_type_opt.has_value())
          continue;

        btor2_nid_t field_value = 0;
        btor2_nid_t index_bounds_guard =
          builder.one(builder.get_bool_sort());
        btor2_nid_t field_sort = convert_type(*field_type_opt);
        const typet physical_field_type = follow_tag_type(*field_type_opt, ns);
        if(physical_field_type.id() == ID_array)
        {
          const auto &array_type = to_array_type(physical_field_type);
          const typet pointer_base = follow_tag_type(
            to_pointer_type(pointer_expr.type()).base_type(), ns);
          btor2_nid_t index_nid = pointer_element_index(
            pointer_nid,
            pointer_expr.type(),
            object_entry.first,
            pointer_base,
            array_type.index_type());
          if(index_nid != 0 && !indices.empty())
          {
            auto member_type = project_member_type_through_arrays(
              pointer_base, member_path, ns);
            auto local_index = member_type.has_value()
                                 ? linearize_array_indices(
                                     *member_type, indices, ns)
                                 : std::optional<exprt>{};
            const typet flattened_member = member_type.has_value()
                                            ? flatten_array_type(*member_type, ns)
                                            : typet{};
            if(
              local_index.has_value() &&
              flattened_member.id() == ID_array)
            {
              exprt local_cast = simplify_expr(
                typecast_exprt::conditional_cast(
                  *local_index, array_type.index_type()),
                ns);
              exprt span_cast = simplify_expr(
                typecast_exprt::conditional_cast(
                  to_array_type(flattened_member).size(),
                  array_type.index_type()),
                ns);
              btor2_nid_t local_nid = convert(local_cast);
              btor2_nid_t span_nid = convert(span_cast);
              btor2_nid_t index_sort =
                convert_type(array_type.index_type());
              if(local_nid == 0 || span_nid == 0 || index_sort == 0)
                index_nid = 0;
              else
              {
                index_bounds_guard = builder.ult(
                  builder.get_bool_sort(), local_nid, span_nid);
                index_nid = builder.add(
                  index_sort,
                  builder.mul(index_sort, index_nid, span_nid),
                  local_nid);
              }
            }
            else
              index_nid = 0;
          }
          if(index_nid != 0)
          {
            // Scalarized arrays have no aggregate state node. Reuse their
            // registered per-element read path with an expression equivalent
            // to the already decoded runtime index.
            btor2_nid_t field_array_nid = lookup_symbol(field_id).value_or(0);
            if(field_array_nid != 0)
              field_value = builder.read(
                target_sort, field_array_nid, index_nid);
            else
            {
              // Build the scalarized mux directly because read_scalar_array
              // accepts an exprt while the decoded index is already a nid.
              btor2_nid_t scalar_value = unsupported_pointer_input(
                target_sort,
                "__runtime_member_array_read_default$" +
                  std::to_string(nondet_counter++));
              const auto scalar_it = scalar_array_map.find(field_id);
              if(scalar_it != scalar_array_map.end())
              {
                btor2_nid_t index_sort = convert_type(array_type.index_type());
                for(std::size_t i = scalar_it->second.element_nids.size(); i-- > 0;)
                {
                  btor2_nid_t idx = builder.constd(index_sort, mp_integer(i));
                  btor2_nid_t match = builder.eq(
                    builder.get_bool_sort(), index_nid, idx);
                  scalar_value = builder.ite(
                    target_sort,
                    match,
                    scalar_it->second.element_nids[i],
                    scalar_value);
                }
                field_value = scalar_value;
              }
            }
          }
        }
        else if(field_sort == target_sort)
        {
          auto field_nid_opt = lookup_symbol(field_id);
          if(field_nid_opt.has_value())
            field_value = *field_nid_opt;
        }
        else
        {
          auto field_nid_opt = lookup_symbol(field_id);
          if(!field_nid_opt.has_value())
            continue;
          symbol_exprt field_sym(field_id, *field_type_opt);
          typecast_exprt cast_expr(field_sym, expr.type());
          field_value = convert_typecast(cast_expr);
        }

        if(field_value == 0)
          continue;

        const typet pointer_base = follow_tag_type(
          to_pointer_type(pointer_expr.type()).base_type(), ns);
        btor2_nid_t valid_access = pointer_access_guard(
          pointer_nid,
          pointer_expr.type(),
          object_entry.first,
          pointer_base);
        if(valid_access == 0)
          continue;
        valid_access = builder.land(
          builder.get_bool_sort(), valid_access, index_bounds_guard);
        value = builder.ite(target_sort, valid_access, field_value, value);
        matched_any_object = true;
      }

      if(matched_any_object)
        return value;
    }
  }

  return 0;
}
