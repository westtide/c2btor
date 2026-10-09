/*******************************************************************\

Module: 表达式到 BTOR2 的转换 - 实现

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// 表达式到 BTOR2 的转换实现
///
/// 本文件实现了 CBMC 表达式到 BTOR2 节点的转换逻辑。
/// 支持的 CBMC 表达式类型包括：
/// - 常量（整数、布尔）
/// - 符号引用
/// - 算术运算（+, -, *, /, %）
/// - 位运算（&, |, ^, ~, <<, >>）
/// - 比较运算（==, !=, <, <=, >, >=）
/// - 条件表达式（if-then-else）
/// - 数组操作（index, with）
/// - 溢出检查

#include "expr_to_btor2.h"
#include "memory_access.h"
#include "btor2_type_utils.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/ieee_float.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol.h>

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

//===========================================================================
// 构造函数
//===========================================================================

/// 构造函数：初始化表达式转换器
/// @param _builder BTOR2 构建器引用（用于创建 BTOR2 指令）
/// @param _ns 命名空间（用于类型解析）
/// @param _log 消息处理器（用于警告和错误）
expr_to_btor2t::expr_to_btor2t(
  btor2_buildert &_builder,
  const namespacet &_ns,
  messaget &_log,
  bool _emit_warning_comments)
  : builder(_builder),
    ns(_ns),
    log(_log),
    emit_warning_comments(_emit_warning_comments)
{
}

//===========================================================================
// 类型辅助方法
//===========================================================================

/// 获取类型的位宽
/// 支持的类型包括：
/// - bool: 1 位
/// - signedbv/unsignedbv: 指定位宽
/// - bv: 无符号位向量
/// - c_bool: C 布尔类型
/// - c_enum: C 枚举类型（使用底层类型的位宽）
/// - pointer: 指针类型
/// @param type 要查询的 CBMC 类型
/// @return 位宽，如果类型不支持返回 nullopt
std::optional<std::size_t> expr_to_btor2t::get_width(const typet &type) const
{
  // 布尔类型固定为 1 位
  if(type.id() == ID_bool)
    return 1;

  // 有符号位向量
  if(type.id() == ID_signedbv)
    return to_signedbv_type(type).get_width();

  // 无符号位向量
  if(type.id() == ID_unsignedbv)
    return to_unsignedbv_type(type).get_width();

  // 通用位向量
  if(type.id() == ID_bv)
    return to_bv_type(type).get_width();

  // IEEE floating-point values are represented as their packed bit-vector.
  if(type.id() == ID_floatbv)
    return to_floatbv_type(type).get_width();

  // C 布尔类型（通常是 1 位或 8 位，取决于平台）
  if(type.id() == ID_c_bool)
    return to_c_bool_type(type).get_width();

  // C bit-field type.
  if(type.id() == ID_c_bit_field)
    return to_c_bit_field_type(type).get_width();

  // C 枚举类型：使用其底层整数类型的位宽
  if(type.id() == ID_c_enum)
    return to_bitvector_type(to_c_enum_type(type).underlying_type()).get_width();

  // C 枚举标签：递归解析实际类型
  if(type.id() == ID_c_enum_tag)
    return get_width(ns.follow_tag(to_c_enum_tag_type(type)));

  // 指针类型
  if(type.id() == ID_pointer)
  {
    std::size_t width = to_pointer_type(type).get_width();
    if(width < 32)
      width = 32;
    return width;
  }

  if(type.id() == ID_union_tag)
    return get_width(ns.follow_tag(to_union_tag_type(type)));

  if(type.id() == ID_union)
  {
    // A union occupies enough bits for its largest member (including any
    // ABI-mandated padding).  Using the first member's width truncates unions
    // whose first member is narrower, corrupting both reads and writes.
    const auto object_bits = pointer_offset_bits(type, ns);
    if(object_bits.has_value() && *object_bits > 0)
      return numeric_castt<std::size_t>{}(*object_bits);
    return std::nullopt;
  }

  // 不支持的类型
  return std::nullopt;
}

/// 检查类型是否为有符号类型
/// @param type 要检查的类型
/// @return 如果是有符号类型返回 true
bool expr_to_btor2t::is_signed(const typet &type) const
{
  // 有符号位向量
  if(type.id() == ID_signedbv)
    return true;

  // 枚举类型：检查底层类型
  if(type.id() == ID_c_enum)
  {
    const auto &underlying = to_c_enum_type(type).underlying_type();
    return underlying.id() == ID_signedbv;
  }

  // 枚举标签：递归解析
  if(type.id() == ID_c_enum_tag)
    return is_signed(ns.follow_tag(to_c_enum_tag_type(type)));

  // 默认无符号
  return false;
}

/// 检查类型是否支持转换到 BTOR2
/// @param type 要检查的类型
/// @return 如果支持返回 true
bool expr_to_btor2t::is_supported_type(const typet &type) const
{
  const typet t = follow_tag_type(type, ns);

  // Scalar bitvector-like types.
  if(get_width(t).has_value())
    return true;

  // Arrays are supported if index/element types are supported recursively.
  if(t.id() == ID_array)
  {
    const auto &a = to_array_type(t);
    return is_supported_type(a.index_type()) && is_supported_type(a.element_type());
  }

  // Structs/unions are not directly supported (handled by higher-level flattening).
  return false;
}

/// 检查表达式是否支持转换到 BTOR2
/// @param expr 要检查的表达式
/// @return 如果支持返回 true
bool expr_to_btor2t::is_supported_expr(const exprt &expr) const
{
  // 检查表达式自身类型是否支持
  if(!is_supported_type(expr.type()))
    return false;

  // 检查所有子表达式类型是否支持
  for(const auto &op : expr.operands())
  {
    if(!is_supported_type(op.type()))
      return false;
  }

  return true;
}

//===========================================================================
// 类型转换
//===========================================================================

const typet &expr_to_btor2t::flatten_array_element(const array_typet &at)
{
  const typet &elem = at.element_type();
  if(elem.id() == ID_array)
    return flatten_array_element(to_array_type(elem));
  return elem;
}

std::size_t expr_to_btor2t::total_array_size(const array_typet &at)
{
  const typet &elem = at.element_type();
  auto size_opt = numeric_cast<mp_integer>(at.size());
  std::size_t n = size_opt.has_value()
                   ? numeric_cast_v<std::size_t>(*size_opt)
                   : 1;
  if(elem.id() != ID_array)
    return n;
  return n * total_array_size(to_array_type(elem));
}

std::size_t expr_to_btor2t::address_bits(std::size_t n)
{
  if(n <= 1)
    return 1;
  std::size_t bits = 0;
  while((1ULL << bits) < n)
    ++bits;
  return bits;
}

//===========================================================================

/// 将 CBMC 类型转换为 BTOR2 sort（类型）
///
/// BTOR2 支持的类型：
/// - bitvec N: N 位位向量
/// - array S1 S2: 索引类型为 S1，元素类型为 S2 的数组
///
/// @param type 要转换的 CBMC 类型
/// @return sort 的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_type(const typet &type)
{
  // 首先检查缓存，避免重复创建
  auto it = type_cache.find(type);
  if(it != type_cache.end())
    return it->second;

  btor2_nid_t result = 0;

  // 尝试获取位宽（标量类型）
  auto width_opt = get_width(type);
  if(width_opt.has_value())
  {
    // 创建位向量 sort
    result = builder.get_or_create_bitvec_sort(*width_opt);
  }
  else if(type.id() == ID_array)
  {
    // 处理数组类型：sort array <index_sort> <element_sort>
    // BTOR2 requires element sort to be bitvec, so flatten multi-dimensional
    // arrays: array(array(T, M), N) → array(T, N*M) with flattened index.
    const auto &array_type = to_array_type(type);
    const typet flattened_elem = flatten_array_element(array_type);
    btor2_nid_t elem_sort = convert_type(flattened_elem);
    if(elem_sort == 0)
      return 0;

    // Use the C-level index type bit-width (e.g. 32 for int, 64 for size_t)
    // so that read/write index sorts always match the array index sort.
    // Fall back to address_bits only when index_type has no discernible width.
    std::size_t total_elements = total_array_size(array_type);
    auto idx_width_opt = get_width(array_type.index_type());
    std::size_t index_width = idx_width_opt.has_value()
                                ? *idx_width_opt
                                : address_bits(total_elements);
    btor2_nid_t index_sort = builder.get_or_create_bitvec_sort(index_width);
    result = builder.sort_array(index_sort, elem_sort);
  }

  // 缓存结果
  if(result != 0)
    type_cache[type] = result;

  return result;
}

//===========================================================================
// 符号管理
//===========================================================================

/// 注册符号与其 BTOR2 节点 ID 的映射
/// 在创建状态变量后调用此方法，以便后续表达式转换可以引用该变量
/// @param id 符号标识符（变量名）
/// @param nid 对应的 BTOR2 节点 ID
void expr_to_btor2t::register_symbol(
  const irep_idt &id,
  btor2_nid_t nid,
  const typet &type)
{
  symbol_map[id] = nid;
  symbol_type_map[id] = type;
}

void expr_to_btor2t::register_scalar_array(
  const irep_idt &id,
  const typet &storage_type,
  const typet &element_type,
  const std::vector<btor2_nid_t> &element_nids)
{
  scalar_array_map[id] =
    scalar_array_infot{storage_type, element_type, element_nids};
  symbol_type_map[id] = storage_type;
}

void expr_to_btor2t::register_pointer_target(
  const irep_idt &ptr_id,
  const irep_idt &array_id,
  const exprt &index,
  const typet &element_type,
  const typet &storage_type)
{
  nil_exprt nil;
  register_pointer_target(
    ptr_id, array_id, index, element_type, storage_type, nil);
}

void expr_to_btor2t::register_pointer_target(
  const irep_idt &ptr_id,
  const irep_idt &array_id,
  const exprt &index,
  const typet &element_type,
  const typet &storage_type,
  const exprt &object_size_bytes)
{
  pointer_targets[ptr_id] = pointer_targett{
    array_id,
    index,
    element_type,
    storage_type,
    flattened_element_count(element_type, ns),
    object_size_bytes};
  conditional_pointer_targets.erase(ptr_id);
}

void expr_to_btor2t::clear_pointer_target(const irep_idt &ptr_id)
{
  pointer_targets.erase(ptr_id);
  conditional_pointer_targets.erase(ptr_id);
}

void expr_to_btor2t::add_known_pointer_target(
  const irep_idt &ptr_id,
  const irep_idt &array_id)
{
  auto &vec = known_pointer_targets[ptr_id];
  if(std::find(vec.begin(), vec.end(), array_id) == vec.end())
    vec.push_back(array_id);
}

bool expr_to_btor2t::is_ambiguous_pointer(const irep_idt &ptr_id) const
{
  auto it = known_pointer_targets.find(ptr_id);
  return it != known_pointer_targets.end() && it->second.size() > 1;
}

const std::vector<irep_idt> &
expr_to_btor2t::get_known_pointer_targets(const irep_idt &ptr_id) const
{
  static const std::vector<irep_idt> empty;
  auto it = known_pointer_targets.find(ptr_id);
  if(it != known_pointer_targets.end())
    return it->second;
  return empty;
}

std::vector<irep_idt> expr_to_btor2t::get_addressable_objects() const
{
  std::vector<irep_idt> result;
  result.reserve(object_ids.size());
  for(const auto &entry : object_ids)
    result.push_back(entry.first);
  return result;
}

void expr_to_btor2t::register_conditional_pointer_target(
  const irep_idt &ptr_id,
  const exprt &condition,
  const pointer_targett &true_target,
  const pointer_targett &false_target)
{
  conditional_pointer_targett target;
  target.guarded_targets.push_back({condition, true_target});
  target.guarded_targets.push_back({not_exprt(condition), false_target});
  register_conditional_pointer_target(ptr_id, target);
}

void expr_to_btor2t::register_conditional_pointer_target(
  const irep_idt &ptr_id,
  const conditional_pointer_targett &target)
{
  auto normalize_target = [&](pointer_targett target) {
    target.element_stride = flattened_element_count(target.element_type, ns);
    return target;
  };

  conditional_pointer_targett normalized;
  normalized.guarded_targets.reserve(target.guarded_targets.size());
  for(const auto &guarded_target : target.guarded_targets)
  {
    normalized.guarded_targets.push_back(
      {guarded_target.first, normalize_target(guarded_target.second)});
  }

  conditional_pointer_targets[ptr_id] = normalized;
  pointer_targets.erase(ptr_id);
}

/// 查找已注册的符号
/// @param id 符号标识符
/// @return 节点 ID，如果未找到返回 nullopt
std::optional<btor2_nid_t> expr_to_btor2t::lookup_symbol(const irep_idt &id) const
{
  auto it = symbol_map.find(id);
  if(it != symbol_map.end())
    return it->second;
  return std::nullopt;
}

std::optional<typet> expr_to_btor2t::lookup_symbol_type(const irep_idt &id) const
{
  auto it = symbol_type_map.find(id);
  if(it != symbol_type_map.end())
    return it->second;
  return std::nullopt;
}

/// 清除表达式缓存和类型缓存
/// 注意：符号映射不会被清除，因为它代表程序状态
void expr_to_btor2t::clear_caches()
{
  expr_cache.clear();
  type_cache.clear();
  // 注意：symbol_map 不清除，因为它代表程序的状态变量
}

//===========================================================================
// 主表达式转换入口
//===========================================================================

/// 将 CBMC 表达式转换为 BTOR2 节点
/// 
/// 这是主要的转换入口点，会根据表达式类型分派到具体的转换方法：
/// - 常量 → convert_constant
/// - 符号 → convert_symbol
/// - 类型转换 → convert_typecast
/// - 条件表达式 → convert_if
/// - 数组索引 → convert_index
/// - 数组更新 → convert_with
/// - 一元运算 → convert_unary
/// - 二元运算 → convert_binary
/// - 比较运算 → convert_comparison
/// - 溢出检查 → convert_overflow
/// 
/// @param expr 要转换的表达式
/// @return 转换结果的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert(const exprt &expr)
{
  if(memory)
  {
    auto result = memory->convert(expr);
    if(result.has_value())
      return *result;
  }
  // Nondet side effects must be treated as fresh inputs. Do not cache them:
  // structurally-equal nondet expressions can appear multiple times and must
  // remain independent.
  if(expr.id() == ID_side_effect)
  {
    const auto &se = to_side_effect_expr(expr);
    if(se.get_statement() == ID_nondet || se.get_statement() == ID_va_start)
      return convert_nondet(se);
    if(se.get_statement() == ID_allocate)
      return convert_allocate(se);
  }

  // 检查缓存，避免重复转换
  auto it = expr_cache.find(expr);
  if(!memory && it != expr_cache.end())
    return it->second;

  btor2_nid_t result = 0;

  if(expr.id() == "c2btor_sqrt" || expr.id() == "c2btor_fma" ||
     expr.id() == "c2btor_remainder" || expr.id() == "c2btor_fmod")
    return convert_float_math(expr);

  //--- 常量表达式 ---
  if(expr.id() == ID_constant)
  {
    result = convert_constant(to_constant_expr(expr));
  }
  //--- 符号表达式（变量引用）---
  else if(expr.id() == ID_symbol)
  {
    result = convert_symbol(to_symbol_expr(expr));
  }
  //--- 类型转换 ---
  else if(expr.id() == ID_typecast)
  {
    result = convert_typecast(to_typecast_expr(expr));
  }
  //--- semantic floating-point type conversion ---
  else if(expr.id() == ID_floatbv_typecast)
  {
    result = convert_floatbv_typecast(to_floatbv_typecast_expr(expr));
  }
  //--- semantic floating-point arithmetic ---
  else if(
    expr.id() == ID_floatbv_plus || expr.id() == ID_floatbv_minus ||
    expr.id() == ID_floatbv_mult || expr.id() == ID_floatbv_div ||
    expr.id() == ID_floatbv_rem)
  {
    result = convert_floatbv_op(to_ieee_float_op_expr(expr));
  }
  //--- semantic floating-point equality ---
  else if(
    expr.id() == ID_ieee_float_equal ||
    expr.id() == ID_ieee_float_notequal)
  {
    result = convert_floatbv_relation(to_binary_relation_expr(expr));
  }
  //--- semantic floating-point predicates ---
  else if(
    expr.id() == ID_isnan || expr.id() == ID_isinf ||
    expr.id() == ID_isfinite || expr.id() == ID_isnormal)
  {
    result = convert_floatbv_predicate(to_unary_expr(expr));
  }
  //--- 条件表达式 (if-then-else) ---
  else if(expr.id() == ID_if)
  {
    result = convert_if(to_if_expr(expr));
  }
  //--- 数组索引 (array[index]) ---
  else if(expr.id() == ID_index)
  {
    result = convert_index(to_index_expr(expr));
  }
  //--- address_of ---
  else if(expr.id() == ID_address_of)
  {
    result = convert_address_of(to_address_of_expr(expr));
  }
  //--- dereference ---
  else if(expr.id() == ID_dereference)
  {
    result = convert_dereference(to_dereference_expr(expr));
  }
  //--- pointer predicates ---
  else if(expr.id() == ID_pointer_object)
  {
    result = convert_pointer_object(to_pointer_object_expr(expr));
  }
  else if(expr.id() == ID_pointer_offset)
  {
    result = convert_pointer_offset(to_pointer_offset_expr(expr));
  }
  else if(expr.id() == ID_object_size)
  {
    result = convert_object_size(to_object_size_expr(expr));
  }
  else if(expr.id() == ID_is_invalid_pointer)
  {
    result = convert_is_invalid_pointer(to_unary_expr(expr));
  }
  else if(expr.id() == ID_is_dynamic_object)
  {
    result = convert_is_dynamic_object(to_unary_expr(expr));
  }
  else if(
    expr.id() == ID_prophecy_r_ok || expr.id() == ID_prophecy_w_ok ||
    expr.id() == ID_prophecy_rw_ok)
  {
    result = convert_prophecy_r_or_w_ok(to_prophecy_r_or_w_ok_expr(expr));
  }
  //--- 数组字面量 ({ ... }) ---
  else if(expr.id() == ID_array)
  {
    result = convert_array(to_array_expr(expr));
  }
  //--- array_of(x) ---
  else if(expr.id() == ID_array_of)
  {
    result = convert_array_of(to_array_of_expr(expr));
  }
  //--- 数组更新 (array with [index := value]) ---
  else if(expr.id() == ID_with)
  {
    result = convert_with(to_with_expr(expr));
  }
  //--- 结构体成员访问 ---
  else if(expr.id() == ID_member)
  {
    result = convert_member(to_member_expr(expr));
  }
  //--- 位提取 ---
  else if(expr.id() == ID_extractbits)
  {
    result = convert_extractbits(to_extractbits_expr(expr));
  }
  //--- 位拼接 ---
  else if(expr.id() == ID_concatenation)
  {
    result = convert_concatenation(to_concatenation_expr(expr));
  }
  //--- 一元运算符 ---
  // not: 逻辑非
  // bitnot: 按位取反
  // unary_minus: 算术取反 (-x)
  // unary_plus: 正号 (+x)
  else if(
    expr.id() == ID_not || expr.id() == ID_bitnot ||
    expr.id() == ID_unary_minus || expr.id() == ID_unary_plus ||
    expr.id() == ID_abs)
  {
    result = convert_unary(to_unary_expr(expr));
  }
  //--- 比较运算符 ---
  // equal: ==
  // notequal: !=
  // lt: <
  // le: <=
  // gt: >
  // ge: >=
  else if(
    expr.id() == ID_equal || expr.id() == ID_notequal || expr.id() == ID_lt ||
    expr.id() == ID_le || expr.id() == ID_gt || expr.id() == ID_ge)
  {
    result = convert_comparison(to_binary_relation_expr(expr));
  }
  //--- 二元运算符 ---
  // 算术: plus, minus, mult, div, mod
  // 位运算: bitand, bitor, bitxor, shl, ashr, lshr
  // 逻辑: and, or, xor, implies
  else if(
    expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
    expr.id() == ID_div || expr.id() == ID_mod || expr.id() == ID_bitand ||
    expr.id() == ID_bitor || expr.id() == ID_bitxor || expr.id() == ID_shl ||
    expr.id() == ID_ashr || expr.id() == ID_lshr || expr.id() == ID_and ||
    expr.id() == ID_or || expr.id() == ID_xor || expr.id() == ID_implies)
  {
    result = convert_binary(expr);
  }
  //--- 溢出检查表达式 ---
  // overflow_plus: 加法溢出
  // overflow_minus: 减法溢出
  // overflow_mult: 乘法溢出
  else if(
    expr.id() == ID_overflow_plus || expr.id() == ID_overflow_minus ||
    expr.id() == ID_overflow_mult)
  {
    result = convert_overflow(to_binary_overflow_expr(expr));
  }
  else if(
    expr.id() == ID_byte_extract_little_endian ||
    expr.id() == ID_byte_extract_big_endian)
  {
    result = convert_byte_extract(expr);
  }
  else if(expr.id() == ID_bswap)
  {
    result = convert_bswap(to_bswap_expr(expr));
  }
  else if(expr.id() == ID_string_constant)
  {
    auto target = resolve_pointer_target(address_of_exprt(expr));
    if(target.has_value())
    {
      btor2_nid_t sort = convert_type(expr.type());
      if(sort == 0)
        return 0;
      mp_integer obj_id = get_object_id(target->array_id);
      return builder.constd(sort, obj_id);
    }
    result = 0;
  }
  else
  {
    conversion_had_errors = true;
    log.warning() << "Unsupported expression for BTOR2: " << expr.id();
    if(expr.id() == ID_side_effect)
      log.warning() << " statement="
                    << to_side_effect_expr(expr).get_statement();
    log.warning() << messaget::eom;
    if(emit_warning_comments)
      builder.comment(
        "WARNING: Unsupported expression for BTOR2: " + id2string(expr.id()));
  }

  // 缓存结果
  if(result != 0 && !memory)
    expr_cache[expr] = result;
  if(result == 0)
    conversion_had_errors = true;

  return result;
}

btor2_nid_t expr_to_btor2t::convert_nondet(const side_effect_exprt &expr)
{
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
  {
    log.warning() << "Unsupported nondet type in BTOR2 conversion"
                  << messaget::eom;
    return 0;
  }

  const std::string name = "nondet_" + std::to_string(nondet_counter++);
  return builder.input(sort, name);
}

btor2_nid_t expr_to_btor2t::unsupported_pointer_input(
  btor2_nid_t sort, const std::string &name)
{
  conversion_had_errors = true;
  log.error() << "Unsupported pointer/aggregate fallback: " << name << messaget::eom;
  return builder.input(sort, name);
}

btor2_nid_t expr_to_btor2t::convert_allocate(const side_effect_exprt &expr)
{
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
  {
    log.warning() << "Unsupported allocate type in BTOR2 conversion"
                  << messaget::eom;
    return 0;
  }

  ++allocate_counter;
  log.warning() << "allocate expression is only supported in assignment context"
                << messaget::eom;
  if(emit_warning_comments)
    builder.comment(
      "WARNING: allocate expression is only supported in assignment context");
  return 0;
}

//===========================================================================
// 常量表达式转换
//===========================================================================

/// 转换常量表达式
/// 
/// 处理两种常量：
/// 1. 布尔常量: true → one(1), false → zero(1)
/// 2. 整数常量: 转换为 BTOR2 十进制常量
/// 
/// BTOR2 格式:
///   <nid> constd <sort> <decimal_value>
/// 
/// @param expr 常量表达式
/// @return 常量的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_constant(const constant_exprt &expr)
{
  // 首先获取类型的 sort
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  if(expr.is_null_pointer())
    return builder.zero(sort);

  // 处理布尔常量
  if(expr.type().id() == ID_bool)
  {
    if(expr.is_true())
      return builder.one(sort);   // true → 1
    else
      return builder.zero(sort);  // false → 0
  }

  // Represent float constants as packed IEEE bit patterns. BTOR2 has no native
  // floating-point sort, but the downstream bit-blasted operations use exactly
  // this packed bit-vector representation.
  if(expr.type().id() == ID_floatbv)
    return builder.constd(sort, ieee_float_valuet(expr).pack());

  // 处理整数常量
  mp_integer value;
  if(to_integer(expr, value))
  {
    log.warning() << "Failed to convert constant to integer" << messaget::eom;
    return 0;
  }

  // 创建十进制常量指令
  return builder.constd(sort, value);
}

//===========================================================================
// 符号表达式转换
//===========================================================================

/// 转换符号表达式（变量引用）
/// 
/// 从符号映射中查找变量对应的 BTOR2 节点 ID。
/// 符号必须在之前通过 register_symbol() 注册过。
/// 
/// @param expr 符号表达式
/// @return 符号的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_symbol(const symbol_exprt &expr)
{
  auto nid_opt = lookup_symbol(expr.get_identifier());
  if(nid_opt.has_value())
  {
    auto storage_type_opt = lookup_symbol_type(expr.get_identifier());
    if(!storage_type_opt.has_value())
      return *nid_opt;

    const typet storage_type = follow_tag_type(*storage_type_opt, ns);
    const typet expr_type = follow_tag_type(expr.type(), ns);
    if(storage_type == expr_type)
      return *nid_opt;

    if(storage_type.id() == ID_array && get_width(expr_type).has_value())
    {
      const auto &array_type = to_array_type(storage_type);
      const typet element_type = follow_tag_type(array_type.element_type(), ns);
      if(get_width(element_type).has_value())
      {
        btor2_nid_t index_sort = convert_type(array_type.index_type());
        btor2_nid_t elem_sort = convert_type(element_type);
        if(index_sort == 0 || elem_sort == 0)
          return 0;

        btor2_nid_t zero_index = builder.constd(index_sort, 0);
        return builder.read(elem_sort, *nid_opt, zero_index);
      }
    }

    return *nid_opt;
  }

  const symbolt *symbol = nullptr;
  if(!ns.lookup(expr.get_identifier(), symbol) && symbol)
  {
    if(symbol->value.is_not_nil())
    {
      if(!has_symbol_expr(symbol->value, expr.get_identifier(), true))
      {
        btor2_nid_t value_nid = convert(symbol->value);
        if(value_nid != 0)
        {
          register_symbol(expr.get_identifier(), value_nid, expr.type());
          return value_nid;
        }
      }
    }
  }

  if(is_supported_type(expr.type()))
  {
    btor2_nid_t sort = convert_type(expr.type());
    if(sort != 0)
    {
      conversion_had_errors = true;
      log.error() << "BTOR2 symbol was not collected; introduced diagnostic "
                     "fallback input for "
                  << expr.get_identifier() << messaget::eom;
      if(emit_warning_comments)
        builder.comment(
          "ERROR: missing BTOR2 symbol " + id2string(expr.get_identifier()));
      btor2_nid_t unknown = builder.input(
        sort,
        "__missing_symbol$" + std::to_string(unknown_symbol_counter++));
      register_symbol(expr.get_identifier(), unknown, expr.type());
      return unknown;
    }
  }

  // 符号未找到 - 这是转换上下文中的错误
  log.warning() << "Symbol not found in BTOR2 conversion: "
                << expr.get_identifier() << messaget::eom;
  return 0;
}
