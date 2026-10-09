/*******************************************************************\

Module: 表达式到 BTOR2 的转换

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// 表达式到 BTOR2 的转换
///
/// 本文件定义了 expr_to_btor2t 类，负责将 CBMC 的表达式（exprt）转换为 BTOR2 节点。
/// 这个类处理了从 CBMC 内部表示到 BTOR2 格式的类型和操作符翻译。
///
/// 支持的表达式类型：
/// - 常量表达式（整数、布尔值）
/// - 符号表达式（变量引用）
/// - 类型转换（扩展、截断）
/// - 算术运算（加、减、乘、除、取模）
/// - 位运算（与、或、异或、移位）
/// - 比较运算（等于、小于、大于等）
/// - 条件表达式（三目运算符）
/// - 数组操作（读取、写入）
/// - 溢出检查

#ifndef CPROVER_GOTO_BTOR2_EXPR_TO_BTOR2_H
#define CPROVER_GOTO_BTOR2_EXPR_TO_BTOR2_H

#include "btor2_builder.h"
#include "btor2_type_utils.h"
#include "expr_to_btor2_types.h"

#include <util/bitvector_expr.h>
#include <util/expr.h>
#include <util/floatbv_expr.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <map>
#include <optional>
#include <cstddef>
#include <vector>
#include <util/mp_arith.h>

/// 将 CBMC 表达式 (exprt) 转换为 BTOR2 节点 ID 的转换器类
///
/// 使用示例：
/// ```cpp
/// btor2_buildert builder;
/// expr_to_btor2t converter(builder, ns, log);
///
/// // 注册变量
/// auto x_sort = builder.get_or_create_bitvec_sort(32);
/// auto x_state = builder.state(x_sort, "x");
/// converter.register_symbol("x", x_state);
///
/// // 转换表达式
/// exprt expr = ...; // 例如 x + 1
/// btor2_nid_t result = converter.convert(expr);
/// ```
class memory_accesst;
class expr_to_btor2t
{
public:
  using scalar_array_infot = ::scalar_array_infot;
  using pointer_targett = ::pointer_targett;
  using conditional_pointer_targett = ::conditional_pointer_targett;

  /// 构造函数
  /// @param _builder BTOR2 构建器引用
  /// @param _ns 命名空间（用于类型解析）
  /// @param _log 消息处理器（用于警告和错误）
  /// @param _emit_warning_comments Whether to also write warnings as BTOR2 comments
  expr_to_btor2t(
    btor2_buildert &_builder,
    const namespacet &_ns,
    messaget &_log,
    bool _emit_warning_comments = false);

  //=========================================================================
  // 类型转换
  //=========================================================================

  /// 将 CBMC 类型转换为 BTOR2 sort
  /// @param type 要转换的 CBMC 类型
  /// @return sort 的节点 ID，失败返回 0
  btor2_nid_t convert_type(const typet &type);

  //=========================================================================
  // 表达式转换
  //=========================================================================

  /// 将 CBMC 表达式转换为 BTOR2
  /// 这是主要的转换入口点，会根据表达式类型分派到具体的转换方法
  /// @param expr 要转换的表达式
  /// @return 转换结果的节点 ID，失败返回 0
  btor2_nid_t convert(const exprt &expr);
  void set_memory(memory_accesst *value) { memory = value; }

  //=========================================================================
  // 类型支持检查
  //=========================================================================

  /// 检查类型是否支持转换
  /// @param type 要检查的类型
  /// @return 如果支持转换返回 true
  bool is_supported_type(const typet &type) const;

  /// 检查表达式是否支持转换
  /// @param expr 要检查的表达式
  /// @return 如果支持转换返回 true
  bool is_supported_expr(const exprt &expr) const;

  /// Whether expression conversion introduced an unsupported fallback.
  bool has_conversion_errors() const
  {
    return conversion_had_errors;
  }

  /// 获取类型的位宽
  /// @param type 要查询的类型
  /// @return 位宽，如果类型不支持返回 nullopt
  std::optional<std::size_t> get_width(const typet &type) const;

  /// Flatten a potentially nested array type to its leaf element type.
  /// array(array(T, M), N) → T
  static const typet &flatten_array_element(const array_typet &at);

  /// Compute total element count of a (possibly nested) array.
  /// array(array(T, M), N) → N * M
  static std::size_t total_array_size(const array_typet &at);

  /// Minimum bit width to address `n` elements.
  static std::size_t address_bits(std::size_t n);

  //=========================================================================
  // 符号管理
  //=========================================================================

  /// 注册符号与其 BTOR2 节点 ID 的映射
  /// 在创建状态变量后调用此方法，以便后续表达式转换可以引用该变量
  /// @param id 符号标识符
  /// @param nid BTOR2 节点 ID
  /// @param type The BTOR2 storage type used for this symbol
  void register_symbol(const irep_idt &id, btor2_nid_t nid, const typet &type);

  /// Register a fixed-size array that has been scalarized into per-element
  /// state variables. This avoids emitting BTOR2 array sorts for small static
  /// arrays, which some downstream solvers handle poorly.
  void register_scalar_array(
    const irep_idt &id,
    const typet &storage_type,
    const typet &element_type,
    const std::vector<btor2_nid_t> &element_nids);

  /// Register a pointer target for a pointer-typed symbol.
  /// @param ptr_id Pointer symbol identifier
  /// @param array_id Array symbol identifier the pointer points into
  /// @param index Base index expression (in elements)
  /// @param element_type Array element type
  void register_pointer_target(
    const irep_idt &ptr_id,
    const irep_idt &array_id,
    const exprt &index,
    const typet &element_type,
    const typet &storage_type);

  /// Register a pointer target with an explicit object size in bytes.
  /// This is useful for modelling heap objects (e.g. from malloc) that don't
  /// correspond to a static symbol in the symbol table.
  void register_pointer_target(
    const irep_idt &ptr_id,
    const irep_idt &array_id,
    const exprt &index,
    const typet &element_type,
    const typet &storage_type,
    const exprt &object_size_bytes);

  /// Clear a previously registered pointer target mapping.
  void clear_pointer_target(const irep_idt &ptr_id);

  /// Record that pointer \p ptr_id can target backing array \p array_id.
  /// Called during the pre-collection pass to detect pointers that are
  /// assigned to more than one distinct backing object across the program.
  /// Such pointers are "ambiguous" and cannot be resolved to a single
  /// target; reads/writes through them must be over-approximated.
  void add_known_pointer_target(const irep_idt &ptr_id, const irep_idt &array_id);

  /// Check whether pointer \p ptr_id has been observed to target more than
  /// one distinct backing array.  If so, resolve_pointer_target returns
  /// nullopt for it and callers must use a sound fallback.
  bool is_ambiguous_pointer(const irep_idt &ptr_id) const;

  /// Return all distinct backing array IDs that \p ptr_id can target.
  const std::vector<irep_idt> &
  get_known_pointer_targets(const irep_idt &ptr_id) const;

  /// Return every object that has received a stable runtime object tag.
  std::vector<irep_idt> get_addressable_objects() const;

  /// Pre-register an addressable root object before instruction lowering.
  /// Once frozen, discovering another object is a conversion error: runtime
  /// pointer dispatch must not depend on instruction traversal order.
  void register_addressable_object(
    const irep_idt &object_id,
    const typet &object_type,
    const exprt &object_size_bytes);
  void freeze_addressable_objects();

  /// Encode a pointer using CBMC's standard layout: object tag in the high
  /// bits and a signed byte offset in the remaining low bits.
  btor2_nid_t encode_pointer_target(
    const pointer_targett &target,
    const typet &pointer_type);

  /// Runtime helpers used by dynamic loads/stores.
  btor2_nid_t pointer_matches_object(
    btor2_nid_t pointer_nid,
    const typet &pointer_type,
    const irep_idt &object_id);
  /// Guard a typed access with tag, alignment and in-bounds checks.
  btor2_nid_t pointer_access_guard(
    btor2_nid_t pointer_nid,
    const typet &pointer_type,
    const irep_idt &object_id,
    const typet &access_type);
  btor2_nid_t pointer_element_index(
    btor2_nid_t pointer_nid,
    const typet &pointer_type,
    const irep_idt &object_id,
    const typet &element_type,
    const typet &index_type);

  /// Register a pointer target that conditionally points into one of two
  /// backing objects. This is used for expressions such as
  /// `p = cond ? &a[0] : &b[0]`, so later `*(p + i)` can lower to an ITE
  /// between the two concrete array reads.
  void register_conditional_pointer_target(
    const irep_idt &ptr_id,
    const exprt &condition,
    const pointer_targett &true_target,
    const pointer_targett &false_target);
  void register_conditional_pointer_target(
    const irep_idt &ptr_id,
    const conditional_pointer_targett &target);

  std::optional<pointer_targett> resolve_pointer_target(const exprt &expr) const;
  std::optional<conditional_pointer_targett>
  resolve_conditional_pointer_target(const exprt &expr) const;

  /// 查找已注册的符号
  /// @param id 符号标识符
  /// @return 节点 ID，如果未找到返回 nullopt
  std::optional<btor2_nid_t> lookup_symbol(const irep_idt &id) const;

  /// 查找已注册符号的 BTOR2 存储类型
  std::optional<typet> lookup_symbol_type(const irep_idt &id) const;

  /// 清除所有缓存（但保留符号映射）
  void clear_caches();

private:
  memory_accesst *memory = nullptr;
  btor2_nid_t unsupported_pointer_input(btor2_nid_t sort, const std::string &name);
  btor2_buildert &builder;  ///< BTOR2 构建器引用
  const namespacet &ns;     ///< 命名空间
  messaget &log;            ///< 消息处理器
  bool emit_warning_comments = false;
  bool conversion_had_errors = false;

  /// 表达式转换缓存：避免重复转换相同的表达式
  std::map<exprt, btor2_nid_t> expr_cache;

  /// 类型转换缓存：避免重复创建相同的类型
  std::map<typet, btor2_nid_t> type_cache;

  /// Counter used for conservative fresh inputs that stand in for symbols
  /// that were not collected as BTOR2 state, typically flattened aggregate
  /// projections from library-heavy code.
  std::size_t unknown_symbol_counter = 0;

  /// 符号映射：符号 ID → BTOR2 节点 ID
  std::map<irep_idt, btor2_nid_t> symbol_map;
  /// 符号映射：符号 ID → BTOR2 存储类型
  std::map<irep_idt, typet> symbol_type_map;
  /// Fixed-size arrays lowered to per-element scalar states.
  std::map<irep_idt, scalar_array_infot> scalar_array_map;

  /// Pointer symbol -> target mapping.
  std::map<irep_idt, pointer_targett> pointer_targets;
  /// Pointer symbol -> conditional target mapping.
  std::map<irep_idt, conditional_pointer_targett> conditional_pointer_targets;

  /// Pointer symbol -> all distinct backing arrays ever observed as
  /// assignment targets.  Populated during the pre-collection pass.
  /// When a pointer maps to 2+ arrays, it is "ambiguous" and single-target
  /// resolution is unsound (the flow-insensitive pointer_targets map only
  /// retains the last assignment).
  std::map<irep_idt, std::vector<irep_idt>> known_pointer_targets;

  /// Array/object identifier -> stable object id.
  std::map<irep_idt, mp_integer> object_ids;
  mp_integer next_object_id = 3; // 0 = NULL, 1/2 reserved
  std::map<irep_idt, exprt> addressable_object_sizes;
  std::map<irep_idt, typet> addressable_object_types;
  bool addressable_objects_frozen = false;

  /// Counter to give stable names to generated nondet inputs.
  std::size_t nondet_counter = 0;
  /// Counter to give stable names to generated array-literal base inputs.
  std::size_t array_literal_counter = 0;
  /// Counter to give stable names to generated allocate inputs.
  std::size_t allocate_counter = 0;

  //=========================================================================
  // 具体表达式类型的转换方法
  //=========================================================================

  /// 转换常量表达式
  /// 处理整数常量和布尔常量
  btor2_nid_t convert_constant(const constant_exprt &expr);

  /// 转换符号表达式
  /// 查找已注册的符号并返回其节点 ID
  btor2_nid_t convert_symbol(const symbol_exprt &expr);

  /// 转换类型转换表达式
  /// 处理位宽扩展（符号/零扩展）和截断
  btor2_nid_t convert_typecast(const typecast_exprt &expr);

  /// Check constant modes or guard a dynamic mode at the current instruction.
  bool require_float_rounding_mode(const exprt &mode, unsigned expected);
  btor2_nid_t convert_float_rounding_mode(const exprt &mode);
  btor2_nid_t convert_float_math(const exprt &expr);

  /// Convert floating-point casts through self-contained IEEE bit circuits.
  btor2_nid_t convert_floatbv_typecast(const floatbv_typecast_exprt &expr);

  /// Convert floating-point arithmetic through the same IEEE bit circuits.
  btor2_nid_t convert_floatbv_op(const ieee_float_op_exprt &expr);

  /// Convert IEEE floating-point comparisons and equality predicates.
  btor2_nid_t convert_floatbv_relation(const binary_relation_exprt &expr);

  /// Convert floating-point predicates such as isnan/isinf/isfinite/isnormal.
  btor2_nid_t convert_floatbv_predicate(const unary_exprt &expr);

  /// Convert floating-point unary operations such as unary minus and abs.
  btor2_nid_t convert_floatbv_unary(const unary_exprt &expr);

  /// 转换一元表达式
  /// 处理逻辑非、按位取反、算术取反
  btor2_nid_t convert_unary(const unary_exprt &expr);

  /// 转换二元/多元表达式
  /// 处理算术运算、位运算、逻辑运算
  btor2_nid_t convert_binary(const exprt &expr);

  /// 转换比较表达式
  /// 处理 ==, !=, <, <=, >, >=
  btor2_nid_t convert_comparison(const binary_relation_exprt &expr);

  /// 转换条件表达式 (if-then-else)
  btor2_nid_t convert_if(const if_exprt &expr);

  /// 转换数组索引表达式 (array[index])
  btor2_nid_t convert_index(const index_exprt &expr);

  /// Read from a scalarized fixed-size array by building a small ITE mux over
  /// its per-element state variables.
  btor2_nid_t read_scalar_array(
    const irep_idt &id,
    const exprt &index_expr,
    const typet &target_type);

  /// Convert address-of expressions.
  btor2_nid_t convert_address_of(const address_of_exprt &expr);

  /// Convert dereference expressions.
  btor2_nid_t convert_dereference(const dereference_exprt &expr);

  /// Convert pointer_object expressions.
  btor2_nid_t convert_pointer_object(const pointer_object_exprt &expr);

  /// Convert pointer_offset expressions.
  btor2_nid_t convert_pointer_offset(const pointer_offset_exprt &expr);

  /// Convert object_size expressions.
  btor2_nid_t convert_object_size(const object_size_exprt &expr);

  /// Convert is_invalid_pointer expressions.
  btor2_nid_t convert_is_invalid_pointer(const unary_exprt &expr);

  /// Convert is_dynamic_object expressions.
  btor2_nid_t convert_is_dynamic_object(const unary_exprt &expr);

  /// Convert an array literal expression (e.g. {1,2,3}).
  btor2_nid_t convert_array(const array_exprt &expr);

  /// Convert an array-of expression (array_of(x)).
  btor2_nid_t convert_array_of(const array_of_exprt &expr);

  /// 转换数组更新表达式 (array with [index := value])
  btor2_nid_t convert_with(const with_exprt &expr);

  /// 转换结构体成员访问表达式
  /// 注意：结构体支持有限
  // Also accepts indexed member accesses, so pointer-backed arrays are read
  // at their scalar element sort without materializing an aggregate view.
  btor2_nid_t convert_member(const exprt &expr);

  /// 转换位提取表达式
  btor2_nid_t convert_extractbits(const extractbits_exprt &expr);

  btor2_nid_t convert_byte_extract(const exprt &expr);

  btor2_nid_t convert_bswap(const bswap_exprt &expr);

  /// 转换位拼接表达式
  btor2_nid_t convert_concatenation(const concatenation_exprt &expr);

  /// 转换溢出检查表达式
  /// 处理加法、减法、乘法的溢出检查
  btor2_nid_t convert_overflow(const binary_overflow_exprt &expr);

  /// Convert a nondet side-effect expression to a BTOR2 input.
  btor2_nid_t convert_nondet(const side_effect_exprt &expr);

  /// Convert an allocate side-effect expression to a BTOR2 input.
  btor2_nid_t convert_allocate(const side_effect_exprt &expr);

  /// Convert prophecy r/w ok predicates by lowering to pointer predicates.
  btor2_nid_t convert_prophecy_r_or_w_ok(const prophecy_r_or_w_ok_exprt &expr);

  mp_integer get_object_id(const irep_idt &array_id);

  /// 检查类型是否为有符号类型
  /// @param type 要检查的类型
  /// @return 如果是有符号类型返回 true
  bool is_signed(const typet &type) const;
};

#endif // CPROVER_GOTO_BTOR2_EXPR_TO_BTOR2_H
