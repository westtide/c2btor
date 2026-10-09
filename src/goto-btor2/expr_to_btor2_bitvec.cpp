/*******************************************************************\

Module: Expression-to-BTOR2 conversion -- bitvector operations

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// Bitvector-related member functions of expr_to_btor2t.
///
/// This translation unit contains the conversions for:
///  - typecast / unary / binary / comparison arithmetic
///  - if-then-else
///  - extractbits / concatenation / byte-extract / bswap
///  - overflow checks

#include "expr_to_btor2.h"
#include "btor2_type_utils.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/ieee_float.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>

/// 转换类型转换表达式（typecast）
/// 
/// 处理三种情况：
/// 1. 位宽相同：无需转换，直接返回操作数
/// 2. 位宽扩展：使用 sext（符号扩展）或 uext（零扩展）
/// 3. 位宽截断：使用 slice 提取低位
/// 
/// BTOR2 指令:
///   sext <sort> <nid> <count>  ; 符号扩展 count 位
///   uext <sort> <nid> <count>  ; 零扩展 count 位
///   slice <sort> <nid> <upper> <lower>  ; 位切片
/// 
/// @param expr 类型转换表达式
/// @return 转换结果的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_typecast(const typecast_exprt &expr)
{
  if(
    expr.type().id() == ID_floatbv &&
    (expr.op().type().id() == ID_bool || expr.op().type().id() == ID_c_bool))
  {
    btor2_nid_t op_nid = convert(expr.op());
    btor2_nid_t target_sort = convert_type(expr.type());
    if(op_nid == 0 || target_sort == 0)
      return 0;

    btor2_nid_t cond_nid = op_nid;
    if(expr.op().type().id() == ID_c_bool)
    {
      btor2_nid_t src_sort = convert_type(expr.op().type());
      if(src_sort == 0)
        return 0;
      cond_nid = builder.neq(
        builder.get_bool_sort(), op_nid, builder.zero(src_sort));
    }

    const auto &float_type = to_floatbv_type(expr.type());
    btor2_nid_t zero = builder.zero(target_sort);
    btor2_nid_t one =
      builder.constd(target_sort, ieee_float_valuet::one(float_type).pack());
    return builder.ite(target_sort, cond_nid, one, zero);
  }

  if(
    (expr.type().id() == ID_bool || expr.type().id() == ID_c_bool) &&
    expr.op().type().id() == ID_floatbv)
  {
    const auto &float_type = to_floatbv_type(expr.op().type());
    const constant_exprt zero = ieee_float_valuet::zero(float_type).to_expr();
    btor2_nid_t bool_result =
      convert_floatbv_relation(notequal_exprt(expr.op(), zero));

    if(bool_result == 0 || expr.type().id() == ID_bool)
      return bool_result;

    btor2_nid_t target_sort = convert_type(expr.type());
    if(target_sort == 0)
      return 0;

    const auto target_width = get_width(expr.type());
    if(!target_width.has_value())
      return 0;

    if(*target_width == 1)
      return bool_result;

    return builder.uext(target_sort, bool_result, *target_width - 1);
  }

  // Array-to-pointer decay should keep using the pointer-target analysis
  // instead of materializing an intermediate BTOR2 array value. This matters
  // for flattened/scalarized member arrays such as `m.data[0]`, where the
  // backing object is addressable but the aggregate row itself is not emitted
  // as a standalone BTOR2 state.
  if(!memory && expr.type().id() == ID_pointer)
  {
    std::optional<pointer_targett> target = resolve_pointer_target(expr.op());
    if(!target.has_value() && expr.op().type().id() == ID_array)
      target = resolve_pointer_target(address_of_exprt(expr.op()));

    if(target.has_value())
      return encode_pointer_target(*target, expr.type());
  }

  // 转换操作数
  btor2_nid_t op_nid = convert(expr.op());
  if(op_nid == 0)
    return 0;

  // 获取目标类型的 sort
  btor2_nid_t target_sort = convert_type(expr.type());
  if(target_sort == 0)
    return 0;

  // Array sorts have no meaningful bit-width for sext/uext/slice.
  // If the source type is an array, the typecast is invalid at the
  // BTOR2 level (array-to-scalar must go through read, not typecast).
  // If both source and target are the same array sort, the typecast is
  // a no-op.
  if(expr.op().type().id() == ID_array)
  {
    if(expr.type().id() == ID_array)
      return op_nid; // same sort, no-op
    // Array-to-bitvec typecast should not reach here; it is a bug
    // in the goto IR or in how array states are used in conditions.
    // Return 0 to signal failure and let the caller produce an unknown.
    return 0;
  }

  // 获取源和目标类型的位宽
  auto src_width = get_width(expr.op().type());
  auto dst_width = get_width(expr.type());

  if(!src_width || !dst_width)
    return 0;

  if(expr.type().id() == ID_bool || expr.type().id() == ID_c_bool)
  {
    // C scalar-to-boolean conversion tests for zero; truncating the low bit
    // would turn 2 into false or leave a noncanonical _Bool byte value.
    const auto source_sort = convert_type(expr.op().type());
    if(source_sort == 0)
      return 0;
    const auto normalized = builder.neq(
      builder.get_bool_sort(), op_nid, builder.zero(source_sort));
    return *dst_width == 1
             ? normalized
             : builder.uext(target_sort, normalized, *dst_width - 1);
  }

  if(*src_width == *dst_width)
  {
    // 位宽相同，BTOR2 中无需转换
    return op_nid;
  }
  else if(*src_width < *dst_width)
  {
    // 扩展：源位宽 < 目标位宽
    unsigned extension = *dst_width - *src_width;
    if(is_signed(expr.op().type()))
      return builder.sext(target_sort, op_nid, extension);  // 符号扩展
    else
      return builder.uext(target_sort, op_nid, extension);  // 零扩展
  }
  else
  {
    // 截断：源位宽 > 目标位宽，保留低位
    return builder.slice(target_sort, op_nid, *dst_width - 1, 0);
  }
}

/// 转换一元表达式
/// 
/// 支持的操作：
/// - not/bitnot: 按位取反 (BTOR2: not)
/// - unary_minus: 算术取反 (BTOR2: neg)
/// - unary_plus: 正号，无操作
/// 
/// BTOR2 指令:
///   not <sort> <nid>   ; 按位取反
///   neg <sort> <nid>   ; 算术取反 (-x = ~x + 1)
/// 
/// @param expr 一元表达式
/// @return 转换结果的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_unary(const unary_exprt &expr)
{
  if(expr.type().id() == ID_floatbv)
  {
    if(expr.id() == ID_unary_minus || expr.id() == ID_unary_plus ||
       expr.id() == ID_abs)
      return convert_floatbv_unary(expr);
  }

  // 转换操作数
  btor2_nid_t op_nid = convert(expr.op());
  if(op_nid == 0)
    return 0;

  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  if(expr.id() == ID_not || expr.id() == ID_bitnot)
  {
    // 逻辑非或按位取反 → BTOR2 not
    return builder.lnot(sort, op_nid);
  }
  else if(expr.id() == ID_unary_minus)
  {
    // 算术取反 → BTOR2 neg
    return builder.neg(sort, op_nid);
  }
  else if(expr.id() == ID_unary_plus)
  {
    // 正号，无操作
    return op_nid;
  }

  return 0;
}

/// 转换二元表达式
/// 
/// 处理两种情况：
/// 1. 多操作数表达式（如 a + b + c）：转换为左结合链
/// 2. 双操作数表达式：直接转换
/// 
/// 支持的操作及其 BTOR2 对应：
/// - plus → add      加法
/// - minus → sub     减法
/// - mult → mul      乘法
/// - div → sdiv/udiv 有符号/无符号除法
/// - mod → srem/urem 有符号/无符号取余
/// - bitand/and → and 按位与
/// - bitor/or → or    按位或
/// - bitxor/xor → xor 按位异或
/// - shl → sll        逻辑左移
/// - ashr → sra       算术右移（保持符号）
/// - lshr → srl       逻辑右移（填充零）
/// - implies → implies 蕴含
/// 
/// @param expr 二元表达式
/// @return 转换结果的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_binary(const exprt &expr)
{
  if(expr.operands().size() < 2)
    return 0;

  // Pointer arithmetic operates on the byte-offset portion of the packed
  // pointer. Scale integer operands by sizeof(*p), as required by C.
  if(
    expr.type().id() == ID_pointer &&
    (expr.id() == ID_plus || expr.id() == ID_minus) &&
    expr.operands().size() == 2)
  {
    const exprt *pointer_op = nullptr;
    const exprt *integer_op = nullptr;
    if(expr.operands()[0].type().id() == ID_pointer)
    {
      pointer_op = &expr.operands()[0];
      integer_op = &expr.operands()[1];
    }
    else if(
      expr.id() == ID_plus &&
      expr.operands()[1].type().id() == ID_pointer)
    {
      pointer_op = &expr.operands()[1];
      integer_op = &expr.operands()[0];
    }
    if(pointer_op != nullptr)
    {
      btor2_nid_t sort = convert_type(expr.type());
      btor2_nid_t pointer_nid = convert(*pointer_op);
      auto size_opt = size_of_expr(
        to_pointer_type(pointer_op->type()).base_type(), ns);
      if(sort == 0 || pointer_nid == 0 || !size_opt.has_value())
        return 0;
      typet offset_type = integer_op->type();
      if(offset_type.id() != ID_signedbv && offset_type.id() != ID_unsignedbv)
      {
        auto pointer_width_opt = get_width(expr.type());
        if(!pointer_width_opt.has_value())
          return 0;
        offset_type = signedbv_typet(*pointer_width_opt);
      }
      exprt index_cast =
        typecast_exprt::conditional_cast(*integer_op, offset_type);
      exprt elem_size_cast =
        typecast_exprt::conditional_cast(*size_opt, offset_type);
      exprt scaled = mult_exprt(index_cast, elem_size_cast);
      scaled.type() = offset_type;
      scaled = simplify_expr(scaled, ns);
      btor2_nid_t scaled_nid = convert(
        typecast_exprt::conditional_cast(scaled, expr.type()));
      if(scaled_nid == 0)
        return 0;
      return expr.id() == ID_plus
               ? builder.add(sort, pointer_nid, scaled_nid)
               : builder.sub(sort, pointer_nid, scaled_nid);
    }
  }

  auto convert_as = [&](const exprt &op, const typet &target_type) -> btor2_nid_t {
    exprt casted = typecast_exprt::conditional_cast(op, target_type);
    return convert(casted);
  };

  // 处理多操作数表达式（结合性操作如 a + b + c）
  if(expr.operands().size() > 2)
  {
    // 转换为左结合链：((a + b) + c)
    btor2_nid_t sort = convert_type(expr.type());
    if(sort == 0)
      return 0;

    btor2_nid_t result = convert_as(expr.operands()[0], expr.type());
    if(result == 0)
      return 0;

    // 从第二个操作数开始，依次与累积结果组合
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
    {
      btor2_nid_t op_nid = convert_as(expr.operands()[i], expr.type());
      if(op_nid == 0)
        return 0;

      // 根据操作类型应用相应的 BTOR2 指令
      if(expr.id() == ID_plus)
        result = builder.add(sort, result, op_nid);
      else if(expr.id() == ID_mult)
        result = builder.mul(sort, result, op_nid);
      else if(expr.id() == ID_bitand || expr.id() == ID_and)
        result = builder.land(sort, result, op_nid);
      else if(expr.id() == ID_bitor || expr.id() == ID_or)
        result = builder.lor(sort, result, op_nid);
      else if(expr.id() == ID_bitxor || expr.id() == ID_xor)
        result = builder.lxor(sort, result, op_nid);
      else
        return 0;  // 不支持的多操作数操作
    }
    return result;
  }

  // 标准双操作数情况
  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  btor2_nid_t lhs_nid = 0;
  btor2_nid_t rhs_nid = 0;
  typet lhs_cast_type = expr.type();
  typet rhs_cast_type = expr.type();

  // BTOR2 shift ops require the shift amount to have the same sort as lhs.
  if(expr.id() == ID_shl || expr.id() == ID_ashr || expr.id() == ID_lshr)
    rhs_cast_type = lhs_cast_type;

  lhs_nid = convert_as(expr.operands()[0], lhs_cast_type);
  rhs_nid = convert_as(expr.operands()[1], rhs_cast_type);
  if(lhs_nid == 0 || rhs_nid == 0)
    return 0;

  // 确定是否为有符号操作（影响除法、取余和移位的选择）
  bool is_signed_op = is_signed(lhs_cast_type);

  //--- 算术运算 ---
  if(expr.id() == ID_plus)
    return builder.add(sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_minus)
    return builder.sub(sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_mult)
    return builder.mul(sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_div)
    // 有符号除法使用 sdiv，无符号使用 udiv
    return is_signed_op ? builder.sdiv(sort, lhs_nid, rhs_nid)
                        : builder.udiv(sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_mod)
    // 有符号取余使用 srem，无符号使用 urem
    return is_signed_op ? builder.srem(sort, lhs_nid, rhs_nid)
                        : builder.urem(sort, lhs_nid, rhs_nid);
  //--- 位运算 ---
  else if(expr.id() == ID_bitand || expr.id() == ID_and)
    return builder.land(sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_bitor || expr.id() == ID_or)
    return builder.lor(sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_bitxor || expr.id() == ID_xor)
    return builder.lxor(sort, lhs_nid, rhs_nid);
  //--- 移位运算 ---
  else if(expr.id() == ID_shl)
    return builder.sll(sort, lhs_nid, rhs_nid);   // 逻辑左移
  else if(expr.id() == ID_ashr)
    return builder.sra(sort, lhs_nid, rhs_nid);   // 算术右移
  else if(expr.id() == ID_lshr)
    return builder.srl(sort, lhs_nid, rhs_nid);   // 逻辑右移
  //--- 逻辑运算 ---
  else if(expr.id() == ID_implies)
    return builder.implies(sort, lhs_nid, rhs_nid);  // 蕴含

  return 0;
}

/// 转换比较表达式
/// 
/// 支持的比较操作及其 BTOR2 对应：
/// - equal → eq       相等
/// - notequal → neq   不等
/// - lt → slt/ult     小于（有符号/无符号）
/// - le → slte/ulte   小于等于
/// - gt → sgt/ugt     大于
/// - ge → sgte/ugte   大于等于
/// 
/// 所有比较操作返回 1 位布尔值。
/// 
/// @param expr 比较表达式
/// @return 转换结果的节点 ID（1 位），失败返回 0
btor2_nid_t expr_to_btor2t::convert_comparison(const binary_relation_exprt &expr)
{
  if(
    expr.lhs().type().id() == ID_floatbv ||
    expr.rhs().type().id() == ID_floatbv ||
    expr.id() == ID_ieee_float_equal ||
    expr.id() == ID_ieee_float_notequal)
  {
    return convert_floatbv_relation(expr);
  }

  btor2_nid_t lhs_nid = convert(expr.lhs());
  btor2_nid_t rhs_nid = convert(expr.rhs());
  if(lhs_nid == 0 || rhs_nid == 0)
    return 0;

  // 比较结果类型为 1 位布尔
  btor2_nid_t bool_sort = builder.get_bool_sort();
  bool is_signed_cmp = is_signed(expr.lhs().type());

  if(expr.id() == ID_equal)
    return builder.eq(bool_sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_notequal)
    return builder.neq(bool_sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_lt)
    return is_signed_cmp ? builder.slt(bool_sort, lhs_nid, rhs_nid)
                         : builder.ult(bool_sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_le)
    return is_signed_cmp ? builder.slte(bool_sort, lhs_nid, rhs_nid)
                         : builder.ulte(bool_sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_gt)
    return is_signed_cmp ? builder.sgt(bool_sort, lhs_nid, rhs_nid)
                         : builder.ugt(bool_sort, lhs_nid, rhs_nid);
  else if(expr.id() == ID_ge)
    return is_signed_cmp ? builder.sgte(bool_sort, lhs_nid, rhs_nid)
                         : builder.ugte(bool_sort, lhs_nid, rhs_nid);

  return 0;
}

/// 转换条件表达式 (if-then-else)
/// 
/// C 语言中的三目运算符 `cond ? then : else` 对应 BTOR2 的 ite 指令。
/// 
/// BTOR2 格式:
///   <nid> ite <sort> <cond> <then> <else>
/// 
/// 语义: if cond then then_value else else_value
/// 
/// @param expr 条件表达式
/// @return 转换结果的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_if(const if_exprt &expr)
{
  btor2_nid_t cond_nid = convert(expr.cond());       // 条件
  btor2_nid_t then_nid = convert(expr.true_case());  // then 分支
  btor2_nid_t else_nid = convert(expr.false_case()); // else 分支

  if(cond_nid == 0 || then_nid == 0 || else_nid == 0)
    return 0;

  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  return builder.ite(sort, cond_nid, then_nid, else_nid);
}

/// 转换位提取表达式 (extractbits)
/// 
/// 从位向量中提取连续的位。
/// 对应 BTOR2 的 slice 指令。
/// 
/// BTOR2 格式:
///   <nid> slice <sort> <src> <upper> <lower>
/// 
/// 例如：extractbits(x, 7, 0) 提取 x 的低 8 位
/// 
/// @param expr 位提取表达式
/// @return 转换结果的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_extractbits(const extractbits_exprt &expr)
{
  btor2_nid_t src_nid = convert(expr.src());
  if(src_nid == 0)
    return 0;

  btor2_nid_t sort = convert_type(expr.type());
  if(sort == 0)
    return 0;

  // extractbits 使用 index 作为起始位置（低位边界）
  // 类型宽度决定上界
  mp_integer index_val;
  if(to_integer(to_constant_expr(expr.index()), index_val))
  {
    // 非常量索引不支持
    log.warning() << "Non-constant extractbits index not supported"
                  << messaget::eom;
    return 0;
  }

  auto width = get_width(expr.type());
  if(!width)
    return 0;

  // 计算位范围：[lower, upper]
  unsigned lower = numeric_cast_v<unsigned>(index_val);
  unsigned upper = lower + static_cast<unsigned>(*width) - 1;

  return builder.slice(sort, src_nid, upper, lower);
}

/// 转换位拼接表达式 (concatenation)
/// 
/// 将多个位向量拼接成一个更大的位向量。
/// 对应 BTOR2 的 concat 指令。
/// 
/// BTOR2 格式:
///   <nid> concat <sort> <high_bits> <low_bits>
/// 
/// 例如：concat(a, b) = a || b（a 在高位，b 在低位）
/// 
/// @param expr 拼接表达式
/// @return 转换结果的节点 ID，失败返回 0
btor2_nid_t expr_to_btor2t::convert_concatenation(const concatenation_exprt &expr)
{
  // 至少需要两个操作数
  if(expr.operands().size() < 2)
    return 0;

  // 从第一个操作数开始
  btor2_nid_t result = convert(expr.op0());
  if(result == 0)
    return 0;

  const auto final_width = get_width(expr.type());
  auto result_width = get_width(expr.op0().type());
  if(!final_width.has_value() || !result_width.has_value())
    return 0;

  // 从左到右依次拼接
  // concat(a, b, c) → concat(concat(a, b), c)
  for(std::size_t i = 1; i < expr.operands().size(); ++i)
  {
    btor2_nid_t op_nid = convert(expr.operands()[i]);
    if(op_nid == 0)
      return 0;

    const auto operand_width = get_width(expr.operands()[i].type());
    if(!operand_width.has_value())
      return 0;
    *result_width += *operand_width;
    btor2_nid_t concat_sort =
      builder.get_or_create_bitvec_sort(*result_width);
    result = builder.concat(concat_sort, result, op_nid);
  }

  return *result_width == *final_width ? result : 0;
}

btor2_nid_t expr_to_btor2t::convert_byte_extract(const exprt &expr)
{
  const exprt &src = to_binary_expr(expr).op0();
  const exprt &offset_expr = to_binary_expr(expr).op1();
  const typet &result_type = expr.type();

  auto src_width_opt = get_width(src.type());
  auto dst_width_opt = get_width(result_type);
  if(!src_width_opt || !dst_width_opt)
    return 0;

  btor2_nid_t src_nid = convert(src);
  if(src_nid == 0)
    return 0;

  auto offset_const = numeric_cast<mp_integer>(offset_expr);
  if(!offset_const)
  {
    btor2_nid_t offset_nid = convert(offset_expr);
    if(offset_nid == 0)
      return 0;
    return 0;
  }

  const mp_integer byte_offset_bits = (*offset_const) * 8;
  if(
    byte_offset_bits == 0 && *dst_width_opt > *src_width_opt &&
    *src_width_opt % 8 == 0 && *dst_width_opt % 8 == 0)
  {
    // Match boolbvt::convert_byte_extract: bits outside the source object
    // are fresh variables, not sign/zero extension. Function-pointer
    // lowering can produce such wider views when adapting call signatures.
    const auto extra_width = numeric_cast_v<std::size_t>(
      *dst_width_opt - *src_width_opt);
    const auto extra_sort = builder.get_or_create_bitvec_sort(extra_width);
    const auto extra = builder.input(extra_sort, "__byte_extract_padding");
    const auto result_sort = convert_type(result_type);
    return expr.id() == ID_byte_extract_little_endian
      ? builder.concat(result_sort, extra, src_nid)
      : builder.concat(result_sort, src_nid, extra);
  }
  if(
    byte_offset_bits < 0 ||
    byte_offset_bits + *dst_width_opt > *src_width_opt)
  {
    return 0;
  }

  mp_integer low_bits = byte_offset_bits;
  if(expr.id() == ID_byte_extract_big_endian)
    low_bits = *src_width_opt - *dst_width_opt - byte_offset_bits;

  if(low_bits == 0 && *src_width_opt == *dst_width_opt)
    return src_nid;

  if(low_bits + *dst_width_opt <= *src_width_opt)
  {
    unsigned high =
      static_cast<unsigned>((low_bits + *dst_width_opt - 1).to_long());
    unsigned low = static_cast<unsigned>(low_bits.to_long());
    btor2_nid_t sort = convert_type(result_type);
    return builder.slice(sort, src_nid, high, low);
  }

  return 0;
}

btor2_nid_t expr_to_btor2t::convert_bswap(const bswap_exprt &expr)
{
  auto width_opt = get_width(expr.type());
  if(!width_opt.has_value())
    return 0;

  const std::size_t width = numeric_cast_v<std::size_t>(*width_opt);
  const std::size_t byte_bits = expr.get_bits_per_byte();
  if(byte_bits == 0 || width == 0 || width % byte_bits != 0)
    return 0;

  btor2_nid_t op_nid = convert(expr.op());
  if(op_nid == 0)
    return 0;

  btor2_nid_t result = 0;
  std::size_t result_width = 0;
  const std::size_t byte_count = width / byte_bits;

  for(std::size_t i = 0; i < byte_count; ++i)
  {
    const std::size_t low = i * byte_bits;
    const std::size_t high = low + byte_bits - 1;
    btor2_nid_t byte_sort = builder.get_or_create_bitvec_sort(byte_bits);
    btor2_nid_t byte_nid = builder.slice(
      byte_sort,
      op_nid,
      static_cast<unsigned>(high),
      static_cast<unsigned>(low));
    if(byte_nid == 0)
      return 0;

    if(result == 0)
    {
      result = byte_nid;
      result_width = byte_bits;
    }
    else
    {
      result_width += byte_bits;
      btor2_nid_t concat_sort =
        builder.get_or_create_bitvec_sort(result_width);
      result = builder.concat(concat_sort, result, byte_nid);
    }
  }

  return result;
}

/// 转换溢出检查表达式
/// 
/// 检查算术运算是否会溢出。
/// 溢出检查对于有符号和无符号类型有不同的语义。
/// 
/// 溢出检测策略：
/// 
/// 1. 加法溢出 (overflow_plus):
///    - 有符号：两个正数相加得到负数，或两个负数相加得到正数
///    - 无符号：结果小于任一操作数
/// 
/// 2. 减法溢出 (overflow_minus):
///    - 有符号：符号不同且结果符号与被减数不同
///    - 无符号：被减数小于减数
/// 
/// 3. 乘法溢出 (overflow_mult):
///    - 使用双倍位宽计算，检查结果是否超出原位宽范围
/// 
/// @param expr 溢出检查表达式
/// @return 转换结果的节点 ID（1 位布尔），失败返回 0
btor2_nid_t expr_to_btor2t::convert_overflow(const binary_overflow_exprt &expr)
{
  auto width_opt = get_width(expr.lhs().type());
  if(!width_opt)
    return 0;

  std::size_t width = *width_opt;
  bool is_signed_op = is_signed(expr.lhs().type());

  // 转换操作数
  btor2_nid_t lhs_nid = convert(expr.lhs());
  btor2_nid_t rhs_nid = convert(expr.rhs());
  if(lhs_nid == 0 || rhs_nid == 0)
    return 0;

  btor2_nid_t bool_sort = builder.get_bool_sort();
  btor2_nid_t orig_sort = builder.get_or_create_bitvec_sort(width);

  //=========================================================================
  // 加法溢出检测
  //=========================================================================
  if(expr.id() == ID_overflow_plus)
  {
    // 计算加法结果
    btor2_nid_t result_nid = builder.add(orig_sort, lhs_nid, rhs_nid);
    
    if(is_signed_op)
    {
      // 有符号加法溢出：
      // - 正溢出：两个正数相加得到负数 (lhs >= 0 && rhs >= 0 && result < 0)
      // - 负溢出：两个负数相加得到正数 (lhs < 0 && rhs < 0 && result >= 0)
      
      btor2_nid_t sign_sort = builder.get_or_create_bitvec_sort(1);
      unsigned msb = static_cast<unsigned>(width - 1);
      
      // 提取符号位（最高位）
      btor2_nid_t lhs_sign = builder.slice(sign_sort, lhs_nid, msb, msb);
      btor2_nid_t rhs_sign = builder.slice(sign_sort, rhs_nid, msb, msb);
      btor2_nid_t res_sign = builder.slice(sign_sort, result_nid, msb, msb);
      
      btor2_nid_t zero_bit = builder.zero(sign_sort);
      btor2_nid_t one_bit = builder.one(sign_sort);
      
      // 判断正负：符号位 == 0 为正，符号位 == 1 为负
      btor2_nid_t lhs_pos = builder.eq(bool_sort, lhs_sign, zero_bit);
      btor2_nid_t rhs_pos = builder.eq(bool_sort, rhs_sign, zero_bit);
      btor2_nid_t res_neg = builder.eq(bool_sort, res_sign, one_bit);
      btor2_nid_t res_pos = builder.eq(bool_sort, res_sign, zero_bit);
      
      // 正溢出：两个正数相加得到负数
      btor2_nid_t pos_overflow = builder.land(bool_sort,
        builder.land(bool_sort, lhs_pos, rhs_pos), res_neg);
      
      // 负溢出：两个负数相加得到正数
      btor2_nid_t lhs_neg = builder.lnot(bool_sort, lhs_pos);
      btor2_nid_t rhs_neg = builder.lnot(bool_sort, rhs_pos);
      btor2_nid_t neg_overflow = builder.land(bool_sort,
        builder.land(bool_sort, lhs_neg, rhs_neg), res_pos);
      
      // 总溢出 = 正溢出 || 负溢出
      return builder.lor(bool_sort, pos_overflow, neg_overflow);
    }
    else
    {
      // 无符号加法溢出：结果 < 任一操作数（发生回绕）
      return builder.ult(bool_sort, result_nid, lhs_nid);
    }
  }
  //=========================================================================
  // 减法溢出检测
  //=========================================================================
  else if(expr.id() == ID_overflow_minus)
  {
    btor2_nid_t result_nid = builder.sub(orig_sort, lhs_nid, rhs_nid);
    
    if(is_signed_op)
    {
      // 有符号减法溢出：
      // 当 lhs 和 rhs 符号不同，且结果符号与 lhs 不同时发生溢出
      // 例如：正数 - 负数 = 负数（应该是正数）→ 溢出
      
      btor2_nid_t sign_sort = builder.get_or_create_bitvec_sort(1);
      unsigned msb = static_cast<unsigned>(width - 1);
      
      btor2_nid_t lhs_sign = builder.slice(sign_sort, lhs_nid, msb, msb);
      btor2_nid_t rhs_sign = builder.slice(sign_sort, rhs_nid, msb, msb);
      btor2_nid_t res_sign = builder.slice(sign_sort, result_nid, msb, msb);
      
      // 操作数符号不同
      btor2_nid_t signs_differ = builder.neq(bool_sort, lhs_sign, rhs_sign);
      // 结果符号与被减数不同
      btor2_nid_t res_sign_differs = builder.neq(bool_sort, res_sign, lhs_sign);
      
      return builder.land(bool_sort, signs_differ, res_sign_differs);
    }
    else
    {
      // 无符号减法下溢：rhs > lhs
      return builder.ugt(bool_sort, rhs_nid, lhs_nid);
    }
  }
  //=========================================================================
  // 乘法溢出检测
  //=========================================================================
  else if(expr.id() == ID_overflow_mult)
  {
    // 乘法溢出检测使用双倍位宽：
    // 1. 将操作数扩展到双倍位宽
    // 2. 计算乘积
    // 3. 将低位结果扩展回双倍位宽
    // 4. 如果扩展结果与原乘积不同，则发生溢出
    
    std::size_t double_width = width * 2;
    btor2_nid_t double_sort = builder.get_or_create_bitvec_sort(double_width);
    
    // 扩展操作数到双倍位宽
    btor2_nid_t lhs_ext, rhs_ext;
    if(is_signed_op)
    {
      // 有符号：符号扩展
      lhs_ext = builder.sext(double_sort, lhs_nid, static_cast<unsigned>(width));
      rhs_ext = builder.sext(double_sort, rhs_nid, static_cast<unsigned>(width));
    }
    else
    {
      // 无符号：零扩展
      lhs_ext = builder.uext(double_sort, lhs_nid, static_cast<unsigned>(width));
      rhs_ext = builder.uext(double_sort, rhs_nid, static_cast<unsigned>(width));
    }
    
    // 双倍位宽乘积
    btor2_nid_t product = builder.mul(double_sort, lhs_ext, rhs_ext);
    
    // 提取低位（实际结果）
    btor2_nid_t lower_result = builder.slice(orig_sort, product, 
      static_cast<unsigned>(width - 1), 0);
    
    // 将低位结果扩展回双倍位宽
    btor2_nid_t extended_lower;
    if(is_signed_op)
    {
      extended_lower = builder.sext(double_sort, lower_result, static_cast<unsigned>(width));
    }
    else
    {
      extended_lower = builder.uext(double_sort, lower_result, static_cast<unsigned>(width));
    }
    
    // 溢出条件：乘积 != 扩展后的低位结果
    // 这意味着有高位信息丢失
    return builder.neq(bool_sort, product, extended_lower);
  }

  return 0;
}
