/*******************************************************************\

Module: Expression-to-BTOR2 conversion -- floating-point operations

Author: Based on CBMC project

\*******************************************************************/

/// \file
/// 浮点相关表达式到 BTOR2 的转换
///
/// 浮点算术直接在 BTOR2 构建器上生成自包含的 IEEE 754 位级电路：
/// 解码符号/阶码/尾数，在扩展定点有效数上计算，最后做一次
/// 按当前 IEEE 舍入模式完成舍入；NaN/Inf/零等特殊值走显式分支。
/// 电路不含自由位，也不引入任何全局假设。
///
/// 包含的转换方法：
/// - convert_floatbv_typecast: 浮点类型转换（float↔int, float↔float）
/// - convert_floatbv_op: 浮点算术（+, -, *, /; % 暂不支持）
/// - convert_floatbv_relation: 浮点比较（==, !=, <, <=, >, >=）
/// - convert_floatbv_predicate: 浮点谓词（isnan, isinf, isfinite, isnormal）
/// - convert_floatbv_unary: 浮点一元操作（negate, abs）
///
/// 支持边界：
/// - 算术/向浮点转换支持五种 CBMC IEEE 舍入模式；向整数转换截断到零。
/// - sqrt/FMA 使用当前模式；remainder/fmod 的精确结果不依赖当前模式。
/// - binary32/binary64 包含非正规数和渐进下溢；其他格式拒绝。
/// - 动态舍入模式及整数转换定义域由执行路径上的 model_limit 检查。

#include "expr_to_btor2.h"
#include "btor2_type_utils.h"
#include "ieee754_arith.h"
#include "memory_access.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/ieee_float.h>
#include <util/std_expr.h>

namespace
{
bool supported_format(const typet &type)
{
  if(type.id() != ID_floatbv)
    return true;
  const ieee_float_spect spec(to_floatbv_type(type));
  return !spec.x86_extended &&
         ((spec.e == 8 && spec.f == 23) || (spec.e == 11 && spec.f == 52));
}
} // namespace

btor2_nid_t expr_to_btor2t::convert_float_rounding_mode(const exprt &mode)
{
  if(mode.is_constant())
  {
    const auto value = numeric_cast<mp_integer>(mode);
    if(value && *value >= 0 && *value <= 4)
      return builder.constd(builder.get_or_create_bitvec_sort(3), *value);
    log.warning() << "Unsupported floating-point rounding mode for BTOR2"
                  << messaget::eom;
    return 0;
  }
  const auto width = get_width(mode.type());
  const auto actual = convert(mode);
  if(!width || !actual || !memory)
    return 0;
  const auto sort = builder.get_or_create_bitvec_sort(*width);
  auto valid = *width < 3 ? builder.one(builder.get_bool_sort())
    : builder.ulte(builder.get_bool_sort(), actual, builder.constd(sort, 4));
  if(is_signed(mode.type()))
    valid = builder.land(builder.get_bool_sort(), valid,
                         builder.sgte(builder.get_bool_sort(), actual, builder.zero(sort)));
  memory->heap.require(valid, true);
  return *width == 3 ? actual : *width > 3
    ? builder.slice(builder.get_or_create_bitvec_sort(3), actual, 2, 0)
    : builder.uext(builder.get_or_create_bitvec_sort(3), actual, 3 - *width);
}

btor2_nid_t expr_to_btor2t::convert_float_math(const exprt &expr)
{
  if(!supported_format(expr.type()) || expr.type().id() != ID_floatbv)
    return 0;
  const auto width = get_width(expr.type());
  const bool remainder = expr.id() == "c2btor_remainder" || expr.id() == "c2btor_fmod";
  const auto mode = remainder ? builder.zero(builder.get_or_create_bitvec_sort(3))
    : convert_float_rounding_mode(expr.operands().back());
  if(!width || !mode)
    return 0;
  std::vector<btor2_nid_t> args;
  const auto count = expr.operands().size() - (remainder ? 0 : 1);
  for(std::size_t i = 0; i < count; ++i)
  {
    const auto value = convert(expr.operands()[i]);
    if(!value || expr.operands()[i].type() != expr.type())
      return 0;
    args.push_back(value);
  }
  ieee754_aritht arith(builder, *width, mode);
  if(expr.id() == "c2btor_sqrt" && args.size() == 1)
    return arith.sqrt(args[0]);
  if(expr.id() == "c2btor_fma" && args.size() == 3)
    return arith.fma(args[0], args[1], args[2]);
  if(remainder && args.size() == 2)
    return arith.remainder(args[0], args[1], expr.id() == "c2btor_remainder");
  return 0;
}

bool expr_to_btor2t::require_float_rounding_mode(
  const exprt &mode,
  unsigned expected)
{
  if(mode.id() == ID_constant)
  {
    mp_integer value;
    if(!to_integer(to_constant_expr(mode), value) && value == expected)
      return true;
    log.warning() << "Unsupported floating-point rounding mode for BTOR2"
                  << messaget::eom;
    return false;
  }
  // The rounding variable is mutable. Guard the current value at this
  // instruction, rather than treating its initializer as a global constant.
  const auto width = get_width(mode.type());
  const auto actual = convert(mode);
  if(!width || !actual || !memory)
    return false;
  memory->heap.require(
    builder.eq(
      builder.get_bool_sort(),
      actual,
      builder.constd(builder.get_or_create_bitvec_sort(*width), expected)),
    true);
  return true;
}

btor2_nid_t
expr_to_btor2t::convert_floatbv_typecast(const floatbv_typecast_exprt &expr)
{
  const typet &src_type = expr.op().type();
  const typet &dest_type = expr.type();

  if(src_type == dest_type)
    return convert(expr.op());

  if(src_type.id() == ID_c_bit_field)
  {
    return convert_floatbv_typecast(floatbv_typecast_exprt(
      typecast_exprt(
        expr.op(), to_c_bit_field_type(src_type).underlying_type()),
      expr.rounding_mode(),
      dest_type));
  }

  const auto src_width = get_width(src_type);
  const auto dest_width = get_width(dest_type);
  if(!src_width.has_value() || !dest_width.has_value())
    return 0;

  const auto mode = dest_type.id() == ID_floatbv
                      ? convert_float_rounding_mode(expr.rounding_mode()) : 0;
  if(dest_type.id() == ID_floatbv ? mode == 0
     : !require_float_rounding_mode(expr.rounding_mode(), ieee_floatt::ROUND_TO_ZERO))
    return 0;

  const btor2_nid_t op = convert(expr.op());
  if(op == 0)
    return 0;

  if(!supported_format(src_type) || !supported_format(dest_type))
  {
    log.warning() << "Unsupported floating-point format for BTOR2"
                  << messaget::eom;
    return 0;
  }

  ieee754_aritht arith(
    builder, dest_type.id() == ID_floatbv ? *dest_width : *src_width, mode);

  if(src_type.id() == ID_floatbv && dest_type.id() == ID_floatbv)
    return arith.cast_float_to_float(op, *src_width);
  if(src_type.id() == ID_signedbv && dest_type.id() == ID_floatbv)
    return arith.cast_int_to_float(op, *src_width, true);
  if(src_type.id() == ID_unsignedbv && dest_type.id() == ID_floatbv)
    return arith.cast_int_to_float(op, *src_width, false);
  if(
    src_type.id() == ID_floatbv &&
    (dest_type.id() == ID_signedbv || dest_type.id() == ID_unsignedbv))
  {
    if(!memory)
      return 0;
    // A non-representable C cast has no defined result. Report the boundary
    // and freeze this execution instead of silently producing zero/wrapping.
    memory->heap.require(
      arith.float_to_int_valid(op, *dest_width, dest_type.id() == ID_signedbv),
      true);
    return arith.cast_float_to_int(op, *dest_width);
  }

  log.warning() << "Unsupported floatbv_typecast for BTOR2: " << src_type.id()
                << " -> " << dest_type.id() << messaget::eom;
  return 0;
}

btor2_nid_t expr_to_btor2t::convert_floatbv_op(const ieee_float_op_exprt &expr)
{
  if(expr.type().id() != ID_floatbv)
    return 0;

  const auto width = get_width(expr.type());
  if(!width.has_value() || !supported_format(expr.type()))
  {
    log.warning() << "Unsupported floating-point format for BTOR2"
                  << messaget::eom;
    return 0;
  }

  const auto mode = convert_float_rounding_mode(expr.rounding_mode());
  if(!mode)
    return 0;

  const btor2_nid_t lhs = convert(expr.lhs());
  const btor2_nid_t rhs = convert(expr.rhs());
  if(lhs == 0 || rhs == 0)
    return 0;

  ieee754_aritht arith(builder, *width, mode);

  if(expr.id() == ID_floatbv_plus)
    return arith.add(lhs, rhs, false);
  if(expr.id() == ID_floatbv_minus)
    return arith.add(lhs, rhs, true);
  if(expr.id() == ID_floatbv_mult)
    return arith.mul(lhs, rhs);
  if(expr.id() == ID_floatbv_div)
    return arith.div(lhs, rhs);

  log.warning() << "Unsupported floating-point arithmetic for BTOR2: "
                << expr.id() << messaget::eom;
  return 0;
}

btor2_nid_t
expr_to_btor2t::convert_floatbv_relation(const binary_relation_exprt &expr)
{
  const typet &lhs_type = expr.lhs().type();
  const typet &rhs_type = expr.rhs().type();
  if(lhs_type.id() != ID_floatbv || rhs_type.id() != ID_floatbv)
  {
    log.warning() << "Unsupported mixed floating-point relation for BTOR2: "
                  << lhs_type.id() << " and " << rhs_type.id() << messaget::eom;
    return 0;
  }

  const auto lhs_width = get_width(lhs_type);
  const auto rhs_width = get_width(rhs_type);
  if(
    !lhs_width.has_value() || lhs_width != rhs_width ||
    !supported_format(lhs_type) || !supported_format(rhs_type))
    return 0;

  const btor2_nid_t lhs = convert(expr.lhs());
  const btor2_nid_t rhs = convert(expr.rhs());
  if(lhs == 0 || rhs == 0)
    return 0;

  ieee754_aritht arith(builder, *lhs_width);

  if(expr.id() == ID_equal || expr.id() == ID_ieee_float_equal)
    return arith.relation(lhs, rhs, 0);
  if(expr.id() == ID_notequal || expr.id() == ID_ieee_float_notequal)
    return builder.lnot(builder.get_bool_sort(), arith.relation(lhs, rhs, 0));
  if(expr.id() == ID_lt)
    return arith.relation(lhs, rhs, 1);
  if(expr.id() == ID_le)
    return arith.relation(lhs, rhs, 2);
  if(expr.id() == ID_gt)
    return arith.relation(lhs, rhs, 3);
  if(expr.id() == ID_ge)
    return arith.relation(lhs, rhs, 4);
  return 0;
}

btor2_nid_t expr_to_btor2t::convert_floatbv_predicate(const unary_exprt &expr)
{
  if(expr.op().type().id() != ID_floatbv)
  {
    log.warning() << "Unsupported floating-point predicate operand for BTOR2: "
                  << expr.op().type().id() << messaget::eom;
    return 0;
  }

  const auto width = get_width(expr.op().type());
  if(!width.has_value() || !supported_format(expr.op().type()))
  {
    log.warning() << "Unsupported floating-point format for BTOR2"
                  << messaget::eom;
    return 0;
  }

  const btor2_nid_t op = convert(expr.op());
  if(op == 0)
    return 0;

  ieee754_aritht arith(builder, *width);

  if(expr.id() == ID_isnan)
    return arith.is_nan_node(op);
  if(expr.id() == ID_isinf)
    return arith.is_inf_node(op);
  if(expr.id() == ID_isfinite)
    return builder.land(
      builder.get_bool_sort(),
      builder.lnot(builder.get_bool_sort(), arith.is_nan_node(op)),
      builder.lnot(builder.get_bool_sort(), arith.is_inf_node(op)));
  if(expr.id() == ID_isnormal)
    return arith.is_normal_node(op);
  return 0;
}

btor2_nid_t expr_to_btor2t::convert_floatbv_unary(const unary_exprt &expr)
{
  if(expr.op().type().id() != ID_floatbv || expr.type().id() != ID_floatbv)
    return 0;

  const auto width = get_width(expr.type());
  if(!width.has_value() || !supported_format(expr.op().type()))
  {
    log.warning() << "Unsupported floating-point format for BTOR2"
                  << messaget::eom;
    return 0;
  }

  const btor2_nid_t op = convert(expr.op());
  if(op == 0)
    return 0;

  ieee754_aritht arith(builder, *width);

  if(expr.id() == ID_unary_minus)
    return arith.neg(op);
  if(expr.id() == ID_abs)
    return arith.abs_value(op);
  if(expr.id() == ID_unary_plus)
    return op;
  return 0;
}
