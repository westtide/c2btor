// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

/*******************************************************************\

Module: Expression-to-BTOR2 conversion -- floating-point operations

Authors: C2BTOR contributors; CBMC attribution is retained in LICENSES/

\*******************************************************************/

/// \file
/// 浮点相关表达式到 BTOR2 的转换
///
/// 基本算术、类型转换和 round_to_integral 复用 CBMC float_utilst。
/// propt 适配器把布尔门映射为 BTOR2；除法的商/余数使用功能性 udiv/urem。
/// sqrt/FMA/remainder/fmod 保留专用 IEEE 电路。运行时舍入模式按值选择；
/// CBMC 对非法模式保留的任意舍入结果是 input，不是额外约束或性质。
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
/// - 仅编码输入 GOTO 的浮点数据操作，不插入辅助性质或停止条件。

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
  if(!width || !actual)
    return 0;
  const auto small_sort = builder.get_or_create_bitvec_sort(3);
  const auto full_sort = builder.get_or_create_bitvec_sort(*width);
  const auto small = *width == 3 ? actual : *width > 3
    ? builder.slice(small_sort, actual, 2, 0)
    : builder.uext(small_sort, actual, 3 - *width);
  // Preserve all five CBMC mode comparisons. Truncating first would turn
  // e.g. 8 into round-to-even. Invalid full-width values map to code 7, for
  // which CBMC's rounding decision retains its unspecified-value branch.
  auto valid = *width < 3 ? builder.one(builder.get_bool_sort())
    : builder.ulte(builder.get_bool_sort(), actual, builder.constd(full_sort, 4));
  if(is_signed(mode.type()))
    valid = builder.land(builder.get_bool_sort(), valid,
      builder.sgte(builder.get_bool_sort(), actual, builder.zero(full_sort)));
  return builder.ite(small_sort, valid, small, builder.constd(small_sort, 7));
}

btor2_nid_t expr_to_btor2t::convert_float_round_to_integral(const exprt &expr)
{
  if(expr.operands().size() != 2 || expr.type().id() != ID_floatbv ||
     !supported_format(expr.type()))
    return 0;
  const auto width = get_width(expr.type());
  const auto value = convert(expr.operands()[0]);
  const auto mode = convert_float_rounding_mode(expr.operands()[1]);
  if(!width || !value || !mode)
    return 0;
  return ieee754_aritht(builder, *width, mode).round_to_integral(value);
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
  // This implementation of float-to-integer conversion only implements
  // truncation. A nonconstant rounding operand is unsupported, not a
  // condition to impose on the program's execution.
  log.warning() << "Nonconstant float-to-integer rounding mode is unsupported"
                << messaget::eom;
  return false;
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
    // Directly reuse CBMC's signed/unsigned truncation implementation;
    // source instrumentation expresses any selected cast checks.
    return arith.cast_float_to_int(
      op, *dest_width, dest_type.id() == ID_signedbv);
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
