// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_BTOR2_FLOAT_H
#define CPROVER_GOTO_BTOR2_BTOR2_FLOAT_H

#include <util/arith_tools.h>

#include <solvers/floatbv/float_utils.h>

#include "btor2_prop.h"

/// CBMC float circuits with a functional division primitive. The div body
/// follows float_utilst::div. For a nonzero divisor the quotient/remainder
/// are unique; zero/Inf/NaN results are selected by CBMC's special-case logic.
/// No quotient/remainder variables, clauses, assumptions or bads are emitted.
class btor2_float_utilst final : public float_utilst
{
public:
  btor2_float_utilst(
    btor2_buildert &builder,
    btor2_propt &gates,
    const ieee_float_spect &format,
    btor2_nid_t mode = 0)
    : float_utilst(gates), builder(builder), gates(gates)
  {
    spec = format;
    if(mode)
      set_rounding_mode(gates.unpack(mode, 3));
    else
      rounding_mode_bits.set(ieee_floatt::ROUND_TO_EVEN);
  }

  bvt div(const bvt &src1, const bvt &src2) override
  {
    // unpack
    const unbiased_floatt unpacked1 = unpack(src1);
    const unbiased_floatt unpacked2 = unpack(src2);

    std::size_t div_width = unpacked1.fraction.size() * 2 + 1;

    // pad fraction1 with zeros
    bvt fraction1 = unpacked1.fraction;
    fraction1.reserve(div_width);
    while(fraction1.size() < div_width)
      fraction1.insert(fraction1.begin(), const_literal(false));

    // zero-extend fraction2
    const bvt fraction2 =
      bv_utils.zero_extension(unpacked2.fraction, div_width);

    // divide fractions
    unbiased_floatt result;
    bvt rem;
    const auto sort = builder.get_or_create_bitvec_sort(div_width);
    const auto numerator = gates.pack(fraction1);
    const auto denominator = gates.pack(fraction2);
    result.fraction =
      gates.unpack(builder.udiv(sort, numerator, denominator), div_width);
    rem = gates.unpack(builder.urem(sort, numerator, denominator), div_width);

    // is there a remainder?
    literalt have_remainder = bv_utils.is_not_zero(rem);

    // we throw this into the result, as one additional bit,
    // to get the right rounding decision
    result.fraction.insert(result.fraction.begin(), have_remainder);

    // We will subtract the exponents;
    // to account for overflow, we add a bit.
    // we add a second bit for the adjust by extra fraction bits
    const bvt exponent1 = bv_utils.sign_extension(
      unpacked1.exponent, unpacked1.exponent.size() + 2);
    const bvt exponent2 = bv_utils.sign_extension(
      unpacked2.exponent, unpacked2.exponent.size() + 2);

    // subtract exponents
    bvt added_exponent = bv_utils.sub(exponent1, exponent2);

    // adjust, as we have thown in extra fraction bits
    result.exponent = bv_utils.add(
      added_exponent, bv_utils.build_constant(spec.f, added_exponent.size()));

    // new sign
    result.sign = prop.lxor(unpacked1.sign, unpacked2.sign);

    // Infinity? This happens when
    // 1) dividing a non-nan/non-zero by zero, or
    // 2) first operand is inf and second is non-nan and non-zero
    // In particular, inf/0=inf.
    result.infinity = prop.lor(
      prop.land(!unpacked1.zero, prop.land(!unpacked1.NaN, unpacked2.zero)),
      prop.land(
        unpacked1.infinity, prop.land(!unpacked2.NaN, !unpacked2.zero)));

    // NaN?
    result.NaN = prop.lor(
      unpacked1.NaN,
      prop.lor(
        unpacked2.NaN,
        prop.lor(
          prop.land(unpacked1.zero, unpacked2.zero),
          prop.land(unpacked1.infinity, unpacked2.infinity))));

    // Division by infinity produces zero, unless we have NaN
    literalt force_zero = prop.land(!unpacked1.NaN, unpacked2.infinity);

    result.fraction = bv_utils.select(
      force_zero, bv_utils.zeros(result.fraction.size()), result.fraction);

    return round_and_pack(result);
  }

private:
  btor2_buildert &builder;
  btor2_propt &gates;
};
#endif
