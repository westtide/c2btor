// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "ieee754_arith.h"
#include "btor2_float.h"

#include <solvers/floatbv/float_utils.h>
#include <util/arith_tools.h>

#include <algorithm>

namespace
{
std::size_t pow2_at_least(std::size_t w)
{
  std::size_t result = 1;
  while(result < w)
    result <<= 1;
  return result;
}

std::size_t log2_of(std::size_t w)
{
  std::size_t result = 0;
  while((std::size_t(1) << result) < w)
    ++result;
  return result;
}
} // namespace

ieee754_aritht::ieee754_aritht(
  btor2_buildert &builder, std::size_t total_width, btor2_nid_t rounding)
  : b(builder), width(total_width), mode(rounding)
{
  PRECONDITION(width == 32 || width == 64);
  P = width == 32 ? 24 : 53;
  E = width == 32 ? 8 : 11;
  // Both formats share enough signed exponent bits for cross-format rebiasing
  // and the extreme exponents produced by multiplication/division.
  EW = 11 + 2;
  bias = power(2, E - 1) - 1;
}

btor2_nid_t ieee754_aritht::srt(std::size_t w) const
{
  const auto found = sorts.find(w);
  if(found != sorts.end())
    return found->second;
  const btor2_nid_t nid = b.get_or_create_bitvec_sort(w);
  sorts.emplace(w, nid);
  return nid;
}

btor2_nid_t ieee754_aritht::zero(std::size_t w) const
{
  return b.zero(srt(w));
}

btor2_nid_t ieee754_aritht::one(std::size_t w) const
{
  return b.one(srt(w));
}

btor2_nid_t ieee754_aritht::ones(std::size_t w) const
{
  return b.ones(srt(w));
}

btor2_nid_t ieee754_aritht::konst(std::size_t w, mp_integer v) const
{
  return b.constd(srt(w), v);
}

btor2_nid_t
ieee754_aritht::slice(btor2_nid_t a, std::size_t hi, std::size_t lo) const
{
  return b.slice(srt(hi - lo + 1), a, hi, lo);
}

btor2_nid_t
ieee754_aritht::cat(btor2_nid_t hi, btor2_nid_t lo, std::size_t total_w) const
{
  // the BTOR2 concat sort describes the whole result width
  return b.concat(srt(total_w), hi, lo);
}

btor2_nid_t
ieee754_aritht::ite(btor2_nid_t c, btor2_nid_t t, btor2_nid_t f, std::size_t w)
  const
{
  return b.ite(srt(w), c, t, f);
}

btor2_nid_t ieee754_aritht::land(btor2_nid_t a, btor2_nid_t b2) const
{
  return b.land(b.get_bool_sort(), a, b2);
}

btor2_nid_t ieee754_aritht::lor(btor2_nid_t a, btor2_nid_t b2) const
{
  return b.lor(b.get_bool_sort(), a, b2);
}

btor2_nid_t ieee754_aritht::lnot(btor2_nid_t a) const
{
  return b.lnot(b.get_bool_sort(), a);
}

btor2_nid_t ieee754_aritht::lxor_b(btor2_nid_t a, btor2_nid_t b2) const
{
  return b.lxor(b.get_bool_sort(), a, b2);
}

btor2_nid_t
ieee754_aritht::eq_w(btor2_nid_t a, btor2_nid_t b2, std::size_t w) const
{
  // comparison nodes take the boolean sort; w only documents the operands
  (void)w;
  return b.eq(b.get_bool_sort(), a, b2);
}

btor2_nid_t
ieee754_aritht::ult_w(btor2_nid_t a, btor2_nid_t b2, std::size_t w) const
{
  (void)w;
  return b.ult(b.get_bool_sort(), a, b2);
}

btor2_nid_t
ieee754_aritht::uext_w(btor2_nid_t a, std::size_t from, std::size_t to) const
{
  if(from == to)
    return a;
  if(from > to)
    return b.slice(srt(to), a, to - 1, 0);
  return b.uext(srt(to), a, to - from);
}

btor2_nid_t
ieee754_aritht::add_w(btor2_nid_t a, btor2_nid_t b2, std::size_t w) const
{
  return b.add(srt(w), a, b2);
}

btor2_nid_t
ieee754_aritht::sub_w(btor2_nid_t a, btor2_nid_t b2, std::size_t w) const
{
  return b.sub(srt(w), a, b2);
}

btor2_nid_t
ieee754_aritht::sll_w(btor2_nid_t a, btor2_nid_t sh, std::size_t w) const
{
  return b.sll(srt(w), a, sh);
}

btor2_nid_t
ieee754_aritht::srl_w(btor2_nid_t a, btor2_nid_t sh, std::size_t w) const
{
  return b.srl(srt(w), a, sh);
}

btor2_nid_t ieee754_aritht::sign_bit(btor2_nid_t v) const
{
  return slice(v, width - 1, width - 1);
}

btor2_nid_t ieee754_aritht::exp_field(btor2_nid_t v) const
{
  return slice(v, width - 2, width - 1 - E);
}

btor2_nid_t ieee754_aritht::frac_field(btor2_nid_t v) const
{
  return slice(v, P - 2, 0);
}

btor2_nid_t ieee754_aritht::sig_with_hidden(btor2_nid_t v) const
{
  return cat(lnot(eq_w(exp_field(v), zero(E), E)), frac_field(v), P);
}

ieee754_aritht::normalizedt ieee754_aritht::normalize(btor2_nid_t v) const
{
  // Subnormals have effective biased exponent 1 and no hidden bit. Moving
  // their leading one to bit P-1 lowers the exponent by the same distance.
  const std::size_t W = pow2_at_least(P);
  const auto sig = sig_with_hidden(v);
  const auto index = msb_index(uext_w(sig, P, W), W);
  const auto distance =
    sub_w(konst(EW, P - 1), uext_w(index, log2_of(W), EW), EW);
  const auto exponent = ite(
    eq_w(exp_field(v), zero(E), E), one(EW), uext_w(exp_field(v), E, EW), EW);
  return {
    sub_w(exponent, distance, EW), sll_w(sig, uext_w(distance, EW, P), P)};
}

btor2_nid_t ieee754_aritht::encode(
  btor2_nid_t sign,
  btor2_nid_t exp,
  btor2_nid_t frac) const
{
  return cat(cat(sign, exp, 1 + E), frac, width);
}

btor2_nid_t ieee754_aritht::is_nan(btor2_nid_t v) const
{
  return land(
    eq_w(exp_field(v), konst(E, power(2, E) - 1), E),
    lnot(eq_w(frac_field(v), zero(P - 1), P - 1)));
}

btor2_nid_t ieee754_aritht::is_inf(btor2_nid_t v) const
{
  return land(
    eq_w(exp_field(v), konst(E, power(2, E) - 1), E),
    eq_w(frac_field(v), zero(P - 1), P - 1));
}

btor2_nid_t ieee754_aritht::is_zero(btor2_nid_t v) const
{
  return eq_w(slice(v, width - 2, 0), zero(width - 1), width - 1);
}

btor2_nid_t ieee754_aritht::nan_value() const
{
  return encode(one(1), ones(E), cat(one(1), zero(P - 2), P - 1));
}

btor2_nid_t ieee754_aritht::inf_value(btor2_nid_t sign) const
{
  return encode(sign, ones(E), zero(P - 1));
}

btor2_nid_t ieee754_aritht::zero_value(btor2_nid_t sign) const
{
  return encode(sign, zero(E), zero(P - 1));
}

btor2_nid_t ieee754_aritht::shift_right_jam(
  btor2_nid_t value,
  btor2_nid_t distance,
  std::size_t W) const
{
  const auto shifted = srl_w(value, distance, W);
  const auto lost = lnot(eq_w(sll_w(shifted, distance, W), value, W));
  return b.lor(srt(W), shifted, uext_w(lost, 1, W));
}

btor2_nid_t ieee754_aritht::round_pack(
  btor2_nid_t sign,
  btor2_nid_t exp_ew,
  btor2_nid_t significand,
  std::size_t W) const
{
  const auto under = b.slt(b.get_bool_sort(), exp_ew, one(EW));
  const auto distance = ite(under, sub_w(one(EW), exp_ew, EW), zero(EW), EW);
  const auto shifted = shift_right_jam(significand, uext_w(distance, EW, W), W);
  btor2_nid_t carry;
  const auto sig = round_significand(sign, shifted, W, carry);
  const auto exponent = add_w(exp_ew, uext_w(carry, 1, EW), EW);
  // A rounded subnormal can become the smallest normal; its leading bit
  // selects exponent 0 or 1 without a second rounding operation.
  const auto encoded_exp = ite(
    under,
    uext_w(slice(sig, P - 1, P - 1), 1, E),
    slice(exponent, E - 1, 0),
    E);
  const auto over = land(lnot(under), ult_w(konst(EW, 2 * bias), exponent, EW));
  return ite(
    over,
    ite(
      lor(
        lor(rounding_is(0), rounding_is(4)),
        lor(land(rounding_is(1), sign), land(rounding_is(2), lnot(sign)))),
      inf_value(sign),
      encode(sign, konst(E, 2 * bias), ones(P - 1)),
      width),
    encode(sign, encoded_exp, slice(sig, P - 2, 0)),
    width);
}

btor2_nid_t ieee754_aritht::msb_index(btor2_nid_t v, std::size_t W) const
{
  // Largest s with (v >> s) != 0 equals the MSB position. W is a power of
  // two and v is known non-zero.
  const std::size_t lw = log2_of(W);
  btor2_nid_t base = zero(lw);
  for(std::size_t step = W / 2; step >= 1; step /= 2)
  {
    const btor2_nid_t sh = uext_w(add_w(base, konst(lw, step), lw), lw, W);
    const btor2_nid_t shifted = srl_w(v, sh, W);
    const btor2_nid_t nonzero = lnot(eq_w(shifted, zero(W), W));
    base = ite(nonzero, add_w(base, konst(lw, step), lw), base, lw);
  }
  return base;
}

btor2_nid_t ieee754_aritht::rounding_is(unsigned value) const
{
  return mode ? eq_w(mode, konst(3, value), 3)
              : (value == 0 ? one(1) : zero(1));
}

btor2_nid_t ieee754_aritht::round_significand(
  btor2_nid_t sign,
  btor2_nid_t sig,
  std::size_t W,
  btor2_nid_t &delta) const
{
  if(W <= P)
  {
    delta = zero(1);
    return uext_w(sig, W, P);
  }
  const btor2_nid_t guard = slice(sig, W - P - 1, W - P - 1);
  const btor2_nid_t lsb = slice(sig, W - P, W - P);
  const btor2_nid_t sticky =
    W - P - 1 >= 1
      ? lnot(eq_w(slice(sig, W - P - 2, 0), zero(W - P - 1), W - P - 1))
      : zero(1);
  const auto inexact = lor(guard, sticky);
  const auto directed =
    lor(land(rounding_is(1), sign), land(rounding_is(2), lnot(sign)));
  const btor2_nid_t round_up = lor(
    lor(land(rounding_is(0), land(guard, lor(sticky, lsb))),
        land(rounding_is(4), guard)),
    land(directed, inexact));
  const btor2_nid_t kept = slice(sig, W - 1, W - P);
  const btor2_nid_t sum =
    add_w(uext_w(kept, P, P + 1), cat(zero(P), round_up, P + 1), P + 1);
  const btor2_nid_t carry = slice(sum, P, P);
  const btor2_nid_t result = slice(sum, P - 1, 0);
  delta = carry;
  // on carry the significand grew to 2^P; shift right one, bringing the
  // carry bit in at the top
  return ite(carry, cat(one(1), slice(result, P - 2, 0), P), result, P);
}

btor2_nid_t
ieee754_aritht::add(btor2_nid_t a, btor2_nid_t b2, bool subtract) const
{
  null_message_handlert handler;
  btor2_propt gates(b, handler);
  btor2_float_utilst floats(b, gates, ieee_float_spect(P - 1, E), mode);
  return gates.pack(floats.add_sub(
    gates.unpack(a, width), gates.unpack(b2, width), subtract));
}

btor2_nid_t ieee754_aritht::mul(btor2_nid_t a, btor2_nid_t b2) const
{
  null_message_handlert handler;
  btor2_propt gates(b, handler);
  btor2_float_utilst floats(b, gates, ieee_float_spect(P - 1, E), mode);
  return gates.pack(floats.mul(gates.unpack(a, width), gates.unpack(b2, width)));
}

btor2_nid_t ieee754_aritht::div(btor2_nid_t a, btor2_nid_t b2) const
{
  null_message_handlert handler;
  btor2_propt gates(b, handler);
  btor2_float_utilst floats(b, gates, ieee_float_spect(P - 1, E), mode);
  return gates.pack(floats.div(gates.unpack(a, width), gates.unpack(b2, width)));
}

btor2_nid_t ieee754_aritht::is_normal_node(btor2_nid_t v) const
{
  return land(
    lnot(eq_w(exp_field(v), zero(E), E)),
    lnot(eq_w(exp_field(v), konst(E, power(2, E) - 1), E)));
}

btor2_nid_t ieee754_aritht::abs_value(btor2_nid_t v) const
{
  return cat(zero(1), slice(v, width - 2, 0), width);
}

btor2_nid_t ieee754_aritht::neg(btor2_nid_t a) const
{
  return cat(lnot(sign_bit(a)), slice(a, width - 2, 0), width);
}

btor2_nid_t
ieee754_aritht::relation(btor2_nid_t a, btor2_nid_t b2, unsigned rel) const
{
  const btor2_nid_t nan = lor(is_nan(a), is_nan(b2));
  const btor2_nid_t s_a = sign_bit(a), s_b = sign_bit(b2);
  const btor2_nid_t zero_a = is_zero(a), zero_b = is_zero(b2);
  const btor2_nid_t mag_a = cat(exp_field(a), frac_field(a), width - 1);
  const btor2_nid_t mag_b = cat(exp_field(b2), frac_field(b2), width - 1);
  const btor2_nid_t both_zero = land(zero_a, zero_b);
  const btor2_nid_t same_sign = lnot(lxor_b(s_a, s_b));
  const btor2_nid_t mag_eq = land(same_sign, eq_w(mag_a, mag_b, E + P - 1));
  // for equal signs: a < b iff |a| < |b| when positive, |a| > |b| when
  // negative
  const btor2_nid_t lt_same = land(
    same_sign,
    ite(
      s_a, ult_w(mag_b, mag_a, E + P - 1), ult_w(mag_a, mag_b, E + P - 1), 1));
  const btor2_nid_t gt_same = land(
    same_sign,
    ite(
      s_a, ult_w(mag_a, mag_b, E + P - 1), ult_w(mag_b, mag_a, E + P - 1), 1));
  const btor2_nid_t lt_cross = land(s_a, lnot(s_b));
  const btor2_nid_t gt_cross = land(lnot(s_a), s_b);
  const btor2_nid_t lt =
    ite(both_zero, zero(1), ite(same_sign, lt_same, lt_cross, 1), 1);
  const btor2_nid_t gt =
    ite(both_zero, zero(1), ite(same_sign, gt_same, gt_cross, 1), 1);
  const btor2_nid_t eq_res = lor(both_zero, mag_eq);

  btor2_nid_t res = zero(1);
  switch(rel)
  {
  case 0:
    res = eq_res;
    break;
  case 1:
    res = lt;
    break;
  case 2:
    res = lor(lt, eq_res);
    break;
  case 3:
    res = gt;
    break;
  default:
    res = lor(gt, eq_res);
    break;
  }
  return ite(nan, zero(1), res, 1);
}

btor2_nid_t ieee754_aritht::cast_int_to_float(
  btor2_nid_t src,
  std::size_t src_width,
  bool src_signed) const
{
  null_message_handlert handler;
  btor2_propt gates(b, handler);
  btor2_float_utilst floats(b, gates, ieee_float_spect(P - 1, E), mode);
  const auto input = gates.unpack(src, src_width);
  return gates.pack(src_signed ? floats.from_signed_integer(input)
                               : floats.from_unsigned_integer(input));
}

btor2_nid_t
ieee754_aritht::cast_float_to_int(
  btor2_nid_t src, std::size_t dest_width, bool dest_signed) const
{
  // Reuse the SAT backend's actual conversion, including its signedness
  // handling. The adapter maps gates to BTOR2 expressions without SAT calls,
  // fresh result bits, constraints, or auxiliary properties.
  null_message_handlert handler;
  btor2_propt gates(b, handler);
  float_utilst floats(gates);
  floats.spec = ieee_float_spect(P - 1, E);
  floats.rounding_mode_bits.set(ieee_floatt::ROUND_TO_ZERO);
  return gates.pack(
    floats.to_integer(gates.unpack(src, width), dest_width, dest_signed));
}

btor2_nid_t ieee754_aritht::cast_float_to_float(
  btor2_nid_t src,
  std::size_t src_width) const
{
  ieee754_aritht source(b, src_width);
  null_message_handlert handler;
  btor2_propt gates(b, handler);
  btor2_float_utilst floats(b, gates, ieee_float_spect(source.P - 1, source.E), mode);
  return gates.pack(floats.conversion(gates.unpack(src, src_width),
                                      ieee_float_spect(P - 1, E)));
}

btor2_nid_t ieee754_aritht::round_to_integral(btor2_nid_t src) const
{
  null_message_handlert handler;
  btor2_propt gates(b, handler);
  btor2_float_utilst floats(b, gates, ieee_float_spect(P - 1, E), mode);
  return gates.pack(floats.round_to_integral(gates.unpack(src, width)));
}
