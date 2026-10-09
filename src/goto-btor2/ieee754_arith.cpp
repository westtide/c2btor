#include "ieee754_arith.h"

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
  const auto right = subtract ? neg(b2) : b2;
  const auto na = normalize(a), nb = normalize(right);
  const auto same_sign = eq_w(sign_bit(a), sign_bit(right), 1);
  const std::size_t W = pow2_at_least(P + 4);
  auto result = sum_significands(
    sign_bit(a), na.exponent,
    sll_w(uext_w(na.significand, P, W), konst(W, W - P), W),
    sign_bit(right), nb.exponent,
    sll_w(uext_w(nb.significand, P, W), konst(W, W - P), W), W);
  result = ite(is_zero(right), a, result, width);
  result = ite(is_zero(a), right, result, width);
  result = ite(
    land(is_zero(a), is_zero(right)),
    zero_value(ite(same_sign, sign_bit(a), rounding_is(1), 1)),
    result,
    width);
  result = ite(is_inf(right), right, result, width);
  result = ite(is_inf(a), a, result, width);
  result = ite(
    land(land(is_inf(a), is_inf(right)), lnot(same_sign)),
    nan_value(),
    result,
    width);
  return ite(lor(is_nan(a), is_nan(right)), nan_value(), result, width);
}

btor2_nid_t ieee754_aritht::mul(btor2_nid_t a, btor2_nid_t b2) const
{
  const auto na = normalize(a), nb = normalize(b2);
  const auto sign = lxor_b(sign_bit(a), sign_bit(b2));
  const auto prod = b.mul(
    srt(2 * P),
    uext_w(na.significand, P, 2 * P),
    uext_w(nb.significand, P, 2 * P));
  const auto top = slice(prod, 2 * P - 1, 2 * P - 1);
  const auto aligned = ite(top, prod, sll_w(prod, one(2 * P), 2 * P), 2 * P);
  const auto exponent = add_w(
    sub_w(add_w(na.exponent, nb.exponent, EW), konst(EW, bias), EW),
    uext_w(top, 1, EW),
    EW);
  auto result = round_pack(sign, exponent, aligned, 2 * P);
  const auto any_zero = lor(is_zero(a), is_zero(b2));
  const auto any_inf = lor(is_inf(a), is_inf(b2));
  result = ite(any_zero, zero_value(sign), result, width);
  result = ite(any_inf, inf_value(sign), result, width);
  result = ite(land(any_inf, any_zero), nan_value(), result, width);
  return ite(lor(is_nan(a), is_nan(b2)), nan_value(), result, width);
}

btor2_nid_t ieee754_aritht::div(btor2_nid_t a, btor2_nid_t b2) const
{
  const auto na = normalize(a), nb = normalize(b2);
  const auto sign = lxor_b(sign_bit(a), sign_bit(b2));
  const std::size_t W = P + 4, DW = 2 * P + 4;
  const auto num = sll_w(uext_w(na.significand, P, DW), konst(DW, P + 3), DW);
  const auto den = uext_w(nb.significand, P, DW);
  const auto quot = slice(b.udiv(srt(DW), num, den), W - 1, 0);
  const auto rem = b.urem(srt(DW), num, den);
  const auto hi = slice(quot, W - 1, W - 1);
  // Keep several quotient bits below precision. Jam the remainder after
  // normalization so a ratio below one retains its guard and sticky bits.
  const auto aligned = ite(hi, quot, sll_w(quot, one(W), W), W);
  const auto jammed =
    b.lor(srt(W), aligned, uext_w(lnot(eq_w(rem, zero(DW), DW)), 1, W));
  const auto exponent = sub_w(
    add_w(sub_w(na.exponent, nb.exponent, EW), konst(EW, bias), EW),
    uext_w(lnot(hi), 1, EW),
    EW);
  auto result = round_pack(sign, exponent, jammed, W);
  result = ite(is_zero(a), zero_value(sign), result, width);
  result = ite(is_inf(b2), zero_value(sign), result, width);
  result = ite(is_zero(b2), inf_value(sign), result, width);
  result = ite(is_inf(a), inf_value(sign), result, width);
  const auto invalid =
    lor(land(is_zero(a), is_zero(b2)), land(is_inf(a), is_inf(b2)));
  result = ite(invalid, nan_value(), result, width);
  return ite(lor(is_nan(a), is_nan(b2)), nan_value(), result, width);
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
  const auto sign =
    src_signed ? slice(src, src_width - 1, src_width - 1) : zero(1);
  const auto magnitude =
    src_signed
      ? ite(sign, sub_w(zero(src_width), src, src_width), src, src_width)
      : src;
  const std::size_t W = pow2_at_least(std::max(src_width, P + 3));
  const auto wide = uext_w(magnitude, src_width, W);
  const auto index = msb_index(wide, W);
  const auto left = sub_w(konst(W, W - 1), uext_w(index, log2_of(W), W), W);
  const auto exponent =
    add_w(uext_w(index, log2_of(W), EW), konst(EW, bias), EW);
  return ite(
    eq_w(magnitude, zero(src_width), src_width),
    zero_value(zero(1)),
    round_pack(sign, exponent, sll_w(wide, left, W), W),
    width);
}

btor2_nid_t
ieee754_aritht::cast_float_to_int(btor2_nid_t src, std::size_t dest_width) const
{
  const auto exponent = sub_w(
    ite(
      eq_w(exp_field(src), zero(E), E),
      one(EW),
      uext_w(exp_field(src), E, EW),
      EW),
    konst(EW, bias),
    EW);
  const auto left = b.sgte(b.get_bool_sort(), exponent, konst(EW, P - 1));
  const auto distance = ite(
    left,
    sub_w(exponent, konst(EW, P - 1), EW),
    sub_w(konst(EW, P - 1), exponent, EW),
    EW);
  const std::size_t W = pow2_at_least(std::max(P, dest_width) + 1);
  const auto sig = uext_w(sig_with_hidden(src), P, W);
  const auto magnitude = ite(
    left,
    sll_w(sig, uext_w(distance, EW, W), W),
    srl_w(sig, uext_w(distance, EW, W), W),
    W);
  const auto truncated = slice(magnitude, dest_width - 1, 0);
  const auto result = ite(
    sign_bit(src),
    sub_w(zero(dest_width), truncated, dest_width),
    truncated,
    dest_width);
  return ite(
    b.slt(b.get_bool_sort(), exponent, zero(EW)),
    zero(dest_width),
    result,
    dest_width);
}

btor2_nid_t ieee754_aritht::float_to_int_valid(
  btor2_nid_t src,
  std::size_t dest_width,
  bool dest_signed) const
{
  const auto exponent =
    sub_w(uext_w(exp_field(src), E, EW), konst(EW, bias), EW);
  const auto small = b.slt(b.get_bool_sort(), exponent, zero(EW));
  const auto sign = sign_bit(src);
  btor2_nid_t range;
  if(dest_signed)
  {
    const auto bound = konst(EW, dest_width - 1);
    // Negative values whose fractional part truncates to INT_MIN are valid;
    // exponent alone would incorrectly exclude that narrow interval.
    const auto at_min = land(
      eq_w(exponent, bound, EW),
      eq_w(
        cast_float_to_int(src, dest_width),
        konst(dest_width, power(2, dest_width - 1)),
        dest_width));
    range = lor(b.slt(b.get_bool_sort(), exponent, bound), land(sign, at_min));
  }
  else
  {
    range = ite(
      sign,
      small,
      b.slt(b.get_bool_sort(), exponent, konst(EW, dest_width)),
      1);
  }
  return land(lnot(lor(is_nan(src), is_inf(src))), range);
}

btor2_nid_t ieee754_aritht::cast_float_to_float(
  btor2_nid_t src,
  std::size_t src_width) const
{
  ieee754_aritht source(b, src_width);
  const auto normalized = source.normalize(src);
  const auto exponent =
    bias >= source.bias
      ? add_w(normalized.exponent, konst(EW, bias - source.bias), EW)
      : sub_w(normalized.exponent, konst(EW, source.bias - bias), EW);
  const std::size_t W = pow2_at_least(std::max(source.P, P + 3));
  const auto aligned = sll_w(
    uext_w(normalized.significand, source.P, W), konst(W, W - source.P), W);
  const auto sign = source.sign_bit(src);
  auto result = round_pack(sign, exponent, aligned, W);
  result = ite(source.is_zero(src), zero_value(sign), result, width);
  result = ite(source.is_inf(src), inf_value(sign), result, width);
  return ite(source.is_nan(src), nan_value(), result, width);
}
