#include "ieee754_arith.h"

// Both add and FMA align exact significands before their single rounding step.
// W is a power of two, with at least four bits below the input precision.
btor2_nid_t ieee754_aritht::sum_significands(
  btor2_nid_t sa, btor2_nid_t ea, btor2_nid_t a,
  btor2_nid_t sb, btor2_nid_t eb, btor2_nid_t rhs, std::size_t W) const
{
  const auto za = eq_w(a, zero(W), W), zb = eq_w(rhs, zero(W), W);
  const auto a_ge = lor(zb, land(lnot(za), lor(
    b.sgt(b.get_bool_sort(), ea, eb),
    land(eq_w(ea, eb, EW), lnot(ult_w(a, rhs, W))))));
  const auto sign = ite(a_ge, sa, sb, 1);
  const auto same_sign = eq_w(sa, sb, 1);
  const auto big_exp = ite(a_ge, ea, eb, EW);
  const auto small_exp = ite(a_ge, eb, ea, EW);
  const auto big = ite(a_ge, a, rhs, W);
  const auto aligned = shift_right_jam(
    ite(a_ge, rhs, a, W), uext_w(sub_w(big_exp, small_exp, EW), EW, W), W);
  const auto sum = add_w(uext_w(big, W, W + 1), uext_w(aligned, W, W + 1), W + 1);
  const auto carry = slice(sum, W, W);
  const auto sum_sig = ite(carry,
    slice(shift_right_jam(sum, one(W + 1), W + 1), W - 1, 0),
    slice(sum, W - 1, 0), W);
  const auto sum_exp = add_w(big_exp, uext_w(carry, 1, EW), EW);
  const auto diff = sub_w(big, aligned, W);
  std::size_t index_bits = 0;
  while((std::size_t(1) << index_bits) < W)
    ++index_bits;
  const auto left = sub_w(konst(W, W - 1), uext_w(msb_index(diff, W), index_bits, W), W);
  auto result = round_pack(sign,
    ite(same_sign, sum_exp, sub_w(big_exp, uext_w(left, W, EW), EW), EW),
    ite(same_sign, sum_sig, sll_w(diff, left, W), W), W);
  result = ite(land(lnot(same_sign), eq_w(diff, zero(W), W)),
    zero_value(rounding_is(1)), result, width);
  return ite(land(za, zb), zero_value(ite(same_sign, sa, rounding_is(1), 1)), result, width);
}

btor2_nid_t ieee754_aritht::sqrt(btor2_nid_t a) const
{
  const auto input = normalize(a);
  const auto unbiased = sub_w(input.exponent, konst(EW, bias), EW);
  const auto odd = slice(unbiased, 0, 0);
  const std::size_t W = P + 4, DW = 2 * W, RW = W + 2;
  // N = m * 2^odd * 2^(2*(W-1)); floor(sqrt(N)) has its leading
  // bit at W-1. The exact remainder supplies sticky evidence for rounding.
  const auto radicand = sll_w(uext_w(input.significand, P, DW),
    add_w(konst(DW, 2 * W - P - 1), uext_w(odd, 1, DW), DW), DW);
  auto root = zero(W), remainder = zero(RW);
  for(std::size_t i = W; i-- > 0;)
  {
    const auto incoming = b.lor(srt(RW), sll_w(remainder, konst(RW, 2), RW),
      uext_w(slice(radicand, 2 * i + 1, 2 * i), 2, RW));
    const auto trial = b.lor(srt(RW),
      sll_w(uext_w(root, W, RW), konst(RW, 2), RW), one(RW));
    const auto take = b.ugte(b.get_bool_sort(), incoming, trial);
    remainder = ite(take, sub_w(incoming, trial, RW), incoming, RW);
    root = b.lor(srt(W), sll_w(root, one(W), W), uext_w(take, 1, W));
  }
  const auto jammed = b.lor(srt(W), root,
    uext_w(lnot(eq_w(remainder, zero(RW), RW)), 1, W));
  const auto exponent = add_w(
    b.sra(srt(EW), unbiased, one(EW)), konst(EW, bias), EW);
  auto result = round_pack(zero(1), exponent, jammed, W);
  result = ite(is_inf(a), a, result, width);
  result = ite(sign_bit(a), nan_value(), result, width);
  result = ite(is_zero(a), a, result, width); // sqrt(-0) is -0.
  return ite(is_nan(a), nan_value(), result, width);
}

btor2_nid_t ieee754_aritht::fma(
  btor2_nid_t a, btor2_nid_t rhs, btor2_nid_t c) const
{
  const auto na = normalize(a), nb = normalize(rhs), nc = normalize(c);
  const auto product_sign = lxor_b(sign_bit(a), sign_bit(rhs));
  const auto product = b.mul(srt(2 * P),
    uext_w(na.significand, P, 2 * P), uext_w(nb.significand, P, 2 * P));
  const auto top = slice(product, 2 * P - 1, 2 * P - 1);
  const auto normalized_product = ite(top, product,
    sll_w(product, one(2 * P), 2 * P), 2 * P);
  const auto exponent = add_w(
    sub_w(add_w(na.exponent, nb.exponent, EW), konst(EW, bias), EW),
    uext_w(top, 1, EW), EW);
  const std::size_t W = width == 32 ? 64 : 128;
  // Retain the full 2P-bit product. Near cancellation, exponent alignment
  // loses no product bits; widely separated values retain guard/sticky bits.
  auto result = sum_significands(product_sign, exponent,
    sll_w(uext_w(normalized_product, 2 * P, W), konst(W, W - 2 * P), W),
    sign_bit(c), nc.exponent,
    sll_w(uext_w(nc.significand, P, W), konst(W, W - P), W), W);
  const auto product_inf = lor(is_inf(a), is_inf(rhs));
  const auto invalid_product = land(product_inf, lor(is_zero(a), is_zero(rhs)));
  result = ite(is_inf(c), c, result, width);
  result = ite(product_inf, inf_value(product_sign), result, width);
  const auto invalid_sum = land(land(product_inf, is_inf(c)),
    lnot(eq_w(product_sign, sign_bit(c), 1)));
  result = ite(lor(invalid_product, invalid_sum), nan_value(), result, width);
  return ite(lor(lor(is_nan(a), is_nan(rhs)), is_nan(c)), nan_value(), result, width);
}

btor2_nid_t ieee754_aritht::remainder(
  btor2_nid_t a, btor2_nid_t rhs, bool nearest) const
{
  const auto na = normalize(a), nb = normalize(rhs);
  const auto distance = sub_w(na.exponent, nb.exponent, EW);
  const std::size_t M = P + 1, DW = 2 * M;
  const auto divisor = uext_w(nb.significand, P, M);
  const auto modulus = sll_w(divisor, one(M), M);
  auto residue = uext_w(na.significand, P, M);
  auto factor = konst(M, 2);
  // For nonnegative exponent difference d, reduce A*2^d modulo 2B.
  // The extra factor of two retains quotient parity for ties-even. Modular
  // exponentiation needs EW stages rather than one stage per exponent value.
  auto modular_product = [&](btor2_nid_t x, btor2_nid_t y) {
    const auto product = b.mul(srt(DW), uext_w(x, M, DW), uext_w(y, M, DW));
    return slice(b.urem(srt(DW), product, uext_w(modulus, M, DW)), M - 1, 0);
  };
  for(std::size_t i = 0; i < EW; ++i)
  {
    residue = ite(slice(distance, i, i), modular_product(residue, factor), residue, M);
    if(i + 1 < EW)
      factor = modular_product(factor, factor);
  }
  const auto odd_quotient = b.ugte(b.get_bool_sort(), residue, divisor);
  const auto rem = ite(odd_quotient, sub_w(residue, divisor, M), residue, M);
  const auto twice = sll_w(rem, one(M), M);
  const auto adjust = nearest ? lor(
    b.ugt(b.get_bool_sort(), twice, divisor),
    land(eq_w(twice, divisor, M), odd_quotient)) : zero(1);
  auto magnitude = ite(adjust, sub_w(divisor, rem, M), rem, M);
  auto sign = lxor_b(sign_bit(a), adjust);
  auto exponent = nb.exponent;
  const auto negative_distance = b.slt(b.get_bool_sort(), distance, zero(EW));
  // If |a/b|<1, only the interval (1/2,1) changes IEEE remainder.
  // Exactly 1/2 keeps quotient zero (even). fmod always returns a here.
  const auto small_adjust = nearest ? land(eq_w(distance, konst(EW, -1), EW),
    b.ugt(b.get_bool_sort(), na.significand, nb.significand)) : zero(1);
  magnitude = ite(negative_distance,
    sub_w(sll_w(divisor, one(M), M), uext_w(na.significand, P, M), M), magnitude, M);
  sign = ite(negative_distance, lnot(sign_bit(a)), sign, 1);
  exponent = ite(negative_distance, na.exponent, exponent, EW);
  std::size_t W = 1, index_bits = 0;
  while(W < M) { W *= 2; ++index_bits; }
  const auto left = sub_w(konst(W, P - 1),
    uext_w(msb_index(uext_w(magnitude, M, W), W), index_bits, W), W);
  auto result = round_pack(sign, sub_w(exponent, uext_w(left, W, EW), EW),
    sll_w(uext_w(magnitude, M, W), add_w(left, konst(W, W - P), W), W), W);
  result = ite(eq_w(magnitude, zero(M), M), zero_value(sign_bit(a)), result, width);
  result = ite(land(negative_distance, lnot(small_adjust)), a, result, width);
  result = ite(lor(is_inf(rhs), is_zero(a)), a, result, width);
  return ite(lor(lor(is_nan(a), is_nan(rhs)), lor(is_inf(a), is_zero(rhs))),
             nan_value(), result, width);
}
