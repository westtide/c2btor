#ifndef C2BTOR_IEEE754_ARITH_H
#define C2BTOR_IEEE754_ARITH_H

#include <util/mp_arith.h>

#include "btor2_builder.h"

#include <map>

// Self-contained IEEE-754 circuits for BTOR2 lowering of C floating-point
// arithmetic. Strategy: decode the IEEE layout (sign, biased exponent,
// fraction), compute on extended fixed-point significands, apply a single
// rounding step in the requested mode, and keep NaN/Inf/zero branches explicit.
// The circuits use no free bits and no global assumptions, so the model
// semantics is exactly the gate-level circuit.
//
// Binary32/binary64 include subnormal inputs and gradual underflow. Arithmetic
// and conversions to floating-point support all five CBMC IEEE rounding modes;
// integral casts truncate toward zero. The caller checks mode/domain validity.
class ieee754_aritht
{
public:
  // mode is a 3-bit CBMC rounding-mode value (0..4); zero node means RNE.
  ieee754_aritht(
    btor2_buildert &builder, std::size_t total_width, btor2_nid_t mode = 0);

  btor2_nid_t add(btor2_nid_t a, btor2_nid_t b, bool subtract) const;
  btor2_nid_t mul(btor2_nid_t a, btor2_nid_t b) const;
  btor2_nid_t div(btor2_nid_t a, btor2_nid_t b) const;
  btor2_nid_t sqrt(btor2_nid_t a) const;
  btor2_nid_t fma(btor2_nid_t a, btor2_nid_t b, btor2_nid_t c) const;
  // nearest=true implements IEEE remainder (ties-even quotient); false is
  // fmod (truncated quotient). Both produce an exact, mode-independent result.
  btor2_nid_t remainder(btor2_nid_t a, btor2_nid_t b, bool nearest) const;
  btor2_nid_t neg(btor2_nid_t a) const;

  // rel: EQ=0, LT=1, LE=2, GT=3, GE=4
  btor2_nid_t relation(btor2_nid_t a, btor2_nid_t b, unsigned rel) const;

  btor2_nid_t cast_int_to_float(
    btor2_nid_t src,
    std::size_t src_width,
    bool src_signed) const;
  btor2_nid_t cast_float_to_int(btor2_nid_t src, std::size_t dest_width) const;
  // Whether the truncated finite value is representable in the C destination.
  btor2_nid_t float_to_int_valid(
    btor2_nid_t src,
    std::size_t dest_width,
    bool dest_signed) const;
  btor2_nid_t cast_float_to_float(btor2_nid_t src, std::size_t src_width) const;

  // classification and simple rewrites
  btor2_nid_t is_nan_node(btor2_nid_t v) const
  {
    return is_nan(v);
  }
  btor2_nid_t is_inf_node(btor2_nid_t v) const
  {
    return is_inf(v);
  }
  btor2_nid_t is_zero_node(btor2_nid_t v) const
  {
    return is_zero(v);
  }
  btor2_nid_t is_normal_node(btor2_nid_t v) const;
  btor2_nid_t abs_value(btor2_nid_t v) const;

private:
  btor2_buildert &b;
  std::size_t width; // total encoding width (32/64)
  std::size_t P;     // significand width incl. hidden bit (24/53)
  std::size_t E;     // exponent field width (8/11)
  std::size_t EW;    // signed work width shared by both supported formats
  mp_integer bias;
  btor2_nid_t mode;

  mutable std::map<std::size_t, btor2_nid_t> sorts;

  btor2_nid_t srt(std::size_t w) const;
  btor2_nid_t zero(std::size_t w) const;
  btor2_nid_t one(std::size_t w) const;
  btor2_nid_t ones(std::size_t w) const;
  btor2_nid_t konst(std::size_t w, mp_integer v) const;
  btor2_nid_t slice(btor2_nid_t a, std::size_t hi, std::size_t lo) const;
  btor2_nid_t cat(btor2_nid_t hi, btor2_nid_t lo, std::size_t total_w) const;
  btor2_nid_t
  ite(btor2_nid_t c, btor2_nid_t t, btor2_nid_t f, std::size_t w) const;
  btor2_nid_t land(btor2_nid_t a, btor2_nid_t b) const;
  btor2_nid_t lor(btor2_nid_t a, btor2_nid_t b) const;
  btor2_nid_t lnot(btor2_nid_t a) const;
  btor2_nid_t lxor_b(btor2_nid_t a, btor2_nid_t b) const;
  btor2_nid_t eq_w(btor2_nid_t a, btor2_nid_t b, std::size_t w) const;
  btor2_nid_t ult_w(btor2_nid_t a, btor2_nid_t b, std::size_t w) const;
  btor2_nid_t uext_w(btor2_nid_t a, std::size_t from, std::size_t to) const;
  btor2_nid_t add_w(btor2_nid_t a, btor2_nid_t b, std::size_t w) const;
  btor2_nid_t sub_w(btor2_nid_t a, btor2_nid_t b, std::size_t w) const;
  btor2_nid_t sll_w(btor2_nid_t a, btor2_nid_t sh, std::size_t w) const;
  btor2_nid_t srl_w(btor2_nid_t a, btor2_nid_t sh, std::size_t w) const;

  btor2_nid_t sign_bit(btor2_nid_t v) const;
  btor2_nid_t exp_field(btor2_nid_t v) const;
  btor2_nid_t frac_field(btor2_nid_t v) const;
  btor2_nid_t sig_with_hidden(btor2_nid_t v) const; // {exp != 0, frac}
  struct normalizedt
  {
    btor2_nid_t exponent;    // signed, biased exponent; may be non-positive
    btor2_nid_t significand; // P bits, leading bit set unless the value is zero
  };
  normalizedt normalize(btor2_nid_t v) const;
  btor2_nid_t encode(btor2_nid_t sign, btor2_nid_t exp, btor2_nid_t frac) const;

  btor2_nid_t is_nan(btor2_nid_t v) const;
  btor2_nid_t is_inf(btor2_nid_t v) const;
  btor2_nid_t is_zero(btor2_nid_t v) const;

  btor2_nid_t nan_value() const;
  btor2_nid_t inf_value(btor2_nid_t sign) const;
  btor2_nid_t zero_value(btor2_nid_t sign) const;

  // Jam shifted-out nonzero bits into the low bit, preserving sticky evidence.
  btor2_nid_t
  shift_right_jam(btor2_nid_t value, btor2_nid_t distance, std::size_t W) const;

  // Shift into the subnormal range before rounding, so precision narrowing
  // and gradual underflow share one rounding step. The significand is aligned
  // to bit W-1; overflow follows the selected mode, underflow keeps the sign.
  btor2_nid_t round_pack(
    btor2_nid_t sign,
    btor2_nid_t exp_ew,
    btor2_nid_t significand,
    std::size_t W) const;

  // sig is W bits with the P-bit significand at the
  // top and guard/sticky bits below. Exact when W <= P. Carry (needing an
  // exponent increment) is returned via delta.
  btor2_nid_t round_significand(
    btor2_nid_t sign, btor2_nid_t sig, std::size_t W, btor2_nid_t &delta) const;
  btor2_nid_t rounding_is(unsigned value) const;
  btor2_nid_t sum_significands(
    btor2_nid_t sa, btor2_nid_t ea, btor2_nid_t a,
    btor2_nid_t sb, btor2_nid_t eb, btor2_nid_t rhs, std::size_t W) const;

  // index (0-based bit position) of the most significant 1; W must be a
  // power of two and v must be non-zero.
  btor2_nid_t msb_index(btor2_nid_t v, std::size_t W) const;
};

#endif
