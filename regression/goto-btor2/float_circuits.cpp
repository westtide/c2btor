// Numerical oracle for the production IEEE circuits. Native operations are
// evaluated in each native rounding mode without contraction; RNA uses CBMC
// value arithmetic. BTOR2 is evaluated independently by BtorSim.
#include <goto-btor2/ieee754_arith.h>
#include <util/ieee_float.h>
#include <util/arith_tools.h>

#include <cfenv>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <limits>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

struct caset
{
  std::string op;
  unsigned source, destination;
  bool is_signed;
  uint64_t a, b, expected;
  uint64_t c = 0;
  unsigned mode = 0;
};

template <typename T>
T from_bits(uint64_t bits)
{
  T value;
  std::memcpy(&value, &bits, sizeof(value));
  return value;
}

template <typename T>
uint64_t to_bits(T value)
{
  uint64_t bits = 0;
  std::memcpy(&bits, &value, sizeof(value));
  return bits;
}

template <typename T>
void floating_cases(std::vector<caset> &cases, std::mt19937_64 &random)
{
  static_assert(std::numeric_limits<T>::is_iec559, "IEEE oracle required");
  const unsigned W = sizeof(T) * 8;
  const unsigned F = std::numeric_limits<T>::digits - 1;
  const unsigned E = W - F - 1;
  const uint64_t sign = uint64_t(1) << (W - 1);
  const uint64_t inf = ((uint64_t(1) << E) - 1) << F;
  const uint64_t unit = uint64_t(std::numeric_limits<T>::max_exponent - 1) << F;
  const std::vector<uint64_t> corners = {
    0,
    sign,
    1,
    sign | 1,
    (uint64_t(1) << F) - 1,
    uint64_t(1) << F,
    (uint64_t(1) << F) + 1,
    unit,
    unit - 1,
    unit + 1,
    unit | (uint64_t(1) << (F - 1)),
    sign | unit,
    sign | (unit + 1),
    inf - 1,
    sign | (inf - 1),
    inf,
    sign | inf,
    inf | 1,
    inf | (uint64_t(1) << (F - 1))};
  std::vector<std::pair<uint64_t, uint64_t>> pairs;
  for(auto a : corners)
    for(auto b : corners)
      pairs.emplace_back(a, b);
  // Values at, below and above half an ULP expose alignment sticky and ties.
  const T half_ulp = std::ldexp(T(1), -int(F) - 1);
  for(T small :
      {half_ulp,
       std::nextafter(half_ulp, T(0)),
       std::nextafter(half_ulp, T(1))})
    for(uint64_t large : {unit, unit + 1, sign | unit})
      pairs.emplace_back(large, to_bits<T>(small));
  for(unsigned i = 0; i < 128; ++i)
    pairs.emplace_back(
      random() & (W == 32 ? UINT32_MAX : UINT64_MAX),
      random() & (W == 32 ? UINT32_MAX : UINT64_MAX));
  for(auto pair : pairs)
  {
    volatile T a = from_bits<T>(pair.first), b = from_bits<T>(pair.second);
    auto add = [&](const std::string &op, uint64_t expected, unsigned dst)
    {
      cases.push_back({op, W, dst, false, pair.first, pair.second, expected});
    };
    add("add", to_bits<T>(a + b), W);
    add("sub", to_bits<T>(a - b), W);
    add("mul", to_bits<T>(a * b), W);
    add("div", to_bits<T>(a / b), W);
    add("remainder", to_bits<T>(std::remainder(T(a), T(b))), W);
    add("fmod", to_bits<T>(std::fmod(T(a), T(b))), W);
    add("eq", a == b, 1);
    add("lt", a < b, 1);
    add("le", a <= b, 1);
    add("gt", a > b, 1);
    add("ge", a >= b, 1);
  }
  // Directed rounding is checked against volatile native arithmetic. FMA
  // uses the actual fused library operation, never a*b+c as its oracle.
  const int native_modes[] = {FE_TONEAREST, FE_DOWNWARD, FE_UPWARD, FE_TOWARDZERO};
  for(unsigned mode = 0; mode < 4; ++mode)
  {
    if(std::fesetround(native_modes[mode]))
      throw std::runtime_error("native rounding mode unavailable");
    for(auto pair : pairs)
    {
      volatile T a=from_bits<T>(pair.first), b=from_bits<T>(pair.second);
      if(mode != 0)
        for(const auto &value : std::vector<std::pair<std::string,T>>{
            {"add",a+b},{"sub",a-b},{"mul",a*b},{"div",a/b}})
          cases.push_back({value.first,W,W,false,pair.first,pair.second,to_bits<T>(value.second),0,mode});
      const auto third = corners[(pair.first ^ pair.second) % corners.size()];
      cases.push_back({"fma",W,W,false,pair.first,pair.second,
        to_bits<T>(std::fma(T(a),T(b),from_bits<T>(third))),third,mode});
    }
    for(auto bits : corners)
      cases.push_back({"sqrt",W,W,false,bits,0,
        to_bits<T>(std::sqrt(from_bits<T>(bits))),0,mode});
    for(unsigned i=0;i<128;++i)
    {
      const auto bits=random() & (W==32 ? UINT32_MAX : UINT64_MAX);
      cases.push_back({"sqrt",W,W,false,bits,0,
        to_bits<T>(std::sqrt(from_bits<T>(bits))),0,mode});
    }
    for(auto bits : {to_bits<T>(T(1)+std::ldexp(T(1),-int(F))),
                     inf-1})
    {
      const auto rhs = bits==inf-1 ? to_bits<T>(T(2)) : to_bits<T>(T(1)-std::ldexp(T(1),-int(F)));
      const auto third = bits==inf-1 ? bits|sign : to_bits<T>(T(-1));
      cases.push_back({"fma",W,W,false,bits,rhs,
        to_bits<T>(std::fma(from_bits<T>(bits),from_bits<T>(rhs),from_bits<T>(third))),third,mode});
    }
  }
  std::fesetround(FE_TONEAREST);
  // RNA has no native fenv selector. Check it with CBMC's independent
  // arbitrary-precision value arithmetic, including exact half-ULP ties.
  const auto spec=W==32 ? ieee_float_spect::single_precision() : ieee_float_spect::double_precision();
  for(auto pair : pairs)
    for(const std::string op : {"add","sub","mul","div"})
    {
      ieee_floatt a(spec,ieee_floatt::ROUND_TO_AWAY), b(spec,ieee_floatt::ROUND_TO_AWAY);
      a.unpack(mp_integer(pair.first)); b.unpack(mp_integer(pair.second));
      if(op=="add") a+=b; else if(op=="sub") a-=b;
      else if(op=="mul") a*=b; else a/=b;
      cases.push_back({op,W,W,false,pair.first,pair.second,numeric_cast_v<uint64_t>(a.pack()),0,4});
    }
  // Exact integer-times-power-of-two FMA oracle for ties-away. Align the
  // product and addend without rounding, then let CBMC value arithmetic
  // round once. This is independent of the production alignment circuit.
  for(auto pair : pairs)
  {
    const auto third = corners[(pair.first ^ pair.second) % corners.size()];
    ieee_floatt a(spec, ieee_floatt::ROUND_TO_AWAY), b(spec, ieee_floatt::ROUND_TO_AWAY), c(spec, ieee_floatt::ROUND_TO_AWAY);
    a.unpack(mp_integer(pair.first)); b.unpack(mp_integer(pair.second)); c.unpack(mp_integer(third));
    auto expected = to_bits<T>(std::fma(from_bits<T>(pair.first), from_bits<T>(pair.second), from_bits<T>(third)));
    if(!a.is_NaN() && !a.is_infinity() && !b.is_NaN() && !b.is_infinity() && !c.is_NaN() && !c.is_infinity())
    {
      mp_integer af,ae,bf,be,cf,ce;
      a.extract_base2(af,ae); b.extract_base2(bf,be); c.extract_base2(cf,ce);
      if(a.get_sign()) af=-af;
      if(b.get_sign()) bf=-bf;
      if(c.get_sign()) cf=-cf;
      const mp_integer pe=ae+be, exponent=pe<ce ? pe : ce;
      const mp_integer exact=af*bf*power(2,pe-exponent)+cf*power(2,ce-exponent);
      if(exact!=0)
      {
        ieee_floatt result(spec,ieee_floatt::ROUND_TO_AWAY);
        result.build(exact,exponent);
        expected=numeric_cast_v<uint64_t>(result.pack());
      } // Exact-zero signs are the same as the native RNE result.
    }
    cases.push_back({"fma",W,W,false,pair.first,pair.second,expected,third,4});
  }
  // A finite binary square root cannot lie exactly at a rounding midpoint:
  // squaring that odd halfway significand needs more input precision.
  for(auto bits : corners)
    cases.push_back({"sqrt",W,W,false,bits,0,to_bits<T>(std::sqrt(from_bits<T>(bits))),0,4});
  std::vector<uint64_t> values = corners;
  for(unsigned i = 0; i < 128; ++i)
    values.push_back(random() & (W == 32 ? UINT32_MAX : UINT64_MAX));
  // Cast boundaries include fractions truncating to signed minimum, exact
  // powers of two, and their adjacent representable values.
  for(unsigned dst : {8u, 16u, 32u, 64u})
    for(int exponent : {int(dst) - 1, int(dst)})
    {
      const T bound = std::ldexp(T(1), exponent);
      for(T value :
          {bound,
           std::nextafter(bound, T(0)),
           std::nextafter(bound, std::numeric_limits<T>::infinity()),
           -bound,
           std::nextafter(-bound, T(0)),
           std::nextafter(-bound, -std::numeric_limits<T>::infinity())})
        values.push_back(to_bits<T>(value));
    }
  for(T value : {T(-128.75), T(-0.75), T(0.75), T(127.75)})
    values.push_back(to_bits<T>(value));
  for(auto bits : values)
  {
    volatile T a = from_bits<T>(bits);
    cases.push_back({"neg", W, W, false, bits, 0, bits ^ sign});
    cases.push_back({"abs", W, W, false, bits, 0, bits & ~sign});
    cases.push_back({"nan", W, 1, false, bits, 0, std::isnan(a)});
    cases.push_back({"inf", W, 1, false, bits, 0, std::isinf(a)});
    cases.push_back({"normal", W, 1, false, bits, 0, std::isnormal(a)});
    const unsigned DW = W == 32 ? 64 : 32;
    cases.push_back(
      {"f2f",
       W,
       DW,
       false,
       bits,
       0,
       W == 32 ? to_bits<double>(double(a)) : to_bits<float>(float(a))});
    for(unsigned dst : {8u, 16u, 32u, 64u})
    {
      for(bool signed_destination : {false, true})
      {
        const long double integer = std::trunc(static_cast<long double>(a));
        const long double upper =
          std::ldexp(1.0L, signed_destination ? dst - 1 : dst);
        const long double lower = signed_destination ? -upper : 0;
        const bool valid =
          std::isfinite(a) && integer >= lower && integer < upper;
        cases.push_back({"valid", W, dst, signed_destination, bits, 0, valid});
        if(valid)
        {
          const uint64_t result = signed_destination
                                    ? uint64_t(static_cast<int64_t>(integer))
                                    : static_cast<uint64_t>(integer);
          cases.push_back({"f2i", W, dst, signed_destination, bits, 0, result});
        }
      }
    }
  }
}

void integer_cases(std::vector<caset> &cases, std::mt19937_64 &random)
{
  for(unsigned source : {8u, 16u, 32u, 64u})
  {
    const uint64_t mask = UINT64_MAX >> (64 - source);
    const uint64_t half = uint64_t(1) << (source - 1);
    std::vector<uint64_t> values = {
      0,
      1,
      mask,
      mask - 1,
      half,
      half - 1,
      (uint64_t(1) << 24) - 1,
      (uint64_t(1) << 24) + 1,
      (uint64_t(1) << 53) + 1,
      (uint64_t(1) << 53) + 3};
    for(unsigned i = 0; i < 128; ++i)
      values.push_back(random());
    for(auto bits : values)
    {
      bits &= mask;
      const uint64_t extended = bits & half ? bits | ~mask : bits;
      int64_t signed_value;
      std::memcpy(&signed_value, &extended, sizeof(signed_value));
      for(bool is_signed : {false, true})
      {
        volatile uint64_t u = bits;
        volatile int64_t s = signed_value;
        cases.push_back(
          {"i2f",
           source,
           32,
           is_signed,
           bits,
           0,
           to_bits<float>(is_signed ? float(s) : float(u))});
        cases.push_back(
          {"i2f",
           source,
           64,
           is_signed,
           bits,
           0,
           to_bits<double>(is_signed ? double(s) : double(u))});
      }
    }
  }
}

btor2_nid_t circuit(btor2_buildert &b, const caset &c)
{
  const auto a =
    b.constd(b.get_or_create_bitvec_sort(c.source), mp_integer(c.a));
  ieee754_aritht fp(
    b, c.op == "i2f" || c.op == "f2f" ? c.destination : c.source,
    b.constd(b.get_or_create_bitvec_sort(3), c.mode));
  if(c.op == "i2f")
    return fp.cast_int_to_float(a, c.source, c.is_signed);
  if(c.op == "f2f")
    return fp.cast_float_to_float(a, c.source);
  if(c.op == "f2i")
    return fp.cast_float_to_int(a, c.destination);
  if(c.op == "valid")
    return fp.float_to_int_valid(a, c.destination, c.is_signed);
  if(c.op == "sqrt")
    return fp.sqrt(a);
  if(c.op == "neg")
    return fp.neg(a);
  if(c.op == "abs")
    return fp.abs_value(a);
  if(c.op == "nan")
    return fp.is_nan_node(a);
  if(c.op == "inf")
    return fp.is_inf_node(a);
  if(c.op == "normal")
    return fp.is_normal_node(a);
  const auto rhs =
    b.constd(b.get_or_create_bitvec_sort(c.source), mp_integer(c.b));
  if(c.op == "remainder" || c.op == "fmod")
    return fp.remainder(a, rhs, c.op == "remainder");
  if(c.op == "fma")
    return fp.fma(a, rhs, b.constd(b.get_or_create_bitvec_sort(c.source), mp_integer(c.c)));
  if(c.op == "add")
    return fp.add(a, rhs, false);
  if(c.op == "sub")
    return fp.add(a, rhs, true);
  if(c.op == "mul")
    return fp.mul(a, rhs);
  if(c.op == "div")
    return fp.div(a, rhs);
  const std::vector<std::string> relations = {"eq", "lt", "le", "gt", "ge"};
  for(unsigned i = 0; i < relations.size(); ++i)
    if(c.op == relations[i])
      return fp.relation(a, rhs, i);
  throw std::runtime_error("unknown oracle operation");
}

int main(int argc, char **argv)
{
  if(argc != 2 || std::fesetround(FE_TONEAREST))
    return 1;
  // Raw bit conversion below uses the host little-endian IEEE representation.
  if(
    to_bits<float>(1.0f) != 0x3f800000 ||
    to_bits<double>(1.0) != UINT64_C(0x3ff0000000000000))
    return 1;
  std::mt19937_64 random(20261003);
  std::vector<caset> cases;
  floating_cases<float>(cases, random);
  floating_cases<double>(cases, random);
  integer_cases(cases, random);
  std::ofstream manifest(std::string(argv[1]) + "/cases.tsv");
  manifest
    << "case\top\tsource\tdestination\tsigned\ta_hex\tb_hex\tc_hex\tmode\texpected_hex\n";
  const unsigned batch_size = 128;
  for(unsigned start = 0; start < cases.size(); start += batch_size)
  {
    btor2_buildert b;
    const auto boolean = b.get_bool_sort();
    for(unsigned i = start; i < cases.size() && i < start + batch_size; ++i)
    {
      const auto &c = cases[i];
      manifest << std::dec << i << '\t' << c.op << '\t' << c.source << '\t'
               << c.destination << '\t' << c.is_signed << '\t' << std::hex
               << c.a << '\t' << c.b << '\t' << c.c << '\t' << std::dec << c.mode << '\t' << std::hex << c.expected << '\n';
      const auto actual = circuit(b, c);
      const unsigned result_width = c.op == "valid" ? 1 : c.destination;
      const auto expected = b.constd(
        b.get_or_create_bitvec_sort(result_width),
        mp_integer(c.expected & (UINT64_MAX >> (64 - result_width))));
      auto equal = b.eq(boolean, actual, expected);
      const bool floating_result = c.op == "add" || c.op == "sub" ||
                                   c.op == "mul" || c.op == "div" || c.op == "sqrt" || c.op == "fma" ||
                                   c.op == "remainder" || c.op == "fmod" ||
                                   c.op == "f2f" || c.op == "i2f";
      // C/IEEE leave NaN payload propagation choices to the implementation.
      // Check classification for NaNs, exact bits (including zero sign) otherwise.
      if(
        floating_result &&
        (result_width == 32 ? std::isnan(from_bits<float>(c.expected))
                            : std::isnan(from_bits<double>(c.expected))))
        equal = ieee754_aritht(b, result_width).is_nan_node(actual);
      const auto mismatch = b.lnot(boolean, equal);
      const auto state = b.state(boolean, "case_" + std::to_string(i));
      b.init(boolean, state, mismatch);
      b.next(boolean, state, state);
      b.bad(state, "mismatch_" + std::to_string(i));
    }
    std::ofstream model(
      std::string(argv[1]) + "/batch_" + std::to_string(start / batch_size) +
      ".btor2");
    b.write(model);
  }
}
