/*******************************************************************\

Module: Unit tests for float utils and approximation

Author: Daniel Kroening

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

// for debug output in case of failure
#include <iostream>
#include <limits>
#include <random>

#include <solvers/floatbv/float_approximation.h>
#include <solvers/floatbv/float_utils.h>
#include <solvers/sat/satcheck.h>

typedef std::uniform_int_distribution<unsigned> distt;

static float random_float(distt &dist, std::mt19937 &gen)
{
  union
  {
    float f;
    unsigned int i;
  } u;

  u.i = dist(gen);
  u.i = (u.i << 16) ^ dist(gen);

  return u.f;
}

static bool eq(const ieee_float_valuet &a, const ieee_float_valuet &b)
{
  return (a.is_NaN() && b.is_NaN()) ||
         (a.is_infinity() && b.is_infinity() && a.get_sign() == b.get_sign()) ||
         a == b;
}

#if 0
static std::string to_str(const bvt &bv)
{
  std::string result;
  for(unsigned i=0; i<bv.size(); i++)
  {
    char ch;
    if(bv[i]==const_literal(true))
      ch='1';
    else if(bv[i]==const_literal(false))
      ch='0';
    else
      ch='?';
    result=ch+result;
  }
  return result;
}
#endif

typedef enum { PLUS=0, MINUS=1, MULT=2, DIV=3 } binopt;
const char *binopsyms[]={ " + ", " - ", " * ", " / " };

static float set_values(
  distt &dist,
  std::mt19937 &gen,
  float_utilst &float_utils,
  float &f1,
  float &f2,
  ieee_float_valuet &i1,
  ieee_float_valuet &i2)
{
  f1 = random_float(dist, gen);
  f2 = random_float(dist, gen);
  i1.from_float(f1);
  i2.from_float(f2);
  float_utils.spec = i1.spec;

  return f1;
}

static bvt compute(
  unsigned i,
  float_utilst &float_utils,
  const float &f2,
  float &f3,
  const ieee_float_valuet &i1,
  const ieee_float_valuet &i2)
{
  const bvt b1 = float_utils.build_constant(i1);
  const bvt b2 = float_utils.build_constant(i2);

  const auto op = i % 3;

  switch(op)
  {
  case PLUS:
    f3 += f2;
    return float_utils.add(b1, b2);

  case MINUS:
    f3 -= f2;
    return float_utils.sub(b1, b2);

  case MULT:
    f3 *= f2;
    return float_utils.mul(b1, b2);

  case DIV:
    f3 /= f2;
    return float_utils.div(b1, b2);
  }

  return bvt();
}

static void print(
  unsigned i,
  const ieee_float_valuet &i1,
  const ieee_float_valuet &i2,
  const ieee_float_valuet &i3,
  const ieee_float_valuet &fres,
  const float &f1,
  const float &f2,
  const float &f3)
{
  const unsigned op = i % 3;
  const char *opsym = binopsyms[op];

  std::cout << i1 << opsym << i2 << " != " << fres << '\n';
  std::cout << f1 << opsym << f2 << " == " << f3 << '\n';
  std::cout << integer2binary(i1.get_exponent(), i1.spec.e) << " "
            << integer2binary(i1.get_fraction(), i1.spec.f + 1) << opsym
            << integer2binary(i2.get_exponent(), i1.spec.e) << " "
            << integer2binary(i2.get_fraction(), i1.spec.f + 1) << " != "
            << integer2binary(fres.get_exponent(), i1.spec.e) << " "
            << integer2binary(fres.get_fraction(), i1.spec.f + 1) << '\n';
  std::cout << integer2binary(i1.get_exponent(), i1.spec.e) << " "
            << integer2binary(i1.get_fraction(), i1.spec.f + 1) << opsym
            << integer2binary(i2.get_exponent(), i1.spec.e) << " "
            << integer2binary(i2.get_fraction(), i1.spec.f + 1) << " == "
            << integer2binary(i3.get_exponent(), i1.spec.e) << " "
            << integer2binary(i3.get_fraction(), i1.spec.f + 1) << '\n';
}

SCENARIO("float_utils", "[core][solvers][floatbv][float_utils]")
{
  ieee_float_valuet i1, i2, i3;
  float f1, f2, f3;

  std::random_device rd;
  std::mt19937 gen(rd());
  distt dist(0, std::numeric_limits<unsigned>::max());

  for(unsigned i = 0; i < 200; i++)
  {
    satcheckt satcheck(null_message_handler);
    float_utilst float_utils(satcheck);

    GIVEN("Two random floating point numbers")
    {
      f3 = set_values(dist, gen, float_utils, f1, f2, i1, i2);
      bvt res = compute(i, float_utils, f2, f3, i1, i2);

      THEN("Machine execution yields the same result as symbolic computation")
      {
        i3.from_float(f3);

        const satcheckt::resultt result = satcheck.prop_solve();
        REQUIRE(result == satcheckt::resultt::P_SATISFIABLE);

        const ieee_float_valuet fres = float_utils.get(res);

        if(!eq(fres, i3))
          print(i, i1, i2, i3, fres, f1, f2, f3);

        REQUIRE(eq(fres, i3));
      }
    }
  }
}

SCENARIO("float_approximation", "[core][solvers][floatbv][float_approximation]")
{
  ieee_float_valuet i1, i2, i3;
  float f1, f2, f3;

  std::random_device rd;
  std::mt19937 gen(rd());
  distt dist(0, std::numeric_limits<unsigned>::max());

  for(unsigned i = 0; i < 200; i++)
  {
    satcheckt satcheck(null_message_handler);
    float_approximationt float_utils(satcheck);

    GIVEN("Two random floating point numbers")
    {
      f3 = set_values(dist, gen, float_utils, f1, f2, i1, i2);
      bvt res = compute(i, float_utils, f2, f3, i1, i2);

      THEN("Machine execution yields the same result as symbolic computation")
      {
        i3.from_float(f3);

        const satcheckt::resultt result = satcheck.prop_solve();
        REQUIRE(result == satcheckt::resultt::P_SATISFIABLE);

        const ieee_float_valuet fres = float_utils.get(res);

        if(!eq(fres, i3))
          print(i, i1, i2, i3, fres, f1, f2, f3);

        REQUIRE(eq(fres, i3));
      }
    }
  }
}

static ieee_float_valuet
round_to_integral(ieee_float_valuet op, ieee_floatt::rounding_modet rm)
{
  satcheckt satcheck(null_message_handler);
  float_utilst float_utils(satcheck);
  float_utils.rounding_mode_bits.set(rm);
  float_utils.spec = op.spec;

  // add constraint
  auto op_bv = float_utils.build_constant(op);
  bvt result_bv = float_utils.round_to_integral(op_bv);

  // solve
  const auto result = satcheck.prop_solve();
  REQUIRE(result == satcheckt::resultt::P_SATISFIABLE);

  return float_utils.get(result_bv);
}

SCENARIO(
  "float_utils_round_to_integral",
  "[core][solvers][floatbv][float_utils][round_to_integral]")
{
  const auto dp = ieee_float_spect::double_precision();

  const auto NaN = ieee_float_valuet::NaN(dp);
  const auto plus_inf = ieee_float_valuet::plus_infinity(dp);
  const auto minus_inf = ieee_float_valuet::minus_infinity(dp);
  const auto dmax = std::numeric_limits<double>::max();

  auto from_double = [](double d) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_double(d);
    return v;
  };

  const auto up = ieee_floatt::ROUND_TO_PLUS_INF;

  REQUIRE(round_to_integral(NaN, up) == NaN);
  REQUIRE(round_to_integral(plus_inf, up) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, up) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), up) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), up) == -0.0);
  REQUIRE(round_to_integral(from_double(1), up) == 1);
  REQUIRE(round_to_integral(from_double(0.1), up) == 1);
  REQUIRE(round_to_integral(from_double(-0.1), up) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), up) == 1);
  REQUIRE(round_to_integral(from_double(0.49999999), up) == 1);
  REQUIRE(round_to_integral(from_double(0.500000001), up) == 1);
  REQUIRE(round_to_integral(from_double(10.1), up) == 11);
  REQUIRE(round_to_integral(from_double(-10.1), up) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), up) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), up) == dmax);

  const auto down = ieee_floatt::ROUND_TO_MINUS_INF;

  REQUIRE(round_to_integral(NaN, down) == NaN);
  REQUIRE(round_to_integral(plus_inf, down) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, down) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), down) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), down) == -0.0);
  REQUIRE(round_to_integral(from_double(1), down) == 1);
  REQUIRE(round_to_integral(from_double(0.1), down) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), down) == -1);
  REQUIRE(round_to_integral(from_double(0.5), down) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), down) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), down) == 0);
  REQUIRE(round_to_integral(from_double(10.1), down) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), down) == -11);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), down) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), down) == dmax);

  const auto even = ieee_floatt::ROUND_TO_EVEN;

  REQUIRE(round_to_integral(NaN, even) == NaN);
  REQUIRE(round_to_integral(plus_inf, even) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, even) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), even) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), even) == -0.0);
  REQUIRE(round_to_integral(from_double(1), even) == 1);
  REQUIRE(round_to_integral(from_double(0.1), even) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), even) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), even) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), even) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), even) == 1);
  REQUIRE(round_to_integral(from_double(10.1), even) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), even) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), even) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), even) == dmax);

  const auto zero = ieee_floatt::ROUND_TO_ZERO;

  REQUIRE(round_to_integral(NaN, zero) == NaN);
  REQUIRE(round_to_integral(plus_inf, zero) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, zero) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), zero) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), zero) == -0.0);
  REQUIRE(round_to_integral(from_double(1), zero) == 1);
  REQUIRE(round_to_integral(from_double(0.1), zero) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), zero) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), zero) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), zero) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), zero) == 0);
  REQUIRE(round_to_integral(from_double(10.1), zero) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), zero) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), zero) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), zero) == dmax);

  const auto away = ieee_floatt::ROUND_TO_AWAY;

  REQUIRE(round_to_integral(NaN, away) == NaN);
  REQUIRE(round_to_integral(plus_inf, away) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, away) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), away) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), away) == -0.0);
  REQUIRE(round_to_integral(from_double(1), away) == 1);
  REQUIRE(round_to_integral(from_double(0.1), away) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), away) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), away) == 1);
  REQUIRE(round_to_integral(from_double(0.49999999), away) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), away) == 1);
  REQUIRE(round_to_integral(from_double(10.1), away) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), away) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), away) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), away) == dmax);
}
