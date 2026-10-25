#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <goto-btor2/memory_capacity.h>
#include <testing-utils/use_catch.h>

namespace
{
exprt nondet(const typet &type)
{
  return side_effect_expr_nondett(type, source_locationt::nil());
}

struct capacity_fixturet
{
  configt::ansi_ct saved_config = config.ansi_c;
  symbol_tablet symbols;
  goto_programt program;
  symbol_exprt n{"n", signedbv_typet(64)};
  symbol_exprt cond{"cond", signedbv_typet(32)};
  symbol_exprt buffer{"buffer", array_typet(unsignedbv_typet(8), n)};

  capacity_fixturet()
  {
    config.ansi_c.set_ILP32();
    for(const auto &expr : {n, cond, buffer})
    {
      symbolt symbol{expr.get_identifier(), expr.type(), ID_C};
      symbol.is_lvalue = true;
      symbols.add(symbol);
      if(expr != buffer)
        program.add(goto_programt::make_decl(expr));
    }
    // Reproduce a short nondet result widened to long long, followed by an
    // inlined C helper parameter capturing the Boolean predicate as int.
    program.add(
      goto_programt::make_assignment(
        n, typecast_exprt(nondet(signedbv_typet(16)), n.type())));
    capture(bound(7));
  }

  ~capacity_fixturet()
  {
    config.ansi_c = saved_config;
  }

  exprt bound(int maximum) const
  {
    return and_exprt(
      binary_relation_exprt(n, ID_gt, from_integer(0, n.type())),
      binary_relation_exprt(n, ID_le, from_integer(maximum, n.type())));
  }

  void capture(const exprt &predicate)
  {
    program.add(
      goto_programt::make_assignment(
        cond, typecast_exprt(predicate, cond.type())));
  }

  mp_integer bytes()
  {
    program.add(
      goto_programt::make_assumption(
        notequal_exprt(cond, from_integer(0, cond.type()))));
    program.add(goto_programt::make_decl(buffer));
    program.update();
    const unsignedbv_typet size_type(32);
    const auto size =
      mult_exprt(typecast_exprt(n, size_type), from_integer(4, size_type));
    return infer_memory_capacity(
             program, namespacet(symbols), {{"buffer", size}})
      .objects.at("buffer");
  }
};
} // namespace

TEST_CASE("Captured capacity predicates", "[goto-btor2][memory-capacity]")
{
  capacity_fixturet f;
  const mp_integer unknown = (mp_integer(1) << 32) - 1;

  SECTION("inlined integer condition narrows the original size")
  {
    REQUIRE(f.bytes() == 28);
  }
  SECTION("predicate copies keep their dependency")
  {
    symbol_exprt copy{"copy", signedbv_typet(32)};
    f.symbols.add(symbolt{"copy", copy.type(), ID_C});
    f.program.add(goto_programt::make_decl(copy));
    f.program.add(goto_programt::make_assignment(copy, f.cond));
    f.program.add(goto_programt::make_dead(f.cond));
    f.cond = copy;
    REQUIRE(f.bytes() == 28);
  }
  SECTION("rewriting the source must invalidate the captured predicate")
  {
    f.program.add(
      goto_programt::make_assignment(f.n, from_integer(100, f.n.type())));
    REQUIRE(f.bytes() == 400);
  }
  SECTION("rewriting the condition must invalidate its predicate")
  {
    f.program.add(
      goto_programt::make_assignment(f.cond, nondet(f.cond.type())));
    REQUIRE(f.bytes() == unknown);
  }
  SECTION("dead and redeclared dependencies lose their facts")
  {
    f.program.add(goto_programt::make_dead(f.n));
    f.program.add(goto_programt::make_decl(f.n));
    REQUIRE(f.bytes() == unknown);
  }
  SECTION("an indirect source write invalidates captured predicates")
  {
    symbol_exprt pointer{"pointer", pointer_type(f.n.type())};
    f.symbols.add(symbolt{"pointer", pointer.type(), ID_C});
    f.program.add(goto_programt::make_decl(pointer));
    f.program.add(
      goto_programt::make_assignment(pointer, address_of_exprt(f.n)));
    f.program.add(
      goto_programt::make_assignment(
        dereference_exprt(pointer), nondet(f.n.type())));
    REQUIRE(f.bytes() == unknown);
  }
  SECTION("unknown writes also invalidate dependency facts")
  {
    symbol_exprt pointer{"pointer", pointer_type(f.n.type())};
    f.symbols.add(symbolt{"pointer", pointer.type(), ID_C});
    f.program.add(goto_programt::make_decl(pointer));
    f.program.add(
      goto_programt::make_assignment(pointer, address_of_exprt(f.n)));
    f.program.add(
      goto_programt::make_assignment(pointer, nondet(pointer.type())));
    f.program.add(
      goto_programt::make_assignment(
        dereference_exprt(pointer), nondet(f.n.type())));
    REQUIRE(f.bytes() == unknown);
  }
  SECTION("different incoming predicates are discarded at joins")
  {
    auto branch = f.program.add_instruction(SKIP);
    f.capture(f.bound(7));
    auto jump = f.program.add_instruction(SKIP);
    auto alternative = f.program.add_instruction(SKIP);
    f.capture(f.bound(100));
    auto join = f.program.add_instruction(SKIP);
    *branch = goto_programt::make_goto(alternative, nondet(bool_typet()));
    *jump = goto_programt::make_goto(join);
    REQUIRE(f.bytes() == unknown);
  }
  SECTION("lossy integer casts cannot narrow the original value")
  {
    f.capture(binary_relation_exprt(
      typecast_exprt(f.n, unsignedbv_typet(8)),
      ID_lt,
      from_integer(8, unsignedbv_typet(8))));
    REQUIRE(f.bytes() == unknown);
  }
}
