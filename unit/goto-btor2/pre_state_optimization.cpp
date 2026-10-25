#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <goto-btor2/pre_state_optimization.h>
#include <testing-utils/use_catch.h>

namespace
{
struct optimization_fixturet
{
  symbol_tablet symbols;
  goto_programt program;

  symbol_exprt symbol(const irep_idt &id, const typet &type)
  {
    symbolt value{id, type, ID_C};
    value.is_lvalue = true;
    symbols.add(value);
    return value.symbol_expr();
  }

  pre_state_optimization_reportt optimize()
  {
    program.add(goto_programt::make_end_function());
    program.update();
    return optimize_before_state(program, namespacet(symbols));
  }

  std::size_t count(goto_program_instruction_typet type) const
  {
    std::size_t result = 0;
    for(const auto &instruction : program.instructions)
      result += instruction.type() == type;
    return result;
  }

  const exprt &assertion() const
  {
    for(const auto &instruction : program.instructions)
      if(instruction.is_assert())
        return instruction.condition();
    UNREACHABLE;
  }
};

exprt nondet(const typet &type)
{
  return side_effect_expr_nondett(type, source_locationt::nil());
}
} // namespace

TEST_CASE(
  "Pointer and string programs retain their original identity universe",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet byte(8), integer_type(32);
  const auto unused =
    f.symbol("unused_array", array_typet(byte, from_integer(32, integer_type)));
  f.program.add(goto_programt::make_decl(unused));
  const auto x = f.symbol("x", integer_type);
  f.program.add(
    goto_programt::make_assignment(x, from_integer(0, integer_type)));
  const auto jump = f.program.add_instruction(GOTO);
  jump->condition_nonconst() = equal_exprt(x, from_integer(0, integer_type));
  SECTION("raw pointer integer representation")
  {
    const auto pointer = f.symbol("pointer", pointer_typet(byte, 64));
    f.program.add(
      goto_programt::make_assertion(equal_exprt(
        typecast_exprt(pointer, unsignedbv_typet(64)),
        from_integer(0, unsignedbv_typet(64)))));
  }
  SECTION("unreachable string root still reserves collection order")
  {
    f.program.add(
      goto_programt::make_other(
        code_expressiont(string_constantt("unreachable string"))));
  }
  SECTION("pointer-containing aggregate type")
  {
    const struct_typet structure(
      {struct_typet::componentt("pointer", pointer_typet(byte, 64))});
    const auto object = f.symbol("pointer_aggregate", structure);
    f.program.add(goto_programt::make_decl(object));
  }
  SECTION("referenced static initializer contains an address")
  {
    const auto implicit = f.symbol("implicit", unsignedbv_typet(64));
    auto &symbol = f.symbols.get_writeable_ref("implicit");
    symbol.is_static_lifetime = true;
    symbol.value = typecast_exprt(address_of_exprt(x), implicit.type());
    const auto copy = f.symbol("copy", implicit.type());
    f.program.add(goto_programt::make_assignment(copy, implicit));
  }
  f.program.add(goto_programt::make_assertion(false_exprt()));
  const auto end = f.program.add(goto_programt::make_assertion(true_exprt()));
  jump->targets.push_back(end);
  const auto report = f.optimize();
  REQUIRE(report.skipped_reason == "pointer-identity-sensitive-program");
  REQUIRE(report.before == report.after);
  REQUIRE(report.constants_replaced == 0);
  REQUIRE(report.unreachable_instructions == 0);
  REQUIRE(report.removed_objects == 0);
  REQUIRE(report.unreachable_assertions.empty());
  REQUIRE(f.count(DECL) >= 1);
}

TEST_CASE(
  "Builtin NULL bookkeeping does not disable integer-array optimization",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet byte(8), integer_type(32);
  const auto unused =
    f.symbol("unused_array", array_typet(byte, from_integer(32, integer_type)));
  const auto bookkeeping =
    f.symbol("__CPROVER_deallocated", pointer_typet(byte, 64));
  f.symbols.get_writeable_ref(bookkeeping.get_identifier())
    .location.set_file("<built-in>");
  f.program.add(
    goto_programt::make_assignment(
      bookkeeping, null_pointer_exprt(to_pointer_type(bookkeeping.type()))));
  f.program.add(goto_programt::make_decl(unused));
  f.program.add(goto_programt::make_assertion(true_exprt()));
  SECTION("unobserved builtin NULL initialization is ignored by the guard")
  {
    const auto report = f.optimize();
    REQUIRE(report.skipped_reason.empty());
    REQUIRE(report.removed_objects == 1);
    REQUIRE(f.count(DECL) == 0);
  }
  SECTION("an actual bookkeeping pointer read invokes the guard")
  {
    f.program.add(
      goto_programt::make_assertion(equal_exprt(
        bookkeeping, null_pointer_exprt(to_pointer_type(bookkeeping.type())))));
    const auto report = f.optimize();
    REQUIRE(report.skipped_reason == "pointer-identity-sensitive-program");
    REQUIRE(report.removed_objects == 0);
    REQUIRE(f.count(DECL) == 1);
  }
}

TEST_CASE(
  "Pre-state constant propagation observes bit-vector widths",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet byte(8), word(32);
  const auto x = f.symbol("x", byte);
  f.program.add(goto_programt::make_decl(x));
  SECTION("unsigned arithmetic wraps before comparison")
  {
    f.program.add(goto_programt::make_assignment(x, from_integer(255, byte)));
    f.program.add(
      goto_programt::make_assignment(x, plus_exprt(x, from_integer(1, byte))));
    f.program.add(
      goto_programt::make_assertion(equal_exprt(x, from_integer(0, byte))));
  }
  SECTION("casts truncate to the destination width")
  {
    f.program.add(
      goto_programt::make_assignment(
        x, typecast_exprt(from_integer(256, word), byte)));
    f.program.add(
      goto_programt::make_assertion(equal_exprt(x, from_integer(0, byte))));
  }
  const auto report = f.optimize();
  REQUIRE(f.assertion().is_true());
  REQUIRE(report.constants_replaced != 0);
  REQUIRE(f.count(ASSIGN) == 0);
  REQUIRE(f.count(ASSERT) == 1);
}

TEST_CASE(
  "Constant division and remainder use signed result widths",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const auto check = [&](
                       const typet &type,
                       int numerator,
                       int denominator,
                       int expected,
                       bool remainder)
  {
    const auto source = f.symbol("source", type);
    const auto result = f.symbol("result", type);
    f.program.add(
      goto_programt::make_assignment(source, from_integer(numerator, type)));
    const exprt expression =
      remainder ? exprt(mod_exprt(source, from_integer(denominator, type)))
                : exprt(div_exprt(source, from_integer(denominator, type)));
    f.program.add(goto_programt::make_assignment(result, expression));
    f.program.add(
      goto_programt::make_assertion(
        equal_exprt(result, from_integer(expected, type))));
    f.optimize();
    REQUIRE(f.assertion().is_true());
    REQUIRE(f.count(ASSIGN) == 0);
    REQUIRE(f.count(ASSERT) == 1);
    REQUIRE(f.count(ASSUME) == 0);
  };
  SECTION("unsigned division uses the high bit as data")
  {
    check(unsignedbv_typet(8), 255, 2, 127, false);
  }
  SECTION("signed division truncates toward zero")
  {
    check(signedbv_typet(8), -7, 3, -2, false);
  }
  SECTION("negative divisor preserves signed quotient")
  {
    check(signedbv_typet(8), 7, -3, -2, false);
  }
  SECTION("unsigned remainder is nonnegative")
  {
    check(unsignedbv_typet(8), 255, 16, 15, true);
  }
  SECTION("signed remainder follows the dividend")
  {
    check(signedbv_typet(8), -7, 3, -1, true);
  }
  SECTION("signed overflow retains the encoder's bit-vector wrap")
  {
    check(signedbv_typet(8), -128, -1, -128, false);
  }
}

TEST_CASE(
  "Constant shifts preserve source bits and truncate shift operands",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const auto check = [&](
                       const typet &type,
                       int initial,
                       const irep_idt &id,
                       int distance,
                       int expected)
  {
    const auto source = f.symbol("source", type);
    const auto result = f.symbol("result", type);
    f.program.add(
      goto_programt::make_assignment(source, from_integer(initial, type)));
    const exprt shift = binary_exprt(
      source, id, from_integer(distance, unsignedbv_typet(32)), type);
    f.program.add(goto_programt::make_assignment(result, shift));
    f.program.add(
      goto_programt::make_assertion(
        equal_exprt(result, from_integer(expected, type))));
    f.optimize();
    REQUIRE(f.assertion().is_true());
    REQUIRE(f.count(ASSIGN) == 0);
    REQUIRE(f.count(ASSUME) == 0);
  };
  SECTION("left shift wraps at the result width")
  {
    check(unsignedbv_typet(8), 129, ID_shl, 1, 2);
  }
  SECTION("logical right shift fills high bits with zero")
  {
    check(unsignedbv_typet(8), 254, ID_lshr, 1, 127);
  }
  SECTION("arithmetic right shift extends a negative sign bit")
  {
    check(signedbv_typet(8), -3, ID_ashr, 1, -2);
  }
  SECTION("logical shift ignores the signed numeric interpretation")
  {
    check(signedbv_typet(8), -2, ID_lshr, 1, 127);
  }
  SECTION("arithmetic shift uses the high bit for an unsigned source")
  {
    check(unsignedbv_typet(8), 254, ID_ashr, 1, 255);
  }
  SECTION("shift distance is cast to the encoder's operand width")
  {
    check(unsignedbv_typet(8), 7, ID_shl, 256, 7);
  }
  SECTION("large logical distance produces zero")
  {
    check(unsignedbv_typet(8), 255, ID_lshr, 8, 0);
  }
  SECTION("large arithmetic distance preserves the sign bit")
  {
    check(signedbv_typet(8), -3, ID_ashr, 8, -1);
  }
}

TEST_CASE(
  "Unresolved division preserves the encoder's zero-divisor behavior",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(8);
  const auto divisor = f.symbol("divisor", type);
  f.program.add(goto_programt::make_decl(divisor));
  exprt expression = div_exprt(from_integer(0, type), divisor);
  SECTION("an unknown divisor is not inferred nonzero")
  {
  }
  SECTION("outer simplification does not rewrite the unresolved division")
  {
    expression = plus_exprt(expression, from_integer(0, type));
  }
  SECTION("a known zero divisor remains an operation")
  {
    f.program.add(
      goto_programt::make_assignment(divisor, from_integer(0, type)));
  }
  f.program.add(
    goto_programt::make_assertion(
      equal_exprt(expression, from_integer(0, type))));
  f.optimize();
  REQUIRE_FALSE(f.assertion().is_true());
  REQUIRE(f.count(ASSERT) == 1);
  REQUIRE(f.count(ASSUME) == 0);
}

TEST_CASE(
  "Pre-state propagation intersects facts at CFG joins",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(8);
  const auto x = f.symbol("x", type);
  const auto choice = f.symbol("choice", bool_typet());
  f.program.add(goto_programt::make_decl(x));
  f.program.add(goto_programt::make_decl(choice));
  const auto branch = f.program.add_instruction(GOTO);
  branch->condition_nonconst() = choice;
  f.program.add(goto_programt::make_assignment(x, from_integer(1, type)));
  const auto skip_else = f.program.add_instruction(GOTO);
  skip_else->condition_nonconst() = true_exprt();
  int else_value = 2;
  SECTION("different constants are forgotten")
  {
    else_value = 2;
  }
  SECTION("a constant shared by every predecessor is retained")
  {
    else_value = 1;
  }
  const auto other = f.program.add(
    goto_programt::make_assignment(x, from_integer(else_value, type)));
  const auto join = f.program.add(
    goto_programt::make_assertion(equal_exprt(x, from_integer(1, type))));
  branch->targets.push_back(other);
  skip_else->targets.push_back(join);
  f.optimize();
  REQUIRE(f.assertion().is_true() == (else_value == 1));
  if(else_value != 1)
    REQUIRE(f.count(ASSIGN) == 2);
  REQUIRE(f.count(GOTO) >= 1);
}

TEST_CASE(
  "Assertions never constrain the pre-state dataflow",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(8);
  const auto x = f.symbol("x", type);
  f.program.add(goto_programt::make_decl(x));
  f.program.add(goto_programt::make_assignment(x, nondet(type)));
  f.program.add(
    goto_programt::make_assertion(equal_exprt(x, from_integer(0, type))));
  const auto branch = f.program.add_instruction(GOTO);
  branch->condition_nonconst() = equal_exprt(x, from_integer(0, type));
  source_locationt selected;
  selected.set_property_id("second-property");
  f.program.add(goto_programt::make_assertion(false_exprt(), selected));
  const auto end = f.program.add(goto_programt::make_skip());
  branch->targets.push_back(end);
  const auto report = f.optimize();
  REQUIRE(f.count(ASSERT) == 2);
  REQUIRE(f.count(ASSUME) == 0);
  REQUIRE(report.unreachable_assertions.empty());
}

TEST_CASE(
  "Pre-state optimization preserves loops and their exit dependencies",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(8);
  const auto counter = f.symbol("counter", type);
  f.program.add(goto_programt::make_decl(counter));
  f.program.add(goto_programt::make_assignment(counter, from_integer(0, type)));
  const auto head = f.program.add_instruction(GOTO);
  head->condition_nonconst() = equal_exprt(counter, from_integer(3, type));
  f.program.add(
    goto_programt::make_assignment(
      counter, plus_exprt(counter, from_integer(1, type))));
  f.program.add(goto_programt::make_goto(head));
  const auto property = f.program.add(
    goto_programt::make_assertion(equal_exprt(counter, from_integer(3, type))));
  head->targets.push_back(property);
  const auto report = f.optimize();
  REQUIRE(f.count(GOTO) == 2);
  REQUIRE(f.count(ASSIGN) == 2);
  REQUIRE(f.count(ASSERT) == 1);
  REQUIRE(report.unreachable_assertions.empty());
}

TEST_CASE(
  "Pre-state optimization removes irrelevant objects before capacity planning",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet byte(8), size(64);
  const auto buffer = f.symbol(
    "oversized", array_typet(byte, from_integer(mp_integer(1) << 40, size)));
  SECTION("automatic object")
  {
  }
  SECTION("static aggregate with a pure literal initializer")
  {
    auto &symbol = f.symbols.get_writeable_ref("oversized");
    symbol.is_static_lifetime = true;
    symbol.value =
      array_of_exprt(from_integer(0, byte), to_array_type(buffer.type()));
  }
  f.program.add(goto_programt::make_decl(buffer));
  f.program.add(
    goto_programt::make_assignment(
      index_exprt(buffer, from_integer(0, size)), from_integer(7, byte)));
  f.program.add(goto_programt::make_dead(buffer));
  // Unknown operations are retained without anchoring unrelated data.
  codet unknown("unknown_pre_state_event");
  f.program.add(goto_programt::make_other(unknown));
  f.program.add(goto_programt::make_assertion(true_exprt()));
  const auto report = f.optimize();
  REQUIRE(report.removed_objects == 1);
  REQUIRE(report.assignments == 1);
  REQUIRE(report.declarations == 1);
  REQUIRE(report.lifetimes == 1);
  REQUIRE(report.memory_symbols.count("oversized") == 0);
  REQUIRE(f.count(OTHER) == 1);
}

TEST_CASE(
  "Pre-state object projection retains alias-observable storage",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet byte(8), size(64);
  const auto buffer =
    f.symbol("buffer", array_typet(byte, from_integer(32, size)));
  const auto p = f.symbol("p", pointer_typet(byte, 64));
  f.program.add(goto_programt::make_decl(buffer));
  f.program.add(
    goto_programt::make_assignment(
      index_exprt(buffer, from_integer(0, size)), from_integer(7, byte)));
  SECTION("an explicit address keeps the complete object")
  {
    f.program.add(
      goto_programt::make_assignment(
        p, address_of_exprt(index_exprt(buffer, from_integer(0, size)))));
  }
  SECTION("arbitrary pointer input keeps source objects")
  {
    f.program.add(goto_programt::make_assignment(p, nondet(p.type())));
  }
  f.program.add(goto_programt::make_assertion(true_exprt()));
  const auto report = f.optimize();
  REQUIRE(report.removed_objects == 0);
  REQUIRE(report.memory_symbols.count("buffer") == 1);
  REQUIRE(f.count(ASSIGN) == 2);
}

TEST_CASE(
  "Alias stores invalidate propagated scalar facts",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(8);
  const auto x = f.symbol("x", type);
  const auto p = f.symbol("p", pointer_typet(type, 64));
  f.program.add(goto_programt::make_assignment(x, from_integer(0, type)));
  f.program.add(goto_programt::make_assignment(p, address_of_exprt(x)));
  f.program.add(
    goto_programt::make_assignment(
      dereference_exprt(p, type), from_integer(1, type)));
  f.program.add(
    goto_programt::make_assertion(equal_exprt(x, from_integer(0, type))));
  f.optimize();
  REQUIRE_FALSE(f.assertion().is_true());
  REQUIRE(f.count(ASSIGN) == 3);
}

TEST_CASE(
  "Pre-state cleanup records unreachable selected assertions",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(8);
  const auto x = f.symbol("x", type);
  f.program.add(goto_programt::make_assignment(x, from_integer(255, type)));
  const auto branch = f.program.add_instruction(GOTO);
  branch->condition_nonconst() = equal_exprt(x, from_integer(255, type));
  source_locationt location;
  location.set_property_id("unreachable-selected");
  f.program.add(goto_programt::make_assertion(false_exprt(), location));
  const auto retained =
    f.program.add(goto_programt::make_assertion(true_exprt()));
  branch->targets.push_back(retained);
  const auto report = f.optimize();
  REQUIRE(f.count(ASSERT) == 1);
  REQUIRE(report.unreachable_assertions.size() == 1);
  REQUIRE(
    report.unreachable_assertions.front().get_property_id() ==
    "unreachable-selected");
}

TEST_CASE(
  "Object removal keeps VLA type dependencies",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(32);
  const auto n = f.symbol("n", type);
  const auto buffer = f.symbol("buffer", array_typet(type, n));
  f.program.add(goto_programt::make_decl(n));
  f.program.add(goto_programt::make_assignment(n, nondet(type)));
  f.program.add(goto_programt::make_decl(buffer));
  f.program.add(goto_programt::make_assertion(true_exprt()));
  const auto report = f.optimize();
  REQUIRE(report.removed_objects == 1);
  REQUIRE(f.count(ASSIGN) == 1);
  REQUIRE(f.count(DECL) == 1);
}

TEST_CASE(
  "Aggregate qualifier and initializer effects remain observable",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  unsignedbv_typet type(8);
  SECTION("a volatile member prevents object projection")
  {
    type.set(ID_C_volatile, true);
    const struct_typet structure({struct_typet::componentt("field", type)});
    const auto object = f.symbol("object", structure);
    f.program.add(goto_programt::make_decl(object));
    f.program.add(
      goto_programt::make_assignment(
        member_exprt(object, "field", type), from_integer(1, type)));
    f.program.add(goto_programt::make_assertion(true_exprt()));
    const auto report = f.optimize();
    REQUIRE(report.removed_objects == 0);
    REQUIRE(f.count(DECL) == 1);
    REQUIRE(f.count(ASSIGN) == 1);
  }
  SECTION("implicit aggregate initializer effects keep the last reference")
  {
    const array_typet array(type, from_integer(32, unsignedbv_typet(64)));
    const auto object = f.symbol("object", array);
    auto &symbol = f.symbols.get_writeable_ref("object");
    symbol.is_static_lifetime = true;
    symbol.value = array_of_exprt(nondet(type), array);
    const auto unused = f.symbol("unused", type);
    f.program.add(
      goto_programt::make_assignment(
        unused, index_exprt(object, from_integer(0, unsignedbv_typet(64)))));
    f.program.add(goto_programt::make_assertion(true_exprt()));
    const auto report = f.optimize();
    REQUIRE(report.forced_static_symbols.count("object") == 1);
    REQUIRE(report.memory_symbols.count("object") == 1);
    REQUIRE(f.count(ASSIGN) == 1);
  }
}

TEST_CASE(
  "Pre-state optimization keeps implicit initializer effects",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(32);
  const auto scalar = f.symbol("implicit", type);
  auto &symbol = f.symbols.get_writeable_ref("implicit");
  symbol.is_static_lifetime = true;
  // An implicit arbitrary/side-effect initializer must still be evaluated
  // even if the source scalar's only explicit use appears to be dead.
  symbol.value = nondet(type);
  const auto dead_copy = f.symbol("dead_copy", type);
  f.program.add(goto_programt::make_assignment(dead_copy, scalar));
  f.program.add(goto_programt::make_assertion(true_exprt()));
  const auto report = f.optimize();
  REQUIRE(f.count(ASSIGN) == 1);
  REQUIRE(report.forced_static_symbols.count("implicit") == 1);
}

TEST_CASE(
  "Unknown calls and custom memory events discard scalar facts",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(8);
  const auto x = f.symbol("x", type);
  f.program.add(goto_programt::make_assignment(x, from_integer(0, type)));
  SECTION("a call with unspecified external effects")
  {
    const auto function = f.symbol("external", code_typet({}, empty_typet()));
    f.program.add(goto_programt::make_function_call(nil_exprt(), function, {}));
  }
  SECTION("a converter-specific memory event")
  {
    codet event("c2btor_custom_memory_event");
    f.program.add(goto_programt::make_other(event));
  }
  f.program.add(
    goto_programt::make_assertion(equal_exprt(x, from_integer(0, type))));
  f.optimize();
  REQUIRE_FALSE(f.assertion().is_true());
  REQUIRE(f.count(ASSIGN) == 1);
}

TEST_CASE(
  "VLA size effects are not removed with an unused declaration",
  "[goto-btor2][pre-state-optimization]")
{
  optimization_fixturet f;
  const unsignedbv_typet type(32);
  const auto buffer = f.symbol("buffer", array_typet(type, nondet(type)));
  f.program.add(goto_programt::make_decl(buffer));
  f.program.add(goto_programt::make_assertion(true_exprt()));
  const auto report = f.optimize();
  REQUIRE(report.removed_objects == 0);
  REQUIRE(f.count(DECL) == 1);
}
