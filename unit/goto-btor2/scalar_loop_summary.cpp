// Exact semantic and rejection probes for constant integer loop summaries.
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <goto-btor2/scalar_loop_summary.h>
#include <testing-utils/use_catch.h>

#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

namespace
{
using valuest = std::map<irep_idt, mp_integer>;

mp_integer normalized(mp_integer value, const typet &type)
{
  if(type.id() == ID_bool)
    return value != 0 ? 1 : 0;
  const auto width = to_bitvector_type(type).get_width();
  const auto modulus = power(2, width);
  value %= modulus;
  if(value < 0)
    value += modulus;
  if(type.id() == ID_signedbv && value >= power(2, width - 1))
    value -= modulus;
  return value;
}

mp_integer eval(const exprt &expr, const valuest &values)
{
  if(expr.id() == ID_symbol)
    return values.at(to_symbol_expr(expr).get_identifier());
  if(expr.id() == ID_constant)
  {
    if(expr.type().id() == ID_bool)
      return expr.is_true() ? 1 : 0;
    mp_integer value;
    REQUIRE(!to_integer(to_constant_expr(expr), value));
    return value;
  }
  const auto left = eval(expr.operands()[0], values);
  if(expr.id() == ID_not)
    return left == 0 ? 1 : 0;
  if(expr.id() == ID_typecast)
    return normalized(left, expr.type());
  const auto right = eval(expr.operands()[1], values);
  if(expr.id() == ID_plus)
    return normalized(left + right, expr.type());
  if(expr.id() == ID_minus)
    return normalized(left - right, expr.type());
  if(expr.id() == ID_lt)
    return left < right ? 1 : 0;
  if(expr.id() == ID_le)
    return left <= right ? 1 : 0;
  if(expr.id() == ID_ge)
    return left >= right ? 1 : 0;
  if(expr.id() == ID_equal)
    return left == right ? 1 : 0;
  throw std::runtime_error("unsupported interpreter expression");
}

struct executiont
{
  valuest values;
  std::vector<bool> assertions;
  bool operator==(const executiont &other) const
  {
    return values == other.values && assertions == other.assertions;
  }
};

executiont execute(const goto_programt &program, valuest values)
{
  executiont result{std::move(values), {}};
  auto pc = program.instructions.begin();
  std::size_t steps = 0;
  while(pc != program.instructions.end())
  {
    REQUIRE(++steps < 10000);
    if(pc->is_assign())
      result.values[to_symbol_expr(pc->assign_lhs()).get_identifier()] =
        normalized(
          eval(pc->assign_rhs(), result.values), pc->assign_lhs().type());
    if(pc->is_assert())
      result.assertions.push_back(eval(pc->condition(), result.values) != 0);
    if(pc->is_goto() && eval(pc->condition(), result.values) != 0)
      pc = pc->get_target();
    else
      ++pc;
  }
  return result;
}

struct fixturet
{
  symbol_tablet symbols;
  goto_programt program;
  symbol_exprt counter, acc;
  goto_programt::targett init, head, body, step, back, exit;

  symbol_exprt symbol(const irep_idt &id, const typet &type)
  {
    symbolt entry{id, type, ID_C};
    entry.is_lvalue = true;
    REQUIRE(!symbols.add(entry));
    return entry.symbol_expr();
  }

  fixturet(
    typet acc_type = signedbv_typet(32),
    mp_integer start = 0,
    mp_integer bound = 5,
    mp_integer amount = 3,
    bool known_entry = true,
    mp_integer entry = 0,
    typet count_type = signedbv_typet(32))
    : counter(symbol("i", count_type)), acc(symbol("sum", acc_type))
  {
    if(known_entry)
      program.add(
        goto_programt::make_assignment(acc, from_integer(entry, acc_type)));
    init = program.add(
      goto_programt::make_assignment(counter, from_integer(start, count_type)));
    head = program.add_instruction(GOTO);
    head->condition_nonconst() = not_exprt(
      binary_relation_exprt(counter, ID_lt, from_integer(bound, count_type)));
    body = program.add(
      goto_programt::make_assignment(
        acc, plus_exprt(acc, from_integer(amount, acc_type))));
    step = program.add(
      goto_programt::make_assignment(
        counter, plus_exprt(counter, from_integer(1, count_type))));
    back = program.add_instruction(GOTO);
    back->condition_nonconst() = true_exprt();
    back->targets.push_back(head);
    exit = program.add(goto_programt::make_assertion(true_exprt()));
    head->targets.push_back(exit);
    program.add(goto_programt::make_end_function());
    program.update();
  }

  scalar_loop_summary_reportt summarize()
  {
    return summarize_scalar_loops(program, namespacet(symbols));
  }

  scalar_loop_summary_reportt
  equivalent(const std::vector<valuest> &inputs = {{}})
  {
    goto_programt original;
    original.copy_from(program);
    const auto report = summarize();
    if(report.summarized != 1)
    {
      for(const auto &line : report.diagnostics)
        std::cerr << line << '\n';
      throw std::runtime_error("expected exactly one summary");
    }
    for(const auto &input : inputs)
      REQUIRE(execute(original, input) == execute(program, input));
    for(const auto &instruction : program.instructions)
      if(instruction.is_goto())
        REQUIRE(
          instruction.get_target()->location_number >
          instruction.location_number);
    return report;
  }

  void retained()
  {
    std::vector<std::string> original;
    for(const auto &instruction : program.instructions)
      original.push_back(
        instruction.code().pretty() + (instruction.has_condition()
                                         ? instruction.condition().pretty()
                                         : std::string{}));
    REQUIRE(summarize().summarized == 0);
    std::vector<std::string> after;
    for(const auto &instruction : program.instructions)
      after.push_back(
        instruction.code().pretty() + (instruction.has_condition()
                                         ? instruction.condition().pretty()
                                         : std::string{}));
    REQUIRE(original == after);
  }
};
} // namespace

TEST_CASE(
  "Signed finite constant reduction preserves the exit state",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.equivalent();
}

TEST_CASE(
  "Empty finite loop preserves its counter exit and unrelated values",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), -3, 7, 1, false);
  f.body->turn_into_skip();
  f.exit->condition_nonconst() =
    equal_exprt(f.counter, from_integer(7, f.counter.type()));
  REQUIRE(f.equivalent({{{"sum", -5}}, {{"sum", 42}}}).empty_loops == 1);
}

TEST_CASE(
  "Empty zero-trip loop preserves the initial counter and failing assertion",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 7, 3, 1, false);
  f.body->turn_into_skip();
  f.exit->condition_nonconst() =
    equal_exprt(f.counter, from_integer(3, f.counter.type()));
  REQUIRE(f.equivalent({{{"sum", 42}}}).empty_loops == 1);
}

TEST_CASE(
  "Empty unsigned loop preserves its inclusive bound exit",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 250, 254, 1, false, 0, unsignedbv_typet(8));
  f.body->turn_into_skip();
  f.head->condition_nonconst() = not_exprt(binary_relation_exprt(
    f.counter, ID_le, from_integer(254, f.counter.type())));
  f.exit->condition_nonconst() =
    equal_exprt(f.counter, from_integer(255, f.counter.type()));
  REQUIRE(f.equivalent({{{"sum", 42}}}).empty_loops == 1);
}

TEST_CASE(
  "Empty loop with a volatile counter is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  typet type = signedbv_typet(32);
  type.set(ID_C_volatile, true);
  fixturet f(signedbv_typet(32), 0, 5, 1, false, 0, type);
  f.body->turn_into_skip();
  f.retained();
}

TEST_CASE(
  "Empty loop with an aliased counter is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.body->turn_into_skip();
  const auto pointer = f.symbol("p", pointer_typet(f.counter.type(), 64));
  f.program.insert_before(
    f.init,
    goto_programt::make_assignment(pointer, address_of_exprt(f.counter)));
  f.retained();
}

TEST_CASE(
  "Empty loop with an unknown bound is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.body->turn_into_skip();
  const auto bound = f.symbol("n", f.counter.type());
  f.head->condition_nonconst() =
    not_exprt(binary_relation_exprt(f.counter, ID_lt, bound));
  f.retained();
}

TEST_CASE(
  "Empty loop whose counter wraps is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 254, 255, 1, false, 0, unsignedbv_typet(8));
  f.body->turn_into_skip();
  f.head->condition_nonconst() = not_exprt(binary_relation_exprt(
    f.counter, ID_le, from_integer(255, f.counter.type())));
  f.retained();
}

TEST_CASE(
  "Empty loop with an external body entry is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.body->turn_into_skip();
  auto outside = f.program.insert_before(f.init);
  *outside = goto_programt::make_goto(f.body, true_exprt());
  f.retained();
}

TEST_CASE(
  "Loop containing a source assumption is not treated as empty",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  *f.body = goto_programt::make_assumption(false_exprt());
  f.retained();
}

TEST_CASE(
  "Negative counter starts and 64-bit accumulators preserve values",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(64), -4, 3, 42, true, -2);
  f.equivalent();
}

TEST_CASE(
  "Unsigned reductions preserve modular arithmetic for arbitrary entry values",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(unsignedbv_typet(32), 0, 5, mp_integer("4294967295"), false);
  f.equivalent(
    {{{"sum", 0}}, {{"sum", 1}}, {{"sum", mp_integer("4294967295")}}});
}

TEST_CASE(
  "Unknown signed accumulator is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 0, 5, 1, false);
  f.retained(); // Unknown signed accumulator may overflow.
}

TEST_CASE(
  "Positive signed overflow is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 0, 3, 1, true, mp_integer("2147483645"));
  f.retained();
}

TEST_CASE("Counter wrap is retained", "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 254, 255, 1, true, 0, unsignedbv_typet(8));
  f.head->condition_nonconst() = not_exprt(binary_relation_exprt(
    f.counter, ID_le, from_integer(255, f.counter.type())));
  f.retained(); // <= UINT8_MAX does not terminate without wrap.
}

TEST_CASE(
  "Address-taken accumulator is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  const auto pointer = f.symbol("p", pointer_typet(f.acc.type(), 64));
  f.program.insert_before(
    f.init, goto_programt::make_assignment(pointer, address_of_exprt(f.acc)));
  f.retained();
}

TEST_CASE(
  "Address-taken counter is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  const auto pointer = f.symbol("p", pointer_typet(f.counter.type(), 64));
  f.program.insert_before(
    f.init,
    goto_programt::make_assignment(pointer, address_of_exprt(f.counter)));
  f.retained();
}

TEST_CASE(
  "Volatile accumulator is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  typet type = signedbv_typet(32);
  type.set(ID_C_volatile, true);
  fixturet f(type);
  f.retained();
}

TEST_CASE(
  "Internal source assertions are retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.program.insert_before(f.step, goto_programt::make_assertion(false_exprt()));
  f.retained(); // Never remove even a failing internal assertion.
}

TEST_CASE(
  "Outside entry into the body is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  auto outside = f.program.insert_before(f.init);
  *outside = goto_programt::make_goto(f.body, true_exprt());
  f.retained();
}

TEST_CASE(
  "Accumulator-dependent loop bound is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 0, 5, -1, true, 5);
  f.head->condition_nonconst() =
    not_exprt(binary_relation_exprt(f.counter, ID_lt, f.acc));
  f.retained(); // Changing accumulator cannot supply an invariant bound.
}

TEST_CASE(
  "Mixed-width and narrowing arithmetic is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.body->assign_rhs_nonconst() = typecast_exprt(
    plus_exprt(
      typecast_exprt(f.acc, signedbv_typet(64)),
      from_integer(3, signedbv_typet(64))),
    f.acc.type());
  f.retained();
}

TEST_CASE(
  "Identity casts do not change the accumulator width",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.body->assign_rhs_nonconst() =
    typecast_exprt(f.body->assign_rhs(), f.acc.type());
  f.equivalent();
}

TEST_CASE(
  "Zero-trip loop preserves an unknown signed accumulator",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 6, 5, 1, false);
  f.equivalent({{{"sum", 9}}, {{"sum", -5}}});
}

TEST_CASE(
  "Direct canonical exit guard is supported",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.head->condition_nonconst() =
    binary_relation_exprt(f.counter, ID_ge, from_integer(5, f.counter.type()));
  f.equivalent();
}

TEST_CASE(
  "INT_MIN subtraction preserves a representable exact result",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 0, 1, 0, true, mp_integer("-2147483648"));
  f.body->assign_rhs_nonconst() =
    minus_exprt(f.acc, from_integer(mp_integer("-2147483648"), f.acc.type()));
  f.equivalent();
}

TEST_CASE(
  "Uninitialized bound on a reachable predecessor is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  const auto bound = f.symbol("n", f.counter.type());
  auto assign = f.program.insert_before(
    f.init,
    goto_programt::make_assignment(bound, from_integer(5, bound.type())));
  const auto condition = f.symbol("condition", bool_typet());
  auto branch = f.program.insert_before(assign);
  *branch = goto_programt::make_goto(f.init, condition);
  f.head->condition_nonconst() =
    not_exprt(binary_relation_exprt(f.counter, ID_lt, bound));
  f.retained(); // A reachable predecessor leaves the bound uninitialized.
}

TEST_CASE(
  "Constant minus accumulator is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.body->assign_rhs_nonconst() =
    minus_exprt(from_integer(3, f.acc.type()), f.acc);
  f.retained(); // constant - accumulator is not a constant additive step.
}

TEST_CASE(
  "Large positive total delta does not require a signed delta value",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(
    signedbv_typet(32),
    0,
    2,
    mp_integer("2147483647"),
    true,
    mp_integer("-2147483648"));
  f.equivalent(); // Positive total delta exceeds INT_MAX, final still fits.
}

TEST_CASE(
  "Large negative total delta does not require a signed delta value",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(
    signedbv_typet(32),
    0,
    2,
    mp_integer("-2147483647"),
    true,
    mp_integer("2147483647"));
  f.equivalent(); // Negative total delta is below INT_MIN, final still fits.
}

TEST_CASE(
  "Negative signed underflow is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f(signedbv_typet(32), 0, 3, -1, true, mp_integer("-2147483646"));
  f.retained(); // Negative monotone range would underflow.
}

TEST_CASE(
  "Outside entry after initialization is retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  auto location = f.program.insert_before(f.head);
  *location = goto_programt::make_location(source_locationt{});
  auto outside = f.program.insert_before(f.init);
  *outside = goto_programt::make_goto(location, true_exprt());
  f.retained(); // A harmless location cannot permit bypassing initialization.
}

TEST_CASE(
  "Outside entry at initialization is supported",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  auto outside = f.program.insert_before(f.init);
  *outside = goto_programt::make_goto(f.init, true_exprt());
  f.equivalent(); // An outside edge to the initialization itself is allowed.
}

TEST_CASE(
  "Failing source assertion at loop exit is preserved",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  f.exit->condition_nonconst() = false_exprt();
  f.equivalent(); // A failing source property at the exit stays observable.
}

TEST_CASE(
  "Conflicting reachable accumulator entries are retained",
  "[goto-btor2][scalar-loop-summary]")
{
  fixturet f;
  const auto condition = f.symbol("condition", bool_typet());
  const auto alternate = f.program.insert_before(
    f.init,
    goto_programt::make_assignment(f.acc, from_integer(100, f.acc.type())));
  auto branch = f.program.insert_before(alternate);
  *branch = goto_programt::make_goto(f.init, condition);
  f.retained(); // Conflicting reachable accumulator entries are not constants.
}

TEST_CASE(
  "Sequential signed reductions remain conservative until constants are "
  "exposed",
  "[goto-btor2][scalar-loop-summary]")
{
  const bool unsigned_acc = false;
  fixturet f(
    unsigned_acc ? typet(unsignedbv_typet(32)) : typet(signedbv_typet(32)));
  f.program.instructions.pop_back(); // Replace END_FUNCTION by a second loop.
  const auto j = f.symbol("j", signedbv_typet(32));
  f.program.add(goto_programt::make_assignment(j, from_integer(0, j.type())));
  const auto head = f.program.add_instruction(GOTO);
  head->condition_nonconst() =
    not_exprt(binary_relation_exprt(j, ID_lt, from_integer(4, j.type())));
  f.program.add(
    goto_programt::make_assignment(
      f.acc, minus_exprt(f.acc, from_integer(2, f.acc.type()))));
  f.program.add(
    goto_programt::make_assignment(
      j, plus_exprt(j, from_integer(1, j.type()))));
  f.program.add(goto_programt::make_goto(head, true_exprt()));
  const auto exit = f.program.add(
    goto_programt::make_assertion(
      equal_exprt(f.acc, from_integer(7, f.acc.type()))));
  head->targets.push_back(exit);
  f.program.add(goto_programt::make_end_function());
  f.program.update();
  goto_programt original;
  original.copy_from(f.program);
  const auto report = f.summarize();
  REQUIRE(report.summarized == (unsigned_acc ? 2 : 1));
  REQUIRE(execute(original, {}) == execute(f.program, {}));
  // Signed second-loop entry is not a constant until the first exact
  // summary has been exposed to the constant analysis. A second pass can
  // then certify it; the initial pass must remain conservative.
  if(!unsigned_acc)
  {
    REQUIRE(f.summarize().summarized == 1);
    REQUIRE(execute(original, {}) == execute(f.program, {}));
  }
}

TEST_CASE(
  "Sequential unsigned reductions are summarized in one pass",
  "[goto-btor2][scalar-loop-summary]")
{
  const bool unsigned_acc = true;
  fixturet f(
    unsigned_acc ? typet(unsignedbv_typet(32)) : typet(signedbv_typet(32)));
  f.program.instructions.pop_back(); // Replace END_FUNCTION by a second loop.
  const auto j = f.symbol("j", signedbv_typet(32));
  f.program.add(goto_programt::make_assignment(j, from_integer(0, j.type())));
  const auto head = f.program.add_instruction(GOTO);
  head->condition_nonconst() =
    not_exprt(binary_relation_exprt(j, ID_lt, from_integer(4, j.type())));
  f.program.add(
    goto_programt::make_assignment(
      f.acc, minus_exprt(f.acc, from_integer(2, f.acc.type()))));
  f.program.add(
    goto_programt::make_assignment(
      j, plus_exprt(j, from_integer(1, j.type()))));
  f.program.add(goto_programt::make_goto(head, true_exprt()));
  const auto exit = f.program.add(
    goto_programt::make_assertion(
      equal_exprt(f.acc, from_integer(7, f.acc.type()))));
  head->targets.push_back(exit);
  f.program.add(goto_programt::make_end_function());
  f.program.update();
  goto_programt original;
  original.copy_from(f.program);
  const auto report = f.summarize();
  REQUIRE(report.summarized == (unsigned_acc ? 2 : 1));
  REQUIRE(execute(original, {}) == execute(f.program, {}));
  // Signed second-loop entry is not a constant until the first exact
  // summary has been exposed to the constant analysis. A second pass can
  // then certify it; the initial pass must remain conservative.
  if(!unsigned_acc)
  {
    REQUIRE(f.summarize().summarized == 1);
    REQUIRE(execute(original, {}) == execute(f.program, {}));
  }
}
