#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-btor2/scalar_block_liveness.h>
#include <testing-utils/use_catch.h>

namespace
{
struct fixturet
{
  symbol_tablet symbols;
  goto_programt program;
  const signedbv_typet integer{32};
  std::map<unsigned, std::vector<unsigned>> successors;

  symbol_exprt symbol(const irep_idt &id, const typet &type)
  {
    symbolt value{id, type, ID_C};
    value.is_lvalue = true;
    REQUIRE_FALSE(symbols.add(value));
    return value.symbol_expr();
  }

  exprt number(unsigned value) const
  {
    return from_integer(value, integer);
  }

  void add(goto_programt::instructiont instruction)
  {
    program.add(std::move(instruction));
  }

  scalar_block_liveness_reportt classify(
    const std::vector<std::vector<unsigned>> &blocks,
    const std::set<irep_idt> &candidates)
  {
    program.update();
    return classify_scalar_block_state(
      program, namespacet(symbols), blocks, candidates, successors);
  }
};
} // namespace

TEST_CASE(
  "Scalar values defined before every in-block use need no state",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  const auto y = f.symbol("y", f.integer);
  f.add(goto_programt::make_decl(x));
  f.add(goto_programt::make_decl(y));
  f.add(goto_programt::make_assignment(x, f.number(1)));
  f.add(goto_programt::make_assignment(y, plus_exprt(x, f.number(2))));
  f.add(goto_programt::make_assertion(equal_exprt(y, f.number(3))));
  f.add(goto_programt::make_end_function());
  f.successors = {{0, {1}}, {1, {2}}, {2, {3}}, {3, {4}}, {4, {5}}, {5, {5}}};
  const auto result = f.classify({{0, 1, 2, 3, 4}, {5}}, {"x", "y"});
  REQUIRE(result.persistent_symbols.empty());
  REQUIRE(result.local_symbols == std::set<irep_idt>{"x", "y"});
  REQUIRE(result.entry_live.at(0).empty());
}

TEST_CASE(
  "Scalar liveness retains values crossing a block boundary",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  const auto temporary = f.symbol("temporary", f.integer);
  f.add(goto_programt::make_assignment(x, f.number(1)));
  f.add(goto_programt::make_assignment(temporary, plus_exprt(x, f.number(2))));
  f.add(goto_programt::make_assertion(equal_exprt(temporary, f.number(3))));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.number(1))));
  f.successors = {{0, {1}}, {1, {2}}, {2, {3}}, {3, {3}}};
  const auto result = f.classify({{0, 1, 2}, {3}}, {"x", "temporary"});
  REQUIRE(result.persistent_symbols == std::set<irep_idt>{"x"});
  REQUIRE(result.local_symbols == std::set<irep_idt>{"temporary"});
  REQUIRE(result.entry_live.at(3).count("x") == 1);
}

TEST_CASE(
  "Loop fixed points retain carried values and eliminate iteration "
  "temporaries",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto carried = f.symbol("carried", f.integer);
  const auto temporary = f.symbol("temporary", f.integer);
  f.add(goto_programt::make_assignment(carried, f.number(0)));
  f.add(goto_programt::make_decl(temporary));
  f.add(
    goto_programt::make_assignment(
      temporary, plus_exprt(carried, f.number(1))));
  f.add(goto_programt::make_assignment(carried, temporary));
  f.add(goto_programt::make_skip());
  f.add(goto_programt::make_assertion(equal_exprt(carried, f.number(3))));
  f.add(goto_programt::make_end_function());
  // The supplied converter CFG is authoritative, even though instruction 4
  // is a synthetic SKIP rather than a frontend GOTO in this unit fixture.
  f.successors = {
    {0, {1}}, {1, {2}}, {2, {3}}, {3, {4}}, {4, {1, 5}}, {5, {6}}, {6, {6}}};
  const auto result =
    f.classify({{0}, {1, 2, 3, 4}, {5}, {6}}, {"carried", "temporary"});
  REQUIRE(result.persistent_symbols == std::set<irep_idt>{"carried"});
  REQUIRE(result.local_symbols == std::set<irep_idt>{"temporary"});
  REQUIRE(result.entry_live.at(1).count("carried") == 1);
  REQUIRE(result.entry_live.at(1).count("temporary") == 0);
}

TEST_CASE(
  "A skipped scalar definition retains its entry value",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto condition = f.symbol("condition", bool_typet{});
  const auto x = f.symbol("x", f.integer);
  f.add(goto_programt::make_assertion(condition));
  f.add(goto_programt::make_decl(x));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.number(0))));
  f.add(goto_programt::make_end_function());
  f.successors = {{0, {1, 2}}, {1, {2}}, {2, {3}}, {3, {3}}};
  const auto result = f.classify({{0, 1, 2}, {3}}, {"x", "condition"});
  REQUIRE(result.persistent_symbols.count("x") == 1);
  REQUIRE(result.entry_live.at(0).count("x") == 1);
  REQUIRE(result.local_symbols.empty());
}

TEST_CASE(
  "Definitions on both diamond paths permit a local scalar value",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto condition = f.symbol("condition", bool_typet{});
  const auto x = f.symbol("x", f.integer);
  f.add(goto_programt::make_assertion(condition));
  f.add(goto_programt::make_assignment(x, f.number(1)));
  f.add(goto_programt::make_skip());
  f.add(goto_programt::make_assignment(x, f.number(2)));
  f.add(
    goto_programt::make_assertion(
      binary_relation_exprt(x, ID_ge, f.number(1))));
  f.add(goto_programt::make_end_function());
  f.successors = {
    {0, {1, 3}}, {1, {2}}, {2, {4}}, {3, {4}}, {4, {5}}, {5, {5}}};
  const auto result = f.classify({{0, 1, 2, 3, 4}, {5}}, {"x", "condition"});
  REQUIRE(result.local_symbols == std::set<irep_idt>{"x"});
  REQUIRE(result.persistent_symbols == std::set<irep_idt>{"condition"});
  REQUIRE(result.entry_live.at(0).count("x") == 0);
}

TEST_CASE(
  "Scalar DEAD does not erase a value needed by a later property",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  f.add(goto_programt::make_assignment(x, f.number(1)));
  f.add(goto_programt::make_dead(x));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.number(1))));
  f.successors = {{0, {1}}, {1, {2}}, {2, {2}}};
  const auto result = f.classify({{0}, {1}, {2}}, {"x"});
  REQUIRE(result.persistent_symbols == std::set<irep_idt>{"x"});
  REQUIRE(result.entry_live.at(1).count("x") == 1);
}

TEST_CASE(
  "Type-only array dimensions are reads at their instruction boundary",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto n = f.symbol("n", f.integer);
  const auto array = f.symbol("array", array_typet(f.integer, n));
  f.add(goto_programt::make_assignment(n, f.number(4)));
  f.add(goto_programt::make_decl(array));
  f.add(goto_programt::make_assertion(true_exprt{}));
  f.successors = {{0, {1}}, {1, {2}}, {2, {2}}};
  const auto result = f.classify({{0}, {1}, {2}}, {"n"});
  REQUIRE(result.persistent_symbols == std::set<irep_idt>{"n"});
  REQUIRE(result.entry_live.at(1).count("n") == 1);
}

TEST_CASE(
  "Explicit sizeof type attributes preserve dimension reads",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto n = f.symbol("n", f.integer);
  const auto value = f.symbol("value", f.integer);
  auto size = f.number(16);
  size.set(ID_C_c_sizeof_type, array_typet(f.integer, n));
  f.add(goto_programt::make_assignment(n, f.number(4)));
  f.add(goto_programt::make_assignment(value, size));
  f.add(goto_programt::make_assertion(equal_exprt(value, f.number(16))));
  f.successors = {{0, {1}}, {1, {2}}, {2, {2}}};
  const auto result = f.classify({{0}, {1}, {2}}, {"n", "value"});
  REQUIRE(result.persistent_symbols.count("n") == 1);
  REQUIRE(result.entry_live.at(1).count("n") == 1);
}

TEST_CASE(
  "Unknown custom operations do not define their scalar operands",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  f.add(goto_programt::make_assignment(x, f.number(1)));
  codet unknown("unknown_effect", {x});
  f.add(goto_programt::make_other(unknown));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.number(1))));
  f.successors = {{0, {1}}, {1, {2}}, {2, {2}}};
  const auto result = f.classify({{0}, {1}, {2}}, {"x"});
  REQUIRE(result.persistent_symbols == std::set<irep_idt>{"x"});
  REQUIRE(result.entry_live.at(1).count("x") == 1);
}

TEST_CASE(
  "Incomplete caller CFG conservatively retains candidate state",
  "[goto-btor2][scalar-block-liveness]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  f.add(goto_programt::make_assignment(x, f.number(1)));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.number(1))));
  f.successors = {{0, {1}}};
  const auto result = f.classify({{0, 1}}, {"x"});
  REQUIRE(result.persistent_symbols == std::set<irep_idt>{"x"});
  REQUIRE(result.local_symbols.empty());
  REQUIRE(result.entry_live.at(0).count("x") == 1);
}
