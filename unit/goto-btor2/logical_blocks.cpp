#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <ansi-c/ansi_c_language.h>
#include <goto-btor2/goto_btor2.h>
#include <json/json_parser.h>
#include <langapi/mode.h>
#include <testing-utils/use_catch.h>

#include "finite_btor2_replay.h"

#include <sstream>

namespace
{
unsigned number(const jsont &value)
{
  return std::stoul(value.value);
}
const json_arrayt &array(const jsont &value)
{
  REQUIRE(value.is_array());
  return static_cast<const json_arrayt &>(value);
}
const jsont &instruction(const jsont &map, unsigned location)
{
  for(const auto &entry : array(map["instructions"]))
    if(number(entry["instruction_id"]) == location)
      return entry;
  throw std::logic_error("missing source instruction");
}
unsigned block(const jsont &map, unsigned location)
{
  return number(instruction(map, location)["pc"]);
}
const jsont &logical_array(const jsont &map, const std::string &symbol)
{
  for(const auto &entry : array(map["memory"]["logical_arrays"]))
    if(entry["symbol"].value == symbol)
      return entry;
  throw std::logic_error("missing logical array");
}
unsigned input_named(const std::string &model, const std::string &name)
{
  std::istringstream lines(model);
  std::string line;
  unsigned result = 0;
  unsigned matches = 0;
  while(std::getline(lines, line))
  {
    std::istringstream words(line);
    unsigned id, sort;
    std::string operation, symbol;
    if(
      words >> id >> operation >> sort >> symbol && operation == "input" &&
      symbol == name)
    {
      result = id;
      ++matches;
    }
  }
  REQUIRE(matches == 1); // One activation input for one original DECL site.
  return result;
}

struct fixturet
{
  configt::ansi_ct saved = config.ansi_c;
  symbol_tablet symbols;
  goto_functionst::goto_functiont function;
  null_message_handlert handler;
  messaget log{handler};
  signedbv_typet integer{32};

  fixturet()
  {
    config.ansi_c.set_ILP32();
    config.ansi_c.endianness = configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
    if(!get_language_from_mode(ID_C))
      register_language(new_ansi_c_language);
  }
  ~fixturet()
  {
    config.ansi_c = saved;
  }
  symbol_exprt symbol(const char *id, const typet &type)
  {
    symbolt s{id, type, ID_C};
    s.is_lvalue = type.id() != ID_code;
    s.base_name = id;
    REQUIRE_FALSE(symbols.add(s));
    return s.symbol_expr();
  }
  symbol_exprt fixed_array(const char *id, unsigned size, const typet &leaf)
  {
    return symbol(id, array_typet(leaf, constant(size)));
  }
  exprt constant(unsigned value) const
  {
    return from_integer(value, integer);
  }
  index_exprt at(const exprt &root, const exprt &index) const
  {
    return index_exprt(root, index);
  }
  index_exprt at(const exprt &root, unsigned index) const
  {
    return at(root, constant(index));
  }
  goto_programt::targett add(goto_programt::instructiont instruction)
  {
    return function.body.add(std::move(instruction));
  }
  void nondet(const symbol_exprt &lhs)
  {
    if(!symbols.has_symbol("__VERIFIER_nondet_int"))
      symbol("__VERIFIER_nondet_int", code_typet({}, integer));
    add(
      goto_programt::make_function_call(
        lhs,
        symbol_exprt("__VERIFIER_nondet_int", code_typet({}, integer)),
        {}));
  }
  struct resultt
  {
    bool failed;
    std::string model, metadata;
    jsont map;
  };
  resultt convert(unsigned encoding, btor2_optimization_optionst options = {})
  {
    function.body.update();
    array_encoding_optionst arrays;
    arrays.bitvectors = encoding == 0;
    arrays.mixed = encoding == 2;
    // Each stage is enabled explicitly in normal cases below.
    std::ostringstream output, metadata;
    resultt result;
    result.failed = write_goto_function_btor2(
      function,
      "main",
      symbols,
      output,
      log,
      false,
      &metadata,
      0,
      arrays,
      {},
      true,
      scalar_projection_modet::NONE,
      options);
    result.model = output.str();
    result.metadata = metadata.str();
    if(!result.failed)
    {
      std::istringstream stream(result.metadata);
      REQUIRE_FALSE(parse_json(stream, "source map", handler, result.map));
    }
    return result;
  }
};

btor2_optimization_optionst optimized()
{
  btor2_optimization_optionst result;
  result.logical_arrays = true;
  result.scalar_blocks = true;
  result.array_blocks = true;
  return result;
}

using btor2_test::trace_replayt;
} // namespace

TEST_CASE(
  "Logical blocks read the latest store at equal dynamic indices",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 4, f.integer);
  const auto i = f.symbol("i", f.integer);
  const auto j = f.symbol("j", f.integer);
  const auto value = f.symbol("value", f.integer);
  f.nondet(i);
  f.nondet(j);
  f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_assignment(f.at(a, i), f.constant(7)));
  f.add(goto_programt::make_assignment(value, f.at(a, j)));
  f.add(goto_programt::make_assertion(equal_exprt(value, f.constant(7))));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    REQUIRE(block(result.map, 2) == block(result.map, 5));
    for(unsigned read_index : {1u, 2u})
    {
      trace_replayt trace(result.model);
      trace.input(number(instruction(result.map, 0)["value_node"]), 1);
      trace.input(number(instruction(result.map, 1)["value_node"]), read_index);
      trace.step();
      trace.step();
      REQUIRE(
        trace.value(number(instruction(result.map, 3)["value_node"])) == 7);
      REQUIRE(
        trace.value(number(instruction(result.map, 4)["value_node"])) ==
        (read_index == 1 ? 7 : 0));
      REQUIRE(
        trace.value(number(instruction(result.map, 5)["bad_condition_node"])) ==
        (read_index != 1));
    }
  }
}

TEST_CASE(
  "Logical block last writes and Boolean observations use typed leaf values",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  typet leaf = f.integer;
  SECTION("integer last write")
  {
  }
  SECTION("Boolean stores normalize their source-width observations")
  {
    leaf = c_bool_typet(8);
  }
  const bool boolean = leaf.id() == ID_c_bool;
  const auto a = f.fixed_array("a", 2, leaf);
  f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_assignment(f.at(a, 0), f.constant(7)));
  f.add(
    goto_programt::make_assignment(f.at(a, 0), f.constant(boolean ? 0 : 9)));
  f.add(
    goto_programt::make_assertion(
      equal_exprt(f.at(a, 0), from_integer(boolean ? 0 : 9, leaf))));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    trace_replayt trace(result.model);
    REQUIRE(
      trace.value(number(instruction(result.map, 1)["value_node"])) ==
      (boolean ? 1 : 7));
    REQUIRE(
      trace.value(number(instruction(result.map, 3)["bad_condition_node"])) ==
      0);
  }
}

TEST_CASE(
  "Logical block diamonds merge storage versions on their path guards",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 2, f.integer);
  const auto choice = f.symbol("choice", f.integer);
  f.nondet(choice);
  f.add(goto_programt::make_decl(a));
  const auto branch = f.add(goto_programt::make_skip());
  f.add(goto_programt::make_assignment(f.at(a, 0), f.constant(3)));
  const auto skip = f.add(goto_programt::make_skip());
  const auto alternative =
    f.add(goto_programt::make_assignment(f.at(a, 0), f.constant(7)));
  const auto assertion = f.add(
    goto_programt::make_assertion(equal_exprt(
      f.at(a, 0),
      if_exprt(
        notequal_exprt(choice, f.constant(0)), f.constant(7), f.constant(3)))));
  f.add(goto_programt::make_end_function());
  *branch = goto_programt::make_goto(
    alternative, notequal_exprt(choice, f.constant(0)));
  *skip = goto_programt::make_goto(assertion);
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    REQUIRE(block(result.map, 1) == block(result.map, 6));
    for(unsigned selected : {0u, 1u})
    {
      trace_replayt trace(result.model);
      trace.input(number(instruction(result.map, 0)["value_node"]), selected);
      trace.step();
      REQUIRE(
        trace.value(number(instruction(result.map, 3)["pc_guard_node"])) ==
        (selected == 0));
      REQUIRE(
        trace.value(number(instruction(result.map, 5)["pc_guard_node"])) ==
        (selected != 0));
      REQUIRE(
        trace.value(number(instruction(result.map, 6)["bad_condition_node"])) ==
        0);
    }
  }
}

TEST_CASE(
  "Logical block loop commits are not limited by a block-size budget",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 1, f.integer);
  const auto i = f.symbol("i", f.integer);
  f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_assignment(f.at(a, 0), f.constant(0)));
  f.add(goto_programt::make_assignment(i, f.constant(0)));
  const auto loop = f.add(
    goto_programt::make_assignment(
      f.at(a, 0), plus_exprt(f.at(a, 0), f.constant(1))));
  f.add(goto_programt::make_assignment(i, plus_exprt(i, f.constant(1))));
  f.add(
    goto_programt::make_goto(
      loop, binary_relation_exprt(i, ID_lt, f.constant(70))));
  f.add(goto_programt::make_assertion(equal_exprt(f.at(a, 0), f.constant(70))));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    REQUIRE(block(result.map, 3) == block(result.map, 5));
    trace_replayt trace(result.model);
    trace.step(); // initialization block
    for(unsigned iteration = 1; iteration <= 70; ++iteration)
    {
      REQUIRE(
        trace.value(number(instruction(result.map, 3)["value_node"])) ==
        iteration);
      trace.step();
    }
    REQUIRE(
      trace.value(number(instruction(result.map, 6)["pc_guard_node"])) == 1);
    REQUIRE(
      trace.value(number(instruction(result.map, 6)["bad_condition_node"])) ==
      0);
  }
}

TEST_CASE(
  "Logical DECL dimensions are latched from the latest scalar environment",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto n = f.symbol("n", f.integer);
  typet type = array_typet(f.integer, n);
  SECTION("one dimensional bound")
  {
  }
  SECTION("multidimensional flattening")
  {
    type = array_typet(type, f.constant(2));
  }
  const auto a = f.symbol("a", type);
  const bool multidimensional =
    to_array_type(type).element_type().id() == ID_array;
  const auto target = multidimensional ? f.at(f.at(a, 1), 0) : f.at(a, 1);
  f.add(goto_programt::make_assignment(n, f.constant(2)));
  f.add(goto_programt::make_decl(a));
  if(multidimensional)
    f.add(goto_programt::make_assignment(f.at(f.at(a, 0), 1), f.constant(0)));
  f.add(goto_programt::make_assignment(target, f.constant(7)));
  f.add(goto_programt::make_assignment(n, f.constant(1)));
  const auto assertion_location = multidimensional ? 5u : 4u;
  f.add(goto_programt::make_assertion(equal_exprt(target, f.constant(7))));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    REQUIRE(block(result.map, 0) == block(result.map, assertion_location));
    trace_replayt trace(result.model);
    REQUIRE(
      trace.value(number(instruction(
        result.map, assertion_location)["bad_condition_node"])) == 0);
    trace.step();
    for(const auto &dimension :
        array(logical_array(result.map, "a")["dimensions"]))
      if(dimension["state"].is_number())
        REQUIRE(trace.value(number(dimension["state"])) == 2);
  }
}

TEST_CASE(
  "Logical DECL reentry supplies fresh storage on every execution",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 1, f.integer);
  const auto count = f.symbol("count", f.integer);
  const auto old = f.symbol("old", f.integer);
  f.add(goto_programt::make_assignment(count, f.constant(0)));
  const auto loop = f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_assignment(old, f.at(a, 0)));
  f.add(
    goto_programt::make_assignment(f.at(a, 0), plus_exprt(old, f.constant(1))));
  f.add(
    goto_programt::make_assertion(
      equal_exprt(f.at(a, 0), plus_exprt(old, f.constant(1)))));
  f.add(
    goto_programt::make_assignment(count, plus_exprt(count, f.constant(1))));
  f.add(
    goto_programt::make_goto(
      loop, binary_relation_exprt(count, ID_lt, f.constant(2))));
  f.add(goto_programt::make_assertion(true_exprt{}));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    trace_replayt trace(result.model);
    const auto fresh = input_named(result.model, "__c2btor_elements_fresh$a$1");
    trace.step();
    for(unsigned seed : {5u, 9u})
    {
      trace.input(fresh, seed);
      REQUIRE(
        trace.value(number(instruction(result.map, 2)["value_node"])) == seed);
      REQUIRE(
        trace.value(number(instruction(result.map, 3)["value_node"])) ==
        seed + 1);
      REQUIRE(
        trace.value(number(instruction(result.map, 4)["bad_condition_node"])) ==
        0);
      trace.step(); // assertion completes normally
      trace.step(); // counter and backward edge
    }
  }
}

TEST_CASE(
  "Addressed arrays preserve physical storage and memory block boundaries",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 2, f.integer);
  const auto pointer = f.symbol("p", pointer_type(f.integer));
  f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_assignment(f.at(a, 0), f.constant(7)));
  f.add(goto_programt::make_assignment(pointer, address_of_exprt(f.at(a, 0))));
  f.add(
    goto_programt::make_assignment(
      dereference_exprt(pointer, f.integer), f.constant(9)));
  f.add(goto_programt::make_assertion(equal_exprt(f.at(a, 0), f.constant(9))));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    const auto &logical = result.map["memory"]["logical_arrays"];
    if(logical.is_array())
      REQUIRE(array(logical).empty());
    else
      REQUIRE(logical.is_null());
    const auto &objects = array(result.map["memory"]["objects"]);
    REQUIRE(objects.size() == 1);
    REQUIRE((*objects.begin())["symbol"].value == "a");
    for(unsigned location = 1; location <= 4; ++location)
      REQUIRE(block(result.map, location - 1) != block(result.map, location));
    trace_replayt trace(result.model);
    for(unsigned location = 0; location < 4; ++location)
      trace.step();
    REQUIRE(
      trace.value(number(instruction(result.map, 4)["pc_guard_node"])) == 1);
    REQUIRE(
      trace.value(number(instruction(result.map, 4)["bad_condition_node"])) ==
      0);
  }
}

TEST_CASE(
  "Logical diamonds merge captured dimensions with their storage version",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto n = f.symbol("n", f.integer);
  const auto choice = f.symbol("choice", f.integer);
  const auto a = f.symbol("a", array_typet(f.integer, n));
  f.nondet(choice);
  const auto branch = f.add(goto_programt::make_skip());
  f.add(goto_programt::make_assignment(n, f.constant(2)));
  f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_assignment(f.at(a, 1), f.constant(3)));
  const auto skip = f.add(goto_programt::make_skip());
  const auto alternative =
    f.add(goto_programt::make_assignment(n, f.constant(3)));
  f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_assignment(f.at(a, 1), f.constant(7)));
  const auto join = f.add(goto_programt::make_assignment(n, f.constant(1)));
  f.add(
    goto_programt::make_assertion(equal_exprt(
      f.at(a, 1),
      if_exprt(
        notequal_exprt(choice, f.constant(0)), f.constant(7), f.constant(3)))));
  f.add(goto_programt::make_end_function());
  *branch = goto_programt::make_goto(
    alternative, notequal_exprt(choice, f.constant(0)));
  *skip = goto_programt::make_goto(join);
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    REQUIRE(block(result.map, 1) == block(result.map, 10));
    const auto first = input_named(result.model, "__c2btor_elements_fresh$a$3");
    const auto second =
      input_named(result.model, "__c2btor_elements_fresh$a$7");
    REQUIRE(first != second);
    for(unsigned selected : {0u, 1u})
    {
      trace_replayt trace(result.model);
      trace.input(number(instruction(result.map, 0)["value_node"]), selected);
      trace.step();
      REQUIRE(
        trace.value(
          number(instruction(result.map, 10)["bad_condition_node"])) == 0);
      trace.step();
      const auto &dimensions =
        array(logical_array(result.map, "a")["dimensions"]);
      REQUIRE(dimensions.size() == 1);
      REQUIRE(
        trace.value(number(dimensions.begin()->operator[]("state"))) ==
        (selected ? 3 : 2));
    }
  }
}

TEST_CASE(
  "Whole-array nondeterminism remains a singleton storage snapshot",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 2, f.integer);
  f.add(goto_programt::make_decl(a));
  f.add(
    goto_programt::make_assignment(
      a, side_effect_expr_nondett(a.type(), source_locationt::nil())));
  f.add(goto_programt::make_assignment(f.at(a, 0), f.constant(7)));
  f.add(
    goto_programt::make_assertion(and_exprt(
      equal_exprt(f.at(a, 0), f.constant(7)),
      equal_exprt(f.at(a, 1), f.constant(23)))));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    REQUIRE(block(result.map, 0) != block(result.map, 1));
    REQUIRE(block(result.map, 1) != block(result.map, 2));
    REQUIRE(block(result.map, 2) == block(result.map, 3));
    trace_replayt trace(result.model);
    mp_integer seed = 23;
    if(logical_array(result.map, "a")["storage"].value == "bitvector")
      seed += mp_integer(23) << 32;
    trace.input(
      input_named(result.model, "__c2btor_elements_nondet$a$1"), seed);
    trace.step(); // DECL
    trace.step(); // Whole-array nondet assignment
    REQUIRE(
      trace.value(number(instruction(result.map, 3)["bad_condition_node"])) ==
      0);
  }
}

TEST_CASE(
  "Logical array subscripts can read another current logical storage version",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 2, f.integer);
  const auto b = f.fixed_array("b", 1, f.integer);
  f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_decl(b));
  f.add(goto_programt::make_assignment(f.at(b, 0), f.constant(1)));
  f.add(goto_programt::make_assignment(f.at(a, f.at(b, 0)), f.constant(7)));
  f.add(goto_programt::make_assertion(equal_exprt(f.at(a, 1), f.constant(7))));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    REQUIRE(block(result.map, 0) == block(result.map, 4));
    trace_replayt trace(result.model);
    REQUIRE(
      trace.value(number(instruction(result.map, 4)["bad_condition_node"])) ==
      0);
  }
}

TEST_CASE(
  "Unused logical storage still emits normalized element assignment "
  "observations",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 2, c_bool_typet(8));
  f.add(goto_programt::make_decl(a));
  f.add(goto_programt::make_assignment(f.at(a, 0), f.constant(9)));
  f.add(goto_programt::make_assertion(true_exprt{}));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    const auto result = f.convert(encoding, optimized());
    REQUIRE_FALSE(result.failed);
    REQUIRE(logical_array(result.map, "a")["unused_storage"].is_true());
    REQUIRE(logical_array(result.map, "a")["data_state"].is_null());
    trace_replayt trace(result.model);
    REQUIRE(trace.value(number(instruction(result.map, 1)["value_node"])) == 1);
  }
}

TEST_CASE(
  "Array blocks cannot accept an unsupported whole-array assignment",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  const auto a = f.fixed_array("a", 2, f.integer);
  f.add(goto_programt::make_decl(a));
  f.add(
    goto_programt::make_assignment(
      a, exprt("c2btor_missing_array_copy", a.type())));
  f.add(goto_programt::make_assertion(true_exprt{}));
  f.add(goto_programt::make_end_function());
  for(unsigned encoding : {0u, 1u, 2u})
  {
    auto flags = optimized();
    for(bool enabled : {false, true})
    {
      flags.array_blocks = enabled;
      const auto result = f.convert(encoding, flags);
      REQUIRE(result.failed);
      REQUIRE(result.model.empty());
      REQUIRE(result.metadata.empty());
    }
  }
}

TEST_CASE(
  "Public array block API requires logical arrays and scalar blocks",
  "[goto-btor2][logical-blocks]")
{
  fixturet f;
  f.add(goto_programt::make_assertion(true_exprt{}));
  for(unsigned missing : {0u, 1u})
  {
    auto flags = optimized();
    if(missing == 0)
      flags.logical_arrays = false;
    else
      flags.scalar_blocks = false;
    const auto result = f.convert(1, flags);
    REQUIRE(result.failed);
    REQUIRE(result.model.empty());
    REQUIRE(result.metadata.empty());
  }
}
