#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/config.h>
#include <util/json.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <ansi-c/ansi_c_language.h>
#include <goto-btor2/goto_btor2.h>
#include <json/json_parser.h>
#include <langapi/mode.h>
#include <testing-utils/use_catch.h>

#include "finite_btor2_replay.h"

#include <cstdint>
#include <map>
#include <sstream>
#include <stdexcept>

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

const jsont &block_at(const jsont &map, unsigned location)
{
  for(const auto &block : array(map["blocks"]))
    for(const auto &member : array(block["instructions"]))
      if(number(member) == location)
        return block;
  throw std::logic_error("missing runtime block");
}

unsigned state(const jsont &map, const std::string &symbol)
{
  for(const auto &entry : array(map["states"]))
    if(entry["symbol"].value == symbol)
      return number(entry["node"]);
  throw std::logic_error("missing source state");
}

struct fixturet
{
  configt::ansi_ct saved = config.ansi_c;
  symbol_tablet symbols;
  goto_functionst::goto_functiont function;
  null_message_handlert handler;
  messaget log{handler};
  const signedbv_typet integer{32};

  fixturet()
  {
    config.ansi_c.set_ILP32();
    if(!get_language_from_mode(ID_C))
      register_language(new_ansi_c_language);
  }
  ~fixturet()
  {
    config.ansi_c = saved;
  }
  symbol_exprt symbol(const char *id, const typet &type)
  {
    symbolt symbol{id, type, ID_C};
    symbol.is_lvalue = type.id() != ID_code;
    symbol.base_name = id;
    REQUIRE_FALSE(symbols.add(symbol));
    return symbol.symbol_expr();
  }
  exprt constant(unsigned value) const
  {
    return from_integer(value, integer);
  }
  goto_programt::targett add(goto_programt::instructiont instruction)
  {
    return function.body.add(std::move(instruction));
  }

  struct resultt
  {
    bool failed;
    std::string model, metadata;
    jsont map;
  };

  resultt convert(
    bool enabled = true,
    bool lbe = true,
    bool prune = false,
    bool source_map = true)
  {
    function.body.update();
    std::ostringstream model, metadata;
    btor2_optimization_optionst options;
    options.scalar_blocks = enabled;
    options.state_projection = prune;
    resultt result;
    result.failed = write_goto_function_btor2(
      function,
      "main",
      symbols,
      model,
      log,
      false,
      source_map ? &metadata : nullptr,
      0,
      {},
      {},
      lbe,
      scalar_projection_modet::NONE,
      options);
    result.model = model.str();
    result.metadata = metadata.str();
    if(!result.failed && source_map)
    {
      std::istringstream input(result.metadata);
      REQUIRE_FALSE(parse_json(input, "source map", handler, result.map));
    }
    return result;
  }
};

using btor2_test::trace_replayt;

} // namespace

TEST_CASE(
  "A final sequential self-loop repeats only its own assignment",
  "[goto-btor2][scalar-blocks]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  f.add(goto_programt::make_assertion(true_exprt{}));
  f.add(goto_programt::make_assignment(x, f.constant(0)));
  f.add(goto_programt::make_assignment(x, plus_exprt(x, f.constant(1))));
  const auto result = f.convert();
  REQUIRE_FALSE(result.failed);
  REQUIRE(array(block_at(result.map, 2)["instructions"]).size() == 1);
  trace_replayt trace(result.model);
  const auto x_node = state(result.map, "x");
  trace.step(); // selected assertion
  trace.step(); // x = 0
  trace.step(); // final x = x + 1
  REQUIRE(trace.value(x_node) == 1);
  trace.step();
  REQUIRE(trace.value(x_node) == 2);
  trace.step();
  REQUIRE(trace.value(x_node) == 3);
}

TEST_CASE(
  "Post counters retain distinct same-line source nondet identities",
  "[goto-btor2][witness-counters]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  const auto nondet =
    f.symbol("__VERIFIER_nondet_int", code_typet({}, f.integer));
  source_locationt source;
  source.set_file("source.c");
  source.set_line(3);
  source.set_column(10);
  source.set_function("main");
  f.add(goto_programt::make_function_call(x, nondet, {}, source));
  source.set_column(40);
  f.add(goto_programt::make_function_call(x, nondet, {}, source));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.constant(9))));
  f.add(goto_programt::make_end_function());
  const auto result = f.convert(true, true, true);
  REQUIRE_FALSE(result.failed);
  REQUIRE(result.map["witness_counter_format"].value == "post-counter-1");
  REQUIRE(result.map["optimization_config"]["array"].value == "bv");
  REQUIRE(result.map["optimization_config"]["scalar_blocks"].is_true());
  REQUIRE(result.map["optimization_config"]["optimize_state"].is_true());
  REQUIRE(result.map["optimization_config"]["property_slicing"].is_null());
  const auto &first = instruction(result.map, 0);
  const auto &second = instruction(result.map, 1);
  REQUIRE(first["source"]["line"].value == second["source"]["line"].value);
  REQUIRE(first["source"]["column"].value != second["source"]["column"].value);
  REQUIRE(array(first["original_event_ids"]).size() == 1);
  REQUIRE(array(second["original_event_ids"]).size() == 1);
  REQUIRE(
    number(*array(first["original_event_ids"]).begin()) !=
    number(*array(second["original_event_ids"]).begin()));
  const auto counter1 = number(first["counter_node"]);
  const auto counter2 = number(second["counter_node"]);
  REQUIRE(counter1 != counter2);
  REQUIRE(number(first["counter_width"]) == 8);
  REQUIRE(number(second["counter_width"]) == 8);
  trace_replayt trace(result.model);
  trace.input(number(first["value_node"]), 7);
  trace.input(number(second["value_node"]), 9);
  REQUIRE(trace.value(counter1) == 0);
  REQUIRE(trace.value(counter2) == 0);
  REQUIRE(trace.value(number(first["executed_node"])) == 1);
  REQUIRE(trace.value(number(second["executed_node"])) == 0);
  trace.step();
  REQUIRE(trace.value(counter1) == 1);
  REQUIRE(trace.value(counter2) == 0);
  // The last available frame can identify a call and its value without
  // requiring a next-frame counter assignment from the model checker.
  REQUIRE(trace.value(number(second["executed_node"])) == 1);
  REQUIRE(trace.value(number(second["value_node"])) == 9);
  trace.step();
  REQUIRE(trace.value(counter1) == 1);
  REQUIRE(trace.value(counter2) == 1);
  REQUIRE(trace.value(number(instruction(result.map, 2)["bad_condition_node"])) == 0);
}

TEST_CASE(
  "Post counters use actual branch guards and wrap modulo 256",
  "[goto-btor2][witness-counters]")
{
  fixturet f;
  const auto choice = f.symbol("choice", f.integer);
  const auto value = f.symbol("value", f.integer);
  const auto nondet =
    f.symbol("__VERIFIER_nondet_int", code_typet({}, f.integer));
  const auto call = f.add(goto_programt::make_function_call(choice, nondet, {}));
  const auto branch = f.add(goto_programt::make_skip());
  f.add(goto_programt::make_function_call(value, nondet, {}));
  f.add(goto_programt::make_assertion(equal_exprt(value, f.constant(9))));
  f.add(goto_programt::make_goto(call, true_exprt{}));
  const auto exit = f.add(goto_programt::make_end_function());
  *branch = goto_programt::make_goto(exit, notequal_exprt(choice, f.constant(0)));
  const auto result = f.convert(true, true, true);
  REQUIRE_FALSE(result.failed);
  const auto &first = instruction(result.map, 0);
  const auto &second = instruction(result.map, 2);
  const auto counter1 = number(first["counter_node"]);
  const auto counter2 = number(second["counter_node"]);
  trace_replayt skipped(result.model);
  skipped.input(number(first["value_node"]), 1);
  skipped.step();
  skipped.step();
  REQUIRE(skipped.value(counter1) == 1);
  REQUIRE(skipped.value(counter2) == 0);
  REQUIRE(skipped.value(number(second["executed_node"])) == 0);

  trace_replayt trace(result.model);
  trace.input(number(first["value_node"]), 0);
  trace.input(number(second["value_node"]), 9);
  unsigned first_calls = 0, second_calls = 0;
  for(unsigned frame = 0; second_calls < 260 && frame < 2000; ++frame)
  {
    REQUIRE(trace.value(counter1) == first_calls % 256);
    REQUIRE(trace.value(counter2) == second_calls % 256);
    first_calls += trace.value(number(first["executed_node"])).to_ulong();
    second_calls += trace.value(number(second["executed_node"])).to_ulong();
    trace.step();
  }
  REQUIRE(first_calls == 260);
  REQUIRE(second_calls == 260);
  REQUIRE(trace.value(counter1) == 4);
  REQUIRE(trace.value(counter2) == 4);
}

TEST_CASE(
  "Error aliases on one source line retain their original target names",
  "[goto-btor2][witness-counters]")
{
  fixturet f;
  source_locationt source;
  source.set_file("source.c");
  source.set_line(3);
  source.set_function("main");
  source.set_property_class("unreach-call");
  source.set_column(14);
  source.set("c2btor_error_function", "reach_error");
  f.add(goto_programt::make_assertion(false_exprt{}, source));
  source.set_column(34);
  source.set("c2btor_error_function", "__VERIFIER_error");
  f.add(goto_programt::make_assertion(false_exprt{}, source));
  f.add(goto_programt::make_end_function());
  const auto result = f.convert();
  REQUIRE_FALSE(result.failed);
  REQUIRE(instruction(result.map, 0)["error_function"].value == "reach_error");
  REQUIRE(instruction(result.map, 1)["error_function"].value == "__VERIFIER_error");
  const auto &properties = array(result.map["source_properties"]);
  REQUIRE(properties.size() == 2);
  auto property = properties.begin();
  REQUIRE((*property++)["error_function"].value == "reach_error");
  REQUIRE((*property)["error_function"].value == "__VERIFIER_error");
}

TEST_CASE(
  "Post counters are emitted only with the source map",
  "[goto-btor2][witness-counters]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  const auto nondet =
    f.symbol("__VERIFIER_nondet_int", code_typet({}, f.integer));
  f.add(goto_programt::make_function_call(x, nondet, {}));
  f.add(goto_programt::make_assumption(notequal_exprt(x, f.constant(0))));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.constant(9))));
  f.add(goto_programt::make_end_function());
  const auto without_map = f.convert(true, true, true, false);
  const auto with_map = f.convert(true, true, true);
  REQUIRE_FALSE(without_map.failed);
  REQUIRE_FALSE(with_map.failed);
  REQUIRE(without_map.metadata.empty());
  REQUIRE(without_map.model.find("__c2btor_nondet_count_") == std::string::npos);
  REQUIRE(with_map.model.find("__c2btor_nondet_count_") != std::string::npos);
  // Counters are observations and never occur in source properties.
  const auto counter = number(instruction(with_map.map, 0)["counter_node"]);
  const auto bad = number(instruction(with_map.map, 2)["bad_condition_node"]);
  REQUIRE(counter > bad);
  const auto properties = [](const std::string &model) {
    std::istringstream lines(model);
    std::string line;
    unsigned bad = 0, constraints = 0;
    while(std::getline(lines, line))
    {
      std::istringstream words(line);
      unsigned node;
      std::string operation;
      if(words >> node >> operation)
      {
        bad += operation == "bad";
        constraints += operation == "constraint";
      }
    }
    return std::make_pair(bad, constraints);
  };
  REQUIRE(properties(with_map.model) == std::make_pair(1u, 1u));
  REQUIRE(properties(without_map.model) == properties(with_map.model));
}

TEST_CASE(
  "A false final conditional backedge holds earlier scalar writes",
  "[goto-btor2][scalar-blocks]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  f.add(goto_programt::make_assertion(true_exprt{}));
  const auto increment =
    f.add(goto_programt::make_assignment(x, plus_exprt(x, f.constant(1))));
  f.add(goto_programt::make_goto(increment, false_exprt{}));
  const auto result = f.convert();
  REQUIRE_FALSE(result.failed);
  REQUIRE(array(block_at(result.map, 2)["instructions"]).size() == 1);
  trace_replayt trace(result.model);
  const auto x_node = state(result.map, "x");
  trace.step(); // selected assertion
  trace.step(); // increment once
  REQUIRE(trace.value(x_node) == 1);
  trace.step(); // conditional GOTO false: self-loop
  trace.step();
  REQUIRE(trace.value(x_node) == 1);
}

TEST_CASE(
  "A final unconditional backedge commits its scalar block each iteration",
  "[goto-btor2][scalar-blocks]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  f.add(goto_programt::make_assertion(true_exprt{}));
  const auto increment =
    f.add(goto_programt::make_assignment(x, plus_exprt(x, f.constant(1))));
  f.add(goto_programt::make_goto(increment));
  const auto result = f.convert();
  REQUIRE_FALSE(result.failed);
  const auto &loop = block_at(result.map, 1);
  REQUIRE(array(loop["instructions"]).size() == 2);
  REQUIRE(number(block_at(result.map, 2)["pc"]) == number(loop["pc"]));
  REQUIRE(array(loop["exit_instructions"]).size() == 1);
  REQUIRE(number(*array(loop["exit_instructions"]).begin()) == 1);
  trace_replayt trace(result.model);
  const auto x_node = state(result.map, "x");
  trace.step(); // selected assertion
  trace.step(); // x++ and backward GOTO in one transition
  REQUIRE(trace.value(x_node) == 1);
  trace.step();
  REQUIRE(trace.value(x_node) == 2);
  trace.step();
  REQUIRE(trace.value(x_node) == 3);
}

TEST_CASE(
  "Removing an unused scalar state cannot hide unsupported singleton RHS",
  "[goto-btor2][scalar-blocks]")
{
  fixturet f;
  const auto unused = f.symbol("unused", f.integer);
  f.add(goto_programt::make_assertion(true_exprt{}));
  f.add(
    goto_programt::make_assignment(
      unused, exprt("c2btor_missing_scalar_operator", f.integer)));
  for(const bool enabled : {false, true})
  {
    const auto result = f.convert(enabled);
    REQUIRE(result.failed);
    REQUIRE(result.model.empty());
    REQUIRE(result.metadata.empty());
  }
}

TEST_CASE(
  "Distinct verifier nondet sites sharing an LHS retain distinct inputs",
  "[goto-btor2][scalar-blocks]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  const auto nondet =
    f.symbol("__VERIFIER_nondet_int", code_typet({}, f.integer));
  f.add(goto_programt::make_function_call(x, nondet, {}));
  f.add(goto_programt::make_function_call(x, nondet, {}));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.constant(9))));
  f.add(goto_programt::make_end_function());
  const auto result = f.convert();
  REQUIRE_FALSE(result.failed);
  const auto first = number(instruction(result.map, 0)["value_node"]);
  const auto second = number(instruction(result.map, 1)["value_node"]);
  REQUIRE(first != second);
  REQUIRE(array(block_at(result.map, 0)["instructions"]).size() == 1);
  REQUIRE(array(block_at(result.map, 1)["instructions"]).size() == 1);
  const auto x_node = state(result.map, "x");
  REQUIRE(number(instruction(result.map, 0)["result_state_node"]) == x_node);
  REQUIRE(number(instruction(result.map, 1)["result_state_node"]) == x_node);
  trace_replayt trace(result.model);
  trace.input(first, 7);
  trace.input(second, 9);
  trace.step();
  REQUIRE(trace.value(x_node) == 7);
  trace.step();
  REQUIRE(trace.value(x_node) == 9);
  const auto bad = number(instruction(result.map, 2)["bad_condition_node"]);
  REQUIRE(trace.value(bad) == 0);
  trace.input(second, 8);
  // A changed input must not change the already-latched call result.
  REQUIRE(trace.value(x_node) == 9);
}

TEST_CASE(
  "A terminal scalar assertion observes latest values only on reached paths",
  "[goto-btor2][scalar-blocks]")
{
  fixturet f;
  const auto x = f.symbol("x", f.integer);
  const auto choice = f.symbol("choice", f.integer);
  const auto nondet =
    f.symbol("__VERIFIER_nondet_int", code_typet({}, f.integer));
  f.add(goto_programt::make_function_call(choice, nondet, {}));
  const auto branch = f.add(goto_programt::make_skip());
  f.add(goto_programt::make_assignment(x, f.constant(1)));
  f.add(goto_programt::make_assertion(equal_exprt(x, f.constant(0))));
  f.add(goto_programt::make_assignment(x, f.constant(2)));
  const auto exit = f.add(goto_programt::make_end_function());
  *branch =
    goto_programt::make_goto(exit, notequal_exprt(choice, f.constant(0)));
  const auto result = f.convert();
  REQUIRE_FALSE(result.failed);
  REQUIRE(array(block_at(result.map, 3)["instructions"]).size() == 3);
  const auto bad = number(instruction(result.map, 3)["bad_condition_node"]);
  const auto executed = number(instruction(result.map, 3)["pc_guard_node"]);
  for(const unsigned skip : {0u, 1u})
  {
    trace_replayt trace(result.model);
    trace.input(number(instruction(result.map, 0)["value_node"]), skip);
    trace.step(); // nondet call, then the scalar branch block
    REQUIRE(trace.value(executed) == (skip == 0));
    // x=1 is the latest in-block value: the reached x==0 assertion fails.
    REQUIRE(trace.value(bad) == (skip == 0));
    trace.step();
    if(skip == 0)
    {
      // ASSERT failure does not constrain execution or prevent the next write.
      REQUIRE(
        trace.value(number(instruction(result.map, 4)["pc_guard_node"])) == 1);
      REQUIRE(
        trace.value(number(instruction(result.map, 4)["value_node"])) == 2);
    }
    else
      REQUIRE(
        trace.value(number(instruction(result.map, 5)["pc_guard_node"])) == 1);
  }
}

TEST_CASE(
  "Scalar block optimization requires the public LBE option",
  "[goto-btor2][scalar-blocks]")
{
  fixturet f;
  f.add(goto_programt::make_assertion(true_exprt{}));
  const auto result = f.convert(true, false);
  REQUIRE(result.failed);
  REQUIRE(result.model.empty());
  REQUIRE(result.metadata.empty());
}
