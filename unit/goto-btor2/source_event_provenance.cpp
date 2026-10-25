#include <goto-btor2/source_event_provenance.h>
#include <ansi-c/ansi_c_language.h>
#include <langapi/mode.h>
#include <testing-utils/use_catch.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

namespace
{
struct fixturet
{
  symbol_tablet symbols;
  source_locationt source;

  fixturet()
  {
    static const bool language_registered = [] {
      register_language(new_ansi_c_language);
      return true;
    }();
    (void)language_registered;
    source.set_file("source.c");
    source.set_line(3);
    source.set_function("main");
  }

  symbol_exprt symbol(const std::string &name, const typet &type)
  {
    symbolt value{name, type, ID_C};
    value.base_name = name;
    value.is_lvalue = type.id() != ID_code;
    REQUIRE_FALSE(symbols.add(value));
    return value.symbol_expr();
  }

  exprt nondet(const typet &type, const typet &source_return)
  {
    symbol("__VERIFIER_nondet_value", code_typet({}, source_return));
    side_effect_expr_nondett result(type, source);
    result.set(ID_C_identifier, "__VERIFIER_nondet_value");
    return result;
  }
};
}

TEST_CASE("Canonical bool wrapper preserves source return", "[goto-btor2][source-event-provenance]")
{
  fixturet f;
  const c_bool_typet c_bool(8);
  const auto lhs = f.symbol("result", c_bool);
  const auto rhs = typecast_exprt(f.nondet(bool_typet(), c_bool), c_bool);
  goto_programt program;
  program.add(goto_programt::make_assignment(lhs, rhs, f.source));
  const auto call = btor2_source_nondet_call(program.instructions.front(), namespacet(f.symbols));
  REQUIRE(call.has_value());
  REQUIRE(call->value_preserving);
  REQUIRE(call->return_type == c_bool);
  btor2_source_provenancet provenance;
  btor2_capture_source_events(program, namespacet(f.symbols), provenance, "unit");
  REQUIRE(program.instructions.front().source_location().get_bool("c2btor_witness_value_root"));
  REQUIRE(provenance.original_events.size() == 1);
  REQUIRE(to_json_object(*provenance.original_events.begin())["nondet_function"].value == "__VERIFIER_nondet_value");
}

TEST_CASE("Identity wrapper preserves source integer return", "[goto-btor2][source-event-provenance]")
{
  fixturet f;
  const signedbv_typet integer(32);
  const auto lhs = f.symbol("result", integer);
  const auto rhs = typecast_exprt(f.nondet(integer, integer), integer);
  const auto instruction = goto_programt::make_assignment(lhs, rhs, f.source);
  const auto call = btor2_source_nondet_call(instruction, namespacet(f.symbols));
  REQUIRE(call.has_value());
  REQUIRE(call->value_preserving);
  REQUIRE(call->return_type == integer);
}

TEST_CASE("Narrowed wrapper cannot impersonate the source integer return", "[goto-btor2][source-event-provenance]")
{
  fixturet f;
  const signedbv_typet integer(32), narrowed(16);
  const auto lhs = f.symbol("result", narrowed);
  const auto rhs = typecast_exprt(f.nondet(integer, integer), narrowed);
  const auto instruction = goto_programt::make_assignment(lhs, rhs, f.source);
  const auto call = btor2_source_nondet_call(instruction, namespacet(f.symbols));
  REQUIRE(call.has_value());
  REQUIRE_FALSE(call->value_preserving);
  REQUIRE(call->return_type == integer);
  REQUIRE_FALSE(call->unsupported_reason.empty());
}

TEST_CASE("Integer-to-bool wrapper cannot impersonate the source integer return", "[goto-btor2][source-event-provenance]")
{
  fixturet f;
  const signedbv_typet integer(32);
  const c_bool_typet c_bool(8);
  const auto lhs = f.symbol("result", c_bool);
  const auto rhs = typecast_exprt(f.nondet(integer, integer), c_bool);
  const auto instruction = goto_programt::make_assignment(lhs, rhs, f.source);
  const auto call = btor2_source_nondet_call(instruction, namespacet(f.symbols));
  REQUIRE(call.has_value());
  REQUIRE_FALSE(call->value_preserving);
  REQUIRE(call->return_type == integer);
}
