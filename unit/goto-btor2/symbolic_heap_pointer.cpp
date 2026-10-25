#include <ansi-c/ansi_c_language.h>
#include <goto-btor2/goto_btor2.h>
#include <json/json_parser.h>
#include <langapi/mode.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include "finite_btor2_replay.h"

#include <sstream>
#include <stdexcept>

namespace
{
struct pointer_fixturet
{
  configt::ansi_ct saved = config.ansi_c;
  symbol_tablet symbols;
  goto_functionst::goto_functiont function;
  std::ostringstream diagnostics;
  stream_message_handlert handler{diagnostics};
  messaget log{handler};
  unsignedbv_typet size{32};
  signedbv_typet integer{32};
  pointer_typet pointer{signedbv_typet(64), 32};

  pointer_fixturet()
  {
    config.ansi_c.set_ILP32();
    config.ansi_c.endianness = configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
    if(!get_language_from_mode(ID_C))
      register_language(new_ansi_c_language);
  }
  ~pointer_fixturet()
  {
    config.ansi_c = saved;
  }
  symbol_exprt symbol(
    const char *id, const typet &type, const exprt &initializer = nil_exprt())
  {
    symbolt symbol{id, type, ID_C};
    symbol.is_lvalue = true;
    symbol.base_name = id;
    symbol.is_static_lifetime = initializer.is_not_nil();
    symbol.value = initializer;
    REQUIRE_FALSE(symbols.add(symbol));
    return symbol.symbol_expr();
  }
  void assign(const exprt &lhs, const exprt &rhs)
  {
    function.body.add(goto_programt::make_assignment(lhs, rhs));
  }
  void allocate(const symbol_exprt &p, const mp_integer &bytes)
  {
    side_effect_exprt allocation(ID_allocate, p.type(), source_locationt{});
    allocation.operands() = {from_integer(bytes, size), false_exprt()};
    assign(p, allocation);
  }
  struct resultt
  {
    bool failed;
    std::string model, diagnostics;
    jsont map;
  };
  resultt convert(const exprt &property = true_exprt())
  {
    function.body.add(goto_programt::make_assertion(property));
    function.body.add(goto_programt::make_end_function());
    function.body.update();
    array_encoding_optionst mode;
    mode.bitvectors = false;
    mode.symbolic_heap = mode.symbolic_heap_arrays = true;
    mode.symbolic_heap_wide_offsets = true;
    std::ostringstream model, metadata;
    resultt result;
    result.failed = write_goto_function_btor2(
      function, "main", symbols, model, log, false, &metadata, 0, mode);
    result.model = model.str();
    result.diagnostics = diagnostics.str();
    if(!result.failed)
    {
      std::istringstream stream(metadata.str());
      REQUIRE_FALSE(parse_json(stream, "source map", handler, result.map));
    }
    return result;
  }
};

unsigned state(const jsont &map, const char *symbol)
{
  for(const auto &entry : to_json_array(map["states"]))
    if(entry["symbol"].value == symbol)
      return std::stoul(entry["node"].value);
  throw std::logic_error("missing pointer test state");
}
} // namespace

TEST_CASE(
  "Wide pointer differences cross the machine sign bit",
  "[goto-btor2][symbolic-heap][symbolic-heap-pointer]")
{
  pointer_fixturet f;
  const auto p = f.symbol("p", f.pointer);
  const auto high = f.symbol("high", f.pointer);
  const auto low = f.symbol("low", f.pointer);
  const auto positive = f.symbol("positive", f.integer);
  const auto negative = f.symbol("negative", f.integer);
  f.allocate(p, (mp_integer(1) << 32) - 8);
  // The same object has offsets 0x80000000 and 0x7ffffff8. Both remain
  // aligned, in bounds, and only eight bytes apart for a long long pointer.
  f.assign(high, plus_exprt(p, from_integer(268435456, f.integer)));
  f.assign(low, plus_exprt(p, from_integer(268435455, f.integer)));
  auto forward = minus_exprt(high, low);
  forward.type() = f.integer;
  auto backward = minus_exprt(low, high);
  backward.type() = f.integer;
  f.assign(positive, forward);
  f.assign(negative, backward);
  const auto result = f.convert(and_exprt(
    equal_exprt(positive, from_integer(1, f.integer)),
    equal_exprt(negative, from_integer(-1, f.integer))));
  INFO(result.diagnostics);
  REQUIRE_FALSE(result.failed);
  REQUIRE(result.map["memory"]["pointer_width"].value == "32");
  REQUIRE(result.map["memory"]["offset_width"].value == "32");
  btor2_test::trace_replayt replay(result.model);
  for(unsigned step = 0; step < 5; ++step)
    replay.step();
  REQUIRE(replay.value(state(result.map, "positive")) == 1);
  REQUIRE(replay.value(state(result.map, "negative")) ==
          (mp_integer(1) << 32) - 1);
  const auto &properties = to_json_array(result.map["source_properties"]);
  REQUIRE(properties.size() == 1);
  REQUIRE(replay.value(
            std::stoul((*properties.begin())["condition_node"].value)) == 0);
}

TEST_CASE(
  "Wide scalar pointers retain null casts and copies",
  "[goto-btor2][symbolic-heap][symbolic-heap-pointer]")
{
  pointer_fixturet f;
  const auto p = f.symbol("p", f.pointer);
  const auto q = f.symbol("q", f.pointer);
  const auto copied = f.symbol("copied", f.pointer);
  const auto null = null_pointer_exprt(f.pointer);
  const auto global_null = f.symbol("global_null", f.pointer, null);
  const auto truth = f.symbol("truth", bool_typet());
  const auto falsehood = f.symbol("falsehood", bool_typet());
  const auto casted = f.symbol("casted", pointer_typet(empty_typet(), 32));
  f.allocate(p, (mp_integer(1) << 32) - 8);
  f.assign(q, if_exprt(true_exprt(), p, global_null));
  f.assign(copied, q);
  f.assign(truth, typecast_exprt(q, bool_typet()));
  f.assign(falsehood, typecast_exprt(global_null, bool_typet()));
  f.assign(casted, typecast_exprt(copied, casted.type()));
  const auto result = f.convert(and_exprt(
    truth, and_exprt(not_exprt(falsehood), equal_exprt(copied, p))));
  INFO(result.diagnostics);
  REQUIRE_FALSE(result.failed);
  btor2_test::trace_replayt replay(result.model);
  for(unsigned step = 0; step < 6; ++step)
    replay.step();
  const auto pointer = replay.value(state(result.map, "p"));
  REQUIRE(pointer != 0);
  REQUIRE(replay.value(state(result.map, "q")) == pointer);
  REQUIRE(replay.value(state(result.map, "copied")) == pointer);
  REQUIRE(replay.value(state(result.map, "casted")) == pointer);
  REQUIRE(replay.value(state(result.map, "global_null")) == 0);
  REQUIRE(replay.value(state(result.map, "truth")) == 1);
  REQUIRE(replay.value(state(result.map, "falsehood")) == 0);
}

TEST_CASE(
  "Wide pointers reject machine representation imports and serialization",
  "[goto-btor2][symbolic-heap][symbolic-heap-pointer]")
{
  pointer_fixturet f;
  const auto p = f.symbol("p", f.pointer);
  f.allocate(p, (mp_integer(1) << 32) - 8);
  SECTION("nonnull integer imports cannot discard or invent an object tag")
  {
    f.assign(p, typecast_exprt(from_integer(1, f.size), f.pointer));
  }
  SECTION("pointer integer exports cannot expose a hidden tag as C bytes")
  {
    const auto raw = f.symbol("raw", f.size);
    f.assign(raw, typecast_exprt(p, f.size));
  }
  SECTION("arbitrary pointer input has no machine byte representation")
  {
    f.assign(p, side_effect_expr_nondett(f.pointer, source_locationt{}));
  }
  SECTION("pointer loads through a char buffer are rejected")
  {
    const pointer_typet void_pointer(empty_typet(), 32);
    const auto loaded = f.symbol("loaded", void_pointer);
    const auto buffer = f.symbol(
      "buffer", array_typet(unsignedbv_typet(8), from_integer(4, f.size)));
    f.function.body.add(goto_programt::make_decl(buffer));
    const auto bytes = address_of_exprt(
      index_exprt(buffer, from_integer(0, f.integer)));
    const auto view = typecast_exprt(bytes, pointer_typet(void_pointer, 32));
    f.assign(loaded, dereference_exprt(view));
  }
  SECTION("pointer stores through a char buffer are rejected")
  {
    const pointer_typet void_pointer(empty_typet(), 32);
    const auto buffer = f.symbol(
      "buffer", array_typet(unsignedbv_typet(8), from_integer(4, f.size)));
    f.function.body.add(goto_programt::make_decl(buffer));
    const auto bytes = address_of_exprt(
      index_exprt(buffer, from_integer(0, f.integer)));
    const auto view = typecast_exprt(bytes, pointer_typet(void_pointer, 32));
    f.assign(dereference_exprt(view), typecast_exprt(p, void_pointer));
  }
  const auto result = f.convert();
  INFO(result.diagnostics);
  REQUIRE(result.failed);
  REQUIRE(result.model.empty());
  REQUIRE(result.diagnostics.find("wide-offset pointer representation") !=
          std::string::npos);
}
