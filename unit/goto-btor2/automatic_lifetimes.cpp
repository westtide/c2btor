#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <goto-btor2/automatic_lifetimes.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "Owner-disjoint lifetime effects",
  "[goto-btor2][automatic-lifetimes]")
{
  const auto saved = config.ansi_c;
  config.ansi_c.set_ILP32();
  symbol_tablet symbols;
  symbol_exprt owner{
    "owner", array_typet(unsignedbv_typet(8), from_integer(2, size_type()))};
  symbol_exprt pointer{"parameter", pointer_type(unsignedbv_typet(8))};
  symbols.add(symbolt{"owner", owner.type(), ID_C});
  symbolt parameter{"parameter", pointer.type(), ID_C};
  parameter.is_parameter = true;
  symbols.add(parameter);
  goto_programt program;
  auto start = program.add(goto_programt::make_decl(owner));
  program.add(goto_programt::make_decl(pointer));
  side_effect_exprt allocation(
    ID_allocate, pointer.type(), source_locationt::nil());
  allocation.operands() = {from_integer(1, size_type()), false_exprt()};
  program.add(goto_programt::make_assignment(pointer, allocation));
  bool expected = true;

  SECTION("inlined parameters can contain only fresh heap identities")
  {
    program.add(
      goto_programt::make_assumption(notequal_exprt(
        pointer, null_pointer_exprt(to_pointer_type(pointer.type())))));
  }
  SECTION("discarded heap identity queries cannot observe the owner")
  {
    program.add(
      goto_programt::make_other(
        code_expressiont(pointer_object_exprt(pointer, size_type()))));
  }
  SECTION("heap release cannot deactivate the automatic owner")
  {
    codet release("c2btor_deallocate");
    release.operands() = {pointer};
    program.add(goto_programt::make_other(release));
  }
  SECTION("unknown pointer inputs still prevent reuse")
  {
    program.add(
      goto_programt::make_assignment(
        pointer,
        side_effect_expr_nondett(pointer.type(), source_locationt::nil())));
    expected = false;
  }
  SECTION("an uninitialized inlined parameter has no provenance certificate")
  {
    program.add(goto_programt::make_dead(pointer));
    program.add(goto_programt::make_decl(pointer));
    program.add(
      goto_programt::make_other(
        code_expressiont(pointer_object_exprt(pointer, size_type()))));
    expected = false;
  }
  SECTION("a query of the owner identity still prevents reuse")
  {
    program.add(
      goto_programt::make_other(code_expressiont(
        pointer_object_exprt(address_of_exprt(owner), size_type()))));
    expected = false;
  }
  SECTION("escaping the owner identity still prevents reuse")
  {
    symbol_exprt global{"global", pointer_type(owner.type())};
    symbolt global_symbol{"global", global.type(), ID_C};
    global_symbol.is_static_lifetime = true;
    symbols.add(global_symbol);
    program.add(
      goto_programt::make_assignment(global, address_of_exprt(owner)));
    expected = false;
  }
  program.add(goto_programt::make_dead(pointer));
  program.add(goto_programt::make_dead(owner));
  program.add(goto_programt::make_goto(start));
  program.update();
  const bool certified = automatic_object_reuse_is_safe(
    program, namespacet(symbols), "owner", {"owner"});
  config.ansi_c = saved;
  REQUIRE(certified == expected);
}

TEST_CASE(
  "Unknown pointers outside an automatic lifetime",
  "[goto-btor2][automatic-lifetimes]")
{
  const auto saved = config.ansi_c;
  config.ansi_c.set_ILP32();
  symbol_tablet symbols;
  symbol_exprt owner{"owner", signedbv_typet(32)};
  symbol_exprt pointer{"pointer", pointer_type(owner.type())};
  symbols.add(symbolt{"owner", owner.type(), ID_C});
  symbols.add(symbolt{"pointer", pointer.type(), ID_C});
  goto_programt program;
  program.add(goto_programt::make_decl(pointer));
  program.add(
    goto_programt::make_assignment(
      pointer,
      side_effect_expr_nondett(pointer.type(), source_locationt::nil())));
  auto start = program.add(goto_programt::make_decl(owner));
  program.add(
    goto_programt::make_assignment(owner, from_integer(0, owner.type())));
  bool expected = true;
  SECTION("unrelated unknown values before and after the lifetime")
  {
  }
  SECTION("known other-object provenance can flow through a pointer")
  {
    symbol_exprt other{"other", owner.type()};
    symbolt other_symbol{"other", other.type(), ID_C};
    other_symbol.is_static_lifetime = true;
    symbols.add(other_symbol);
    program.add(
      goto_programt::make_assignment(pointer, address_of_exprt(other)));
    program.add(
      goto_programt::make_assignment(
        owner, dereference_exprt(pointer, owner.type())));
  }
  SECTION("an unknown scalar dereference during the lifetime prevents reuse")
  {
    program.add(
      goto_programt::make_assignment(
        owner, dereference_exprt(pointer, owner.type())));
    expected = false;
  }
  SECTION("an owner identity query during the lifetime prevents reuse")
  {
    program.add(
      goto_programt::make_other(code_expressiont(
        pointer_object_exprt(address_of_exprt(owner), size_type()))));
    expected = false;
  }
  SECTION("a may-live path cannot bypass the checks")
  {
    program.add(goto_programt::make_goto(start));
    expected = false;
  }
  program.add(goto_programt::make_dead(owner));
  program.add(
    goto_programt::make_other(
      code_expressiont(pointer_object_exprt(pointer, size_type()))));
  program.add(goto_programt::make_goto(start));
  program.update();
  const bool certified = automatic_object_reuse_is_safe(
    program, namespacet(symbols), "owner", {"owner", "other"});
  config.ansi_c = saved;
  REQUIRE(certified == expected);
}
