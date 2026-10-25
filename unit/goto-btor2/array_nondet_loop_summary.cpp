#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <goto-btor2/array_loop_summary.h>
#include <goto-btor2/array_relation_pruning.h>
#include <testing-utils/use_catch.h>

#include <algorithm>
#include <string>
#include <vector>

namespace
{
bool contains_symbol(const exprt &expr, const irep_idt &id)
{
  if(expr.id() == ID_symbol && to_symbol_expr(expr).get_identifier() == id)
    return true;
  return std::any_of(
    expr.operands().begin(),
    expr.operands().end(),
    [&](const exprt &operand) { return contains_symbol(operand, id); });
}

struct nondet_fixturet
{
  symbol_tablet symbols;
  signedbv_typet integer{32};
  goto_programt program;
  symbol_exprt a, b, i, old;
  goto_programt::targett head;
  std::vector<irep_idt> samples;
  int limit = 4;

  symbol_exprt symbol(const irep_idt &id, const typet &type)
  {
    symbolt entry{id, type, ID_C};
    entry.is_lvalue = true;
    REQUIRE(!symbols.add(entry));
    return entry.symbol_expr();
  }

  nondet_fixturet()
    : a(symbol("a", array_typet(integer, from_integer(4, integer)))),
      b(symbol("b", array_typet(integer, from_integer(4, integer)))),
      i(symbol("i", integer)),
      old(symbol("old", integer))
  {
    for(const auto &value : {a, b, i, old})
      add(goto_programt::make_decl(value));
  }

  goto_programt::targett add(goto_programt::instructiont ins)
  {
    program.instructions.push_back(std::move(ins));
    return std::prev(program.instructions.end());
  }

  void
  insert_before(goto_programt::targett target, goto_programt::instructiont ins)
  {
    program.insert_before_swap(target, ins);
  }

  exprt at(const symbol_exprt &array, int index = 0) const
  {
    return index_exprt(array, from_integer(index, integer));
  }

  void start(int bound = 4, int initial = 0)
  {
    limit = bound;
    add(goto_programt::make_assignment(i, from_integer(initial, integer)));
    head = program.add_instruction(GOTO);
  }

  struct chunkt
  {
    symbol_exprt sample;
    goto_programt::targett declaration, input, store, dead;
  };

  chunkt chunk(const symbol_exprt &array, const exprt &index)
  {
    const auto value =
      symbol("sample" + std::to_string(samples.size()), integer);
    samples.push_back(value.get_identifier());
    const auto declaration = add(goto_programt::make_decl(value));
    const auto input = add(
      goto_programt::make_assignment(
        value, side_effect_expr_nondett(integer, source_locationt{})));
    const auto store =
      add(goto_programt::make_assignment(index_exprt(array, index), value));
    const auto dead = add(goto_programt::make_dead(value));
    return {value, declaration, input, store, dead};
  }

  void finish()
  {
    add(
      goto_programt::make_assignment(
        i, plus_exprt(i, from_integer(1, integer))));
    add(goto_programt::make_goto(head));
    const auto exit = program.add_instruction(LOCATION);
    *head = goto_programt::make_goto(
      exit,
      not_exprt(binary_relation_exprt(i, ID_lt, from_integer(limit, integer))));
  }

  void copy_loop(const symbol_exprt &destination, const symbol_exprt &source)
  {
    start();
    add(
      goto_programt::make_assignment(
        index_exprt(destination, i), index_exprt(source, i)));
    finish();
  }

  array_loop_summary_reportt
  check(bool accept, std::size_t roots = 1, std::size_t expected_copies = 0)
  {
    add(
      goto_programt::make_assertion(
        equal_exprt(i, from_integer(limit, integer))));
    add(goto_programt::make_assertion(equal_exprt(at(a), at(a))));
    program.add_instruction(END_FUNCTION);
    program.update();
    goto_programt original;
    original.copy_from(program);
    const auto count_assertions = [](const goto_programt &p)
    {
      std::size_t count = 0;
      for(const auto &ins : p.instructions)
        count += ins.is_assert();
      return count;
    };
    const auto properties = count_assertions(program);
    const auto report = summarize_array_loops(program, namespacet(symbols));
    REQUIRE(report.nondet_initializations == (accept ? 1 : 0));
    REQUIRE(report.copies == expected_copies);
    REQUIRE(count_assertions(program) == properties);
    if(!accept && !expected_copies)
      REQUIRE(program.equals(original));
    if(accept)
    {
      std::size_t fresh_inputs = 0;
      bool final_counter = false;
      for(const auto &ins : program.instructions)
      {
        if(ins.is_assign())
        {
          const auto &rhs = ins.assign_rhs();
          if(
            ins.assign_lhs().type().id() == ID_array &&
            rhs.id() == ID_side_effect && rhs.get(ID_statement) == ID_nondet)
          {
            ++fresh_inputs;
            REQUIRE(rhs.type() == ins.assign_lhs().type());
            REQUIRE(rhs.operands().empty());
          }
          if(
            ins.assign_lhs() == i &&
            ins.assign_rhs() == from_integer(limit, integer))
            final_counter = true;
        }
        for(const auto &sample : samples)
        {
          REQUIRE_FALSE(contains_symbol(ins.code(), sample));
          if(ins.has_condition())
            REQUIRE_FALSE(contains_symbol(ins.condition(), sample));
        }
      }
      REQUIRE(fresh_inputs == roots);
      REQUIRE(final_counter);
    }
    return report;
  }
};
} // namespace

TEST_CASE(
  "Independent nondet array initialization has closed samples and full "
  "coverage",
  "[goto-btor2][array-nondet-summary]")
{
  SECTION("single_root")
  {
    nondet_fixturet f;
    f.start();
    f.chunk(f.a, f.i);
    f.finish();
    f.check(true);
  }
  SECTION("two_independent_roots_in_one_loop")
  {
    nondet_fixturet f;
    f.start();
    f.chunk(f.a, f.i);
    f.chunk(f.b, f.i);
    f.finish();
    f.check(true, 2);
  }
  SECTION("root_order_can_differ_from_source_order")
  {
    nondet_fixturet f;
    f.start();
    f.chunk(f.b, f.i);
    f.chunk(f.a, f.i);
    f.finish();
    f.check(true, 2);
  }
  SECTION("two_independent_samples_tile_one_array")
  {
    nondet_fixturet f;
    f.start(2);
    const auto index = mult_exprt(from_integer(2, f.integer), f.i);
    f.chunk(f.a, index);
    f.chunk(f.a, plus_exprt(index, from_integer(1, f.integer)));
    f.finish();
    f.check(true);
  }
  SECTION("one_sample_cannot_feed_two_cells")
  {
    nondet_fixturet f;
    f.start(2);
    const auto index = mult_exprt(from_integer(2, f.integer), f.i);
    const auto chunk = f.chunk(f.a, index);
    f.insert_before(
      chunk.dead,
      goto_programt::make_assignment(
        index_exprt(f.a, plus_exprt(index, from_integer(1, f.integer))),
        chunk.sample));
    f.finish();
    f.check(false);
  }
  SECTION("one_sample_cannot_feed_two_arrays")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.insert_before(
      chunk.dead,
      goto_programt::make_assignment(index_exprt(f.b, f.i), chunk.sample));
    f.finish();
    f.check(false);
  }
  SECTION("missing_dead_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    chunk.dead->turn_into_skip();
    f.finish();
    f.check(false);
  }
  SECTION("temporary_observed_after_loop_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.finish();
    f.add(goto_programt::make_assignment(f.old, chunk.sample));
    f.check(false);
  }
  SECTION("temporary_in_later_condition_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.finish();
    f.add(
      goto_programt::make_assertion(
        equal_exprt(chunk.sample, from_integer(0, f.integer))));
    f.check(false);
  }
  SECTION("temporary_address_escape_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.finish();
    const auto p = f.symbol("p", pointer_typet(f.integer, 32));
    f.add(goto_programt::make_assignment(p, address_of_exprt(chunk.sample)));
    f.check(false);
  }
  SECTION("assume_on_sample_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.insert_before(
      chunk.dead,
      goto_programt::make_assumption(binary_relation_exprt(
        chunk.sample, ID_ge, from_integer(0, f.integer))));
    f.finish();
    f.check(false);
  }
  SECTION("source_assert_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.insert_before(chunk.dead, goto_programt::make_assertion(true_exprt()));
    f.finish();
    f.check(false);
  }
  SECTION("partial_coverage_is_retained")
  {
    nondet_fixturet f;
    f.start(3);
    f.chunk(f.a, f.i);
    f.finish();
    f.check(false);
  }
  SECTION("duplicate_offsets_are_retained")
  {
    nondet_fixturet f;
    f.start(2);
    const auto index = mult_exprt(from_integer(2, f.integer), f.i);
    f.chunk(f.a, index);
    f.chunk(f.a, index);
    f.finish();
    f.check(false);
  }
  SECTION("computed_sample_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    chunk.store->assign_rhs_nonconst() =
      plus_exprt(chunk.sample, from_integer(1, f.integer));
    f.finish();
    f.check(false);
  }
  SECTION("narrowing_sample_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    chunk.store->assign_rhs_nonconst() = typecast_exprt(
      typecast_exprt(chunk.sample, unsignedbv_typet(8)), f.integer);
    f.finish();
    f.check(false);
  }
  SECTION("nondet_with_operands_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    chunk.input->assign_rhs_nonconst().add_to_operands(
      from_integer(0, f.integer));
    f.finish();
    f.check(false);
  }
  SECTION("zero_trip_loop_is_retained")
  {
    nondet_fixturet f;
    f.start(0);
    f.chunk(f.a, f.i);
    f.finish();
    f.check(false);
  }
  SECTION("external_entry_into_chunk_is_retained")
  {
    nondet_fixturet f;
    const auto outside = f.program.add_instruction(GOTO);
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.finish();
    *outside = goto_programt::make_goto(chunk.input);
    f.check(false);
  }
  SECTION("temporary_in_expression_type_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.finish();
    const auto shaped =
      f.symbol("shaped", array_typet(f.integer, chunk.sample));
    f.add(goto_programt::make_decl(shaped));
    f.check(false);
  }
  SECTION("temporary_in_namespace_type_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.finish();
    const auto shaped =
      f.symbol("shaped", array_typet(f.integer, from_integer(4, f.integer)));
    f.symbols.get_writeable_ref(shaped.get_identifier()).type =
      array_typet(f.integer, chunk.sample);
    f.add(goto_programt::make_decl(shaped));
    f.check(false);
  }
  SECTION("temporary_in_static_namespace_initializer_is_retained")
  {
    nondet_fixturet f;
    f.start();
    const auto chunk = f.chunk(f.a, f.i);
    f.finish();
    const auto hidden = f.symbol("hidden", f.integer);
    auto &metadata = f.symbols.get_writeable_ref(hidden.get_identifier());
    metadata.is_static_lifetime = true;
    metadata.value = chunk.sample;
    f.add(
      goto_programt::make_assertion(
        equal_exprt(hidden, from_integer(0, f.integer))));
    f.check(false);
  }
  SECTION("new_array_remains_independent_of_old_scalar_read")
  {
    nondet_fixturet f;
    const auto save = f.add(goto_programt::make_assignment(f.old, f.at(f.a)));
    f.start();
    f.chunk(f.a, f.i);
    f.finish();
    f.check(true);
    REQUIRE(save->assign_rhs() == f.at(f.a));
  }
  SECTION("new_initialization_kills_old_copy_relation")
  {
    nondet_fixturet f;
    f.copy_loop(f.b, f.a);
    f.start();
    f.chunk(f.a, f.i);
    f.finish();
    const auto property =
      f.add(goto_programt::make_assertion(equal_exprt(f.at(f.a), f.at(f.b))));
    const auto report = f.check(true, 1, 1);
    REQUIRE(
      prune_equal_array_comparisons(
        f.program, namespacet(f.symbols), report.certified_arrays) == 0);
    REQUIRE(property->condition() == equal_exprt(f.at(f.a), f.at(f.b)));
  }
  SECTION("copy_after_new_initialization_establishes_relation")
  {
    nondet_fixturet f;
    f.start();
    f.chunk(f.a, f.i);
    f.finish();
    f.copy_loop(f.b, f.a);
    const auto property =
      f.add(goto_programt::make_assertion(equal_exprt(f.at(f.a), f.at(f.b))));
    const auto report = f.check(true, 1, 1);
    REQUIRE(
      prune_equal_array_comparisons(
        f.program, namespacet(f.symbols), report.certified_arrays) == 1);
    REQUIRE(property->condition() == true);
  }
}
