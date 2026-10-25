#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <goto-btor2/array_relation_pruning.h>
#include <testing-utils/use_catch.h>

#include <cstddef>
#include <utility>
#include <vector>

namespace
{
struct fixturet
{
  symbol_tablet symbols;
  signedbv_typet integer{32};
  array_typet type{integer, from_integer(4, integer)};
  symbol_exprt a{"a", type}, b{"b", type}, c{"c", type},
    choice{"choice", integer};
  goto_programt program;
  std::vector<std::pair<goto_programt::targett, bool>> expected_values;
  fixturet()
  {
    for(const auto &e : {a, b, c, choice})
    {
      symbolt s;
      s.name = e.get_identifier();
      s.type = e.type();
      s.is_lvalue = true;
      symbols.add(s);
      add(goto_programt::make_decl(e));
    }
  }
  goto_programt::targett add(goto_programt::instructiont ins)
  {
    program.instructions.push_back(std::move(ins));
    return std::prev(program.instructions.end());
  }
  goto_programt::targett
  copy(const symbol_exprt &dst, const symbol_exprt &src, bool certified = true)
  {
    code_assignt code(dst, src);
    code.set("c2btor_certified_array_copy", certified);
    return add(goto_programt::make_assignment(code));
  }
  exprt at(const symbol_exprt &array, int index = 0) const
  {
    return index_exprt(array, from_integer(index, integer));
  }
  void write(const symbol_exprt &array)
  {
    add(goto_programt::make_assignment(at(array), from_integer(7, integer)));
  }
  goto_programt::targett compare(
    const symbol_exprt &lhs,
    const symbol_exprt &rhs,
    bool neq = false,
    int left_index = 0,
    int right_index = 0,
    bool expect_rewrite = false)
  {
    const auto expr =
      neq ? exprt(notequal_exprt(at(lhs, left_index), at(rhs, right_index)))
          : exprt(equal_exprt(at(lhs, left_index), at(rhs, right_index)));
    auto instruction = add(goto_programt::make_assertion(expr));
    if(expect_rewrite)
      expected_values.emplace_back(instruction, !neq);
    return instruction;
  }
  exprt condition() const
  {
    return notequal_exprt(choice, from_integer(0, integer));
  }
  void check(std::size_t expected)
  {
    program.add_instruction(END_FUNCTION);
    program.update();
    std::size_t properties = 0;
    for(const auto &ins : program.instructions)
      properties += ins.is_assert();
    const auto result = prune_equal_array_comparisons(
      program, namespacet(symbols), {"a", "b", "c"});
    std::size_t after = 0;
    for(const auto &ins : program.instructions)
      after += ins.is_assert();
    REQUIRE(result == expected);
    REQUIRE(after == properties);
    for(const auto &pair : expected_values)
      REQUIRE(
        pair.first->condition() ==
        from_integer(pair.second ? 1 : 0, bool_typet()));
  }

  void check_reads(std::size_t expected)
  {
    program.add_instruction(END_FUNCTION);
    program.update();
    std::size_t properties = 0;
    for(const auto &ins : program.instructions)
      properties += ins.is_assert();
    REQUIRE(
      prune_equal_array_reads(program, namespacet(symbols), {"a", "b", "c"}) ==
      expected);
    std::size_t after = 0;
    for(const auto &ins : program.instructions)
      after += ins.is_assert();
    REQUIRE(after == properties);
  }
};
} // namespace

TEST_CASE(
  "Certified array copies propagate only must-equal corresponding cells",
  "[goto-btor2][array-relation-pruning]")
{
  SECTION("copy_equal_and_not_equal")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.compare(f.a, f.b, false, 0, 0, true);
    f.compare(f.b, f.a, true, 1, 1, true);
    f.check(2);
  }

  SECTION("copy_chain_transitive")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.c, f.b);
    f.compare(f.a, f.c, false, 2, 2, true);
    f.check(1);
  }

  SECTION("overwritten_destination")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.b, f.c);
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("source_mutation")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.write(f.a);
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("destination_mutation")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.write(f.b);
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("snapshot_relation_survives_old_source_mutation")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.c, f.b);
    f.write(f.a);
    f.compare(f.a, f.b);
    f.compare(f.b, f.c, false, 0, 0, true);
    f.check(1);
  }

  SECTION("self_copies_preserve_facts")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.a, f.a);
    f.copy(f.b, f.b);
    f.compare(f.a, f.b, false, 0, 0, true);
    f.check(1);
  }

  SECTION("self_copy_does_not_invent_relation")
  {
    fixturet f;
    f.copy(f.a, f.a);
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("lifetime_reset")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.add(goto_programt::make_dead(f.b));
    f.add(goto_programt::make_decl(f.b));
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("copy_does_not_dominate")
  {
    fixturet f;
    const auto branch = f.program.add_instruction(GOTO);
    f.copy(f.b, f.a);
    const auto join = f.compare(f.a, f.b);
    *branch = goto_programt::make_goto(join, f.condition());
    f.check(0);
  }

  SECTION("matching_branch_relations")
  {
    fixturet f;
    const auto branch = f.program.add_instruction(GOTO);
    f.copy(f.b, f.a);
    const auto jump = f.program.add_instruction(GOTO);
    const auto other = f.copy(f.b, f.a);
    const auto join = f.compare(f.a, f.b, false, 0, 0, true);
    *branch = goto_programt::make_goto(other, f.condition());
    *jump = goto_programt::make_goto(join);
    f.check(1);
  }

  SECTION("different_branch_relations")
  {
    fixturet f;
    const auto branch = f.program.add_instruction(GOTO);
    f.copy(f.b, f.a);
    const auto jump = f.program.add_instruction(GOTO);
    const auto other = f.copy(f.b, f.c);
    const auto join = f.compare(f.a, f.b);
    *branch = goto_programt::make_goto(other, f.condition());
    *jump = goto_programt::make_goto(join);
    f.check(0);
  }

  SECTION("destructive_backedge")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto loop = f.compare(f.a, f.b);
    f.write(f.a);
    f.add(goto_programt::make_goto(loop, f.condition()));
    f.check(0);
  }

  SECTION("reset_after_destructive_backedge")
  {
    fixturet f;
    const auto loop = f.copy(f.b, f.a);
    f.compare(f.a, f.b, false, 0, 0, true);
    f.write(f.a);
    f.add(goto_programt::make_goto(loop, f.condition()));
    f.check(1);
  }

  SECTION("first_iteration_has_no_relation")
  {
    fixturet f;
    const auto loop = f.compare(f.a, f.b);
    f.copy(f.b, f.a);
    f.add(goto_programt::make_goto(loop, f.condition()));
    f.check(0);
  }

  SECTION("assertions_do_not_establish_relations")
  {
    fixturet f;
    f.compare(f.a, f.b);
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("function_call_clears_relations")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const symbol_exprt unknown("unknown", code_typet({}, empty_typet()));
    f.add(goto_programt::make_function_call(code_function_callt(unknown)));
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("indirect_write_clears_relations")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const symbol_exprt p("p", pointer_typet(f.integer, 32));
    f.add(
      goto_programt::make_assignment(
        dereference_exprt(p), from_integer(1, f.integer)));
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("whole_fill_kills_destination_relations")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.add(
      goto_programt::make_assignment(
        f.b, array_of_exprt(from_integer(0, f.integer), f.type)));
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("unknown_effect")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.program.add_instruction(OTHER);
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("unmarked_whole_write_kills_relation")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.b, f.c, false);
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("unmarked_copy_cannot_establish_relation")
  {
    fixturet f;
    f.copy(f.b, f.a, false);
    f.compare(f.a, f.b);
    f.check(0);
  }

  SECTION("different_indices")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.compare(f.a, f.b, false, 0, 1);
    f.check(0);
  }

  SECTION("scalar_rhs_comparison")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.add(
      goto_programt::make_assignment(
        f.choice,
        typecast_exprt(equal_exprt(f.at(f.a), f.at(f.b)), f.integer)));
    f.check(1);
  }

  SECTION("branch_comparison")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto branch = f.program.add_instruction(GOTO);
    const auto exit = f.program.add_instruction(SKIP);
    *branch = goto_programt::make_goto(exit, equal_exprt(f.at(f.a), f.at(f.b)));
    f.check(1);
  }
}

TEST_CASE(
  "Must-equal array reads use one typed canonical root without changing writes",
  "[goto-btor2][array-relation-pruning][array-read-pruning]")
{
  SECTION("one_copy_canonicalizes_rhs")
  {
    fixturet f;
    const auto copy = f.copy(f.b, f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b, 2)));
    f.check_reads(1);
    REQUIRE(copy->assign_lhs() == f.b);
    REQUIRE(copy->assign_rhs() == f.a);
    REQUIRE(read->assign_rhs() == f.at(f.a, 2));
  }
  SECTION("copy_chain_has_one_canonical_root")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.c, f.b);
    const auto read = f.add(
      goto_programt::make_assignment(
        f.choice, plus_exprt(f.at(f.b, 1), f.at(f.c, 1))));
    f.check_reads(2);
    REQUIRE(read->assign_rhs() == plus_exprt(f.at(f.a, 1), f.at(f.a, 1)));
  }
  SECTION("copy_direction_does_not_determine_canonical_name")
  {
    fixturet f;
    f.copy(f.a, f.b);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.check_reads(1);
    REQUIRE(read->assign_rhs() == f.at(f.a));
  }
  SECTION("different_indices_are_preserved")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto read = f.add(
      goto_programt::make_assignment(
        f.choice, minus_exprt(f.at(f.b, 3), f.at(f.a, 1))));
    f.check_reads(1);
    REQUIRE(read->assign_rhs() == minus_exprt(f.at(f.a, 3), f.at(f.a, 1)));
  }
  SECTION("write_lvalue_keeps_its_original_root")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto write = f.add(
      goto_programt::make_assignment(
        f.at(f.b), plus_exprt(f.at(f.b), from_integer(1, f.integer))));
    const auto later =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.check_reads(1);
    REQUIRE(write->assign_lhs() == f.at(f.b));
    REQUIRE(
      write->assign_rhs() == plus_exprt(f.at(f.a), from_integer(1, f.integer)));
    REQUIRE(later->assign_rhs() == f.at(f.b));
  }
  SECTION("old_value_read_before_source_write_is_preserved")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto write =
      f.add(goto_programt::make_assignment(f.at(f.a), f.at(f.b)));
    f.check_reads(1);
    REQUIRE(write->assign_lhs() == f.at(f.a));
    REQUIRE(write->assign_rhs() == f.at(f.a));
  }
  SECTION("address_expression_is_not_an_element_read")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const symbol_exprt pointer("pointer", pointer_typet(f.integer, 32));
    const auto address = address_of_exprt(f.at(f.b));
    const auto assignment =
      f.add(goto_programt::make_assignment(pointer, address));
    f.check_reads(0);
    REQUIRE(assignment->assign_rhs() == address);
  }
  SECTION("overwritten_destination_has_no_old_relation")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.b, f.c);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.c)));
    f.check_reads(1);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("source_mutation_preserves_only_other_snapshot_members")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.c, f.b);
    f.write(f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.c)));
    f.check_reads(1);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("self_copy_preserves_existing_read_relation")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.copy(f.a, f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.check_reads(1);
    REQUIRE(read->assign_rhs() == f.at(f.a));
  }
  SECTION("conditions_are_canonicalized_without_assuming_the_assertion")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto property = f.compare(f.a, f.b);
    f.check_reads(1);
    REQUIRE(property->condition() == equal_exprt(f.at(f.a), f.at(f.a)));
    REQUIRE(property->condition() != true);
  }
  SECTION("assertion_cannot_create_a_read_relation")
  {
    fixturet f;
    f.compare(f.a, f.b);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.check_reads(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("lifetime_reset_kills_read_relation")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.add(goto_programt::make_dead(f.b));
    f.add(goto_programt::make_decl(f.b));
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.check_reads(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("non_dominating_copy_cannot_rewrite_read")
  {
    fixturet f;
    const auto branch = f.program.add_instruction(GOTO);
    f.copy(f.b, f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    *branch = goto_programt::make_goto(read, f.condition());
    f.check_reads(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("same_branch_copies_meet")
  {
    fixturet f;
    const auto branch = f.program.add_instruction(GOTO);
    f.copy(f.b, f.a);
    const auto jump = f.program.add_instruction(GOTO);
    const auto other = f.copy(f.b, f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    *branch = goto_programt::make_goto(other, f.condition());
    *jump = goto_programt::make_goto(read);
    f.check_reads(1);
    REQUIRE(read->assign_rhs() == f.at(f.a));
  }
  SECTION("different_branch_copies_do_not_meet")
  {
    fixturet f;
    const auto branch = f.program.add_instruction(GOTO);
    f.copy(f.b, f.a);
    const auto jump = f.program.add_instruction(GOTO);
    const auto other = f.copy(f.b, f.c);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    *branch = goto_programt::make_goto(other, f.condition());
    *jump = goto_programt::make_goto(read);
    f.check_reads(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("destructive_backedge_kills_global_array_equality")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.write(f.b);
    f.add(goto_programt::make_goto(read, f.condition()));
    f.check_reads(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("copy_at_each_loop_entry_restores_relation")
  {
    fixturet f;
    const auto loop = f.copy(f.b, f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.write(f.b);
    f.add(goto_programt::make_goto(loop, f.condition()));
    f.check_reads(1);
    REQUIRE(read->assign_rhs() == f.at(f.a));
  }
  SECTION("unknown_effect_kills_read_relation")
  {
    fixturet f;
    f.copy(f.b, f.a);
    f.program.add_instruction(OTHER);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.check_reads(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("unmarked_copy_cannot_create_read_relation")
  {
    fixturet f;
    f.copy(f.b, f.a, false);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.check_reads(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("namespace_type_mismatch_prevents_substitution")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.symbols.get_writeable_ref(f.a.get_identifier()).type =
      array_typet(f.integer, from_integer(8, f.integer));
    f.check_reads(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("comparison_api_does_not_canonicalize_general_reads")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const auto read =
      f.add(goto_programt::make_assignment(f.choice, f.at(f.b)));
    f.check(0);
    REQUIRE(read->assign_rhs() == f.at(f.b));
  }
  SECTION("read_only_paired_recurrences_share_the_same_element")
  {
    fixturet f;
    f.copy(f.b, f.a);
    const symbol_exprt sum1("sum1", f.integer), sum2("sum2", f.integer);
    f.add(goto_programt::make_assignment(f.choice, from_integer(0, f.integer)));
    const auto head = f.program.add_instruction(GOTO);
    f.add(
      goto_programt::make_assignment(
        sum1, plus_exprt(sum1, index_exprt(f.a, f.choice))));
    const auto second = f.add(
      goto_programt::make_assignment(
        sum2, plus_exprt(sum2, index_exprt(f.b, f.choice))));
    f.add(
      goto_programt::make_assignment(
        f.choice, plus_exprt(f.choice, from_integer(1, f.integer))));
    f.add(goto_programt::make_goto(head));
    const auto exit = f.program.add_instruction(LOCATION);
    *head = goto_programt::make_goto(
      exit,
      not_exprt(
        binary_relation_exprt(f.choice, ID_lt, from_integer(4, f.integer))));
    f.check_reads(1);
    REQUIRE(
      second->assign_rhs() == plus_exprt(sum2, index_exprt(f.a, f.choice)));
  }
}
