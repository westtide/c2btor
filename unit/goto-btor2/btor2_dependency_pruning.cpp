#include <goto-btor2/btor2_builder.h>
#include <testing-utils/use_catch.h>

#include <sstream>
#include <stdexcept>

// The public emitter uses positive references. Exercise the BTOR2 signed
// reference and justice grammars without adding a production raw-line API.
struct btor2_dependency_pruning_testt
{
  static btor2_nid_t line(btor2_buildert &builder, const std::string &text)
  {
    return builder.add_line(text);
  }
};

namespace
{
std::string text(const btor2_buildert &builder)
{
  std::ostringstream out;
  builder.write(out);
  return out.str();
}
} // namespace

TEST_CASE(
  "BTOR2 pruning removes unused state dependencies without renumbering",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  builder.comment("model provenance");
  const auto boolean = builder.get_bool_sort();
  const auto unused_sort = builder.get_or_create_bitvec_sort(16);
  const auto unused_zero = builder.zero(unused_sort);
  const auto unused_input = builder.input(unused_sort, "unused_input");
  const auto unused_state =
    builder.state(unused_sort, "unused", "source::dead");
  const auto unused_init = builder.init(unused_sort, unused_state, unused_zero);
  const auto unused_next =
    builder.next(unused_sort, unused_state, unused_input);
  const auto zero = builder.zero(boolean);
  const auto state = builder.state(boolean, "kept", "source::kept");
  const auto init = builder.init(boolean, state, zero);
  const auto next = builder.next(boolean, state, state);
  const auto bad = builder.bad(state);
  const auto high_water_mark = builder.get_node_count();

  const auto report = builder.prune_dependencies();
  REQUIRE(report.nodes_before == 12);
  REQUIRE(report.nodes_after == 6);
  REQUIRE(report.states_before == 2);
  REQUIRE(report.states_after == 1);
  REQUIRE(report.inputs_before == 1);
  REQUIRE(report.inputs_after == 0);
  const std::set<btor2_nid_t> expected = {
    boolean, zero, state, init, next, bad};
  REQUIRE(report.retained_nodes == expected);
  for(const auto id : expected)
    REQUIRE(builder.contains_node(id));
  for(const auto id :
      {unused_sort,
       unused_zero,
       unused_input,
       unused_state,
       unused_init,
       unused_next})
    REQUIRE_FALSE(builder.contains_node(id));
  REQUIRE_FALSE(builder.contains_node(0));
  REQUIRE_FALSE(builder.contains_node(high_water_mark + 1));
  REQUIRE(builder.get_node_count() == high_water_mark);

  const auto model = text(builder);
  REQUIRE(model.find("; model provenance") != std::string::npos);
  REQUIRE(
    model.find("; c2btor-source " + std::to_string(state) + " ") !=
    std::string::npos);
  REQUIRE(
    model.find("; c2btor-source " + std::to_string(unused_state) + " ") ==
    std::string::npos);
  REQUIRE(
    model.find(std::to_string(state) + " state " + std::to_string(boolean)) !=
    std::string::npos);

  // A repeated pass is stable, and sort caches cannot return a deleted ID.
  const auto repeated = builder.prune_dependencies();
  REQUIRE(repeated.nodes_before == report.nodes_after);
  REQUIRE(repeated.retained_nodes == expected);
  const auto replacement_sort = builder.get_or_create_bitvec_sort(16);
  REQUIRE(replacement_sort > high_water_mark);
  REQUIRE(builder.contains_node(replacement_sort));
}

TEST_CASE(
  "BTOR2 constraint fairness and output declarations are independent roots",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto boolean = builder.get_bool_sort();
  const auto constrained = builder.state(boolean, "constrained");
  const auto observed = builder.state(boolean, "observed");
  const auto fair = builder.input(boolean, "fair_input");
  const auto unused = builder.input(boolean, "unused");
  const auto constraint = builder.constraint(constrained);
  const auto output = builder.observed_output(boolean, observed, "observation");
  const auto fairness = builder.fair(fair);
  const auto constrained_next = builder.next(boolean, constrained, constrained);
  const auto observed_next = builder.next(boolean, observed, observed);

  const auto report = builder.prune_dependencies();
  for(const auto id :
      {boolean,
       constrained,
       observed,
       fair,
       constraint,
       output,
       fairness,
       constrained_next,
       observed_next})
    REQUIRE(report.retained_nodes.count(id) == 1);
  REQUIRE_FALSE(builder.contains_node(unused));
  REQUIRE(report.states_after == 2);
  REQUIRE(report.inputs_after == 1);
  REQUIRE(text(builder).find("observation") != std::string::npos);
}

TEST_CASE(
  "BTOR2 state dependency closure follows mutually recursive transitions",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto boolean = builder.get_bool_sort();
  const auto zero = builder.zero(boolean);
  const auto a = builder.state(boolean, "a");
  const auto b = builder.state(boolean, "b");
  const auto choice = builder.input(boolean, "choice");
  const auto a_init = builder.init(boolean, a, zero);
  const auto b_init = builder.init(boolean, b, zero);
  const auto a_next = builder.next(boolean, a, b);
  const auto b_value = builder.lxor(boolean, a, choice);
  const auto b_next = builder.next(boolean, b, b_value);
  const auto unused = builder.state(boolean, "unused");
  const auto unused_next = builder.next(boolean, unused, unused);
  builder.bad(a);

  const auto report = builder.prune_dependencies();
  for(const auto id :
      {boolean, zero, a, b, choice, a_init, b_init, a_next, b_value, b_next})
    REQUIRE(report.retained_nodes.count(id) == 1);
  REQUIRE_FALSE(builder.contains_node(unused));
  REQUIRE_FALSE(builder.contains_node(unused_next));
  REQUIRE(report.states_after == 2);
  REQUIRE(report.inputs_after == 1);
}

TEST_CASE(
  "BTOR2 array initializers keep element values and array seed states",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto index_sort = builder.get_or_create_bitvec_sort(2);
  const auto element_sort = builder.get_or_create_bitvec_sort(8);
  const auto array_sort = builder.sort_array(index_sort, element_sort);
  const auto index = builder.zero(index_sort);
  const auto initial_element = builder.zero(element_sort);
  btor2_nid_t initial_value = initial_element;
  btor2_nid_t seed_next = 0;
  SECTION("element constant initializes the complete array")
  {
  }
  SECTION("array-valued initializer reaches its seed transition")
  {
    initial_value = builder.state(array_sort, "seed");
    seed_next = builder.next(array_sort, initial_value, initial_value);
  }
  const auto array = builder.state(array_sort, "memory");
  const auto init = builder.init(array_sort, array, initial_value);
  const auto next = builder.next(array_sort, array, array);
  const auto read = builder.read(element_sort, array, index);
  builder.output(read);
  const auto report = builder.prune_dependencies();

  for(const auto id :
      {index_sort,
       element_sort,
       array_sort,
       index,
       initial_value,
       array,
       init,
       next,
       read})
    REQUIRE(report.retained_nodes.count(id) == 1);
  if(seed_next != 0)
  {
    REQUIRE(builder.contains_node(seed_next));
    REQUIRE_FALSE(builder.contains_node(initial_element));
  }
  REQUIRE(builder.has_array_sorts());
}

TEST_CASE(
  "BTOR2 pruning respects prior private array initializer simplification",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto index_sort = builder.get_or_create_bitvec_sort(2);
  const auto element_sort = builder.get_or_create_bitvec_sort(8);
  const auto array_sort = builder.sort_array(index_sort, element_sort);
  const auto index = builder.zero(index_sort);
  const auto seed = builder.state(array_sort, "private_seed");
  const auto seed_next = builder.next(array_sort, seed, seed);
  const auto array = builder.state(array_sort, "memory");
  const auto init = builder.memory_init(array_sort, array, seed);
  const auto next = builder.next(array_sort, array, array);
  builder.output(builder.read(element_sort, array, index));

  REQUIRE(builder.simplify_memory_initializers() == 1);
  REQUIRE_FALSE(builder.contains_node(init));
  const auto report = builder.prune_dependencies();
  REQUIRE_FALSE(builder.contains_node(seed));
  REQUIRE_FALSE(builder.contains_node(seed_next));
  REQUIRE(builder.contains_node(array));
  REQUIRE(builder.contains_node(next));
  REQUIRE(report.states_before == 2);
  REQUIRE(report.states_after == 1);
}

TEST_CASE(
  "BTOR2 signed references and justice roots preserve original sparse IDs",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto boolean = builder.get_bool_sort();
  const auto initial_value = builder.one(boolean);
  const auto unused = builder.input(boolean, "unused");
  const auto input = builder.input(boolean, "kept_input");
  const auto value = btor2_dependency_pruning_testt::line(
    builder, "not " + std::to_string(boolean) + " -" + std::to_string(input));
  const auto state = builder.state(boolean, "state");
  const auto init = btor2_dependency_pruning_testt::line(
    builder,
    "init " + std::to_string(boolean) + " " + std::to_string(state) + " -" +
      std::to_string(initial_value));
  const auto next = btor2_dependency_pruning_testt::line(
    builder,
    "next " + std::to_string(boolean) + " " + std::to_string(state) + " -" +
      std::to_string(value));
  const auto bad = btor2_dependency_pruning_testt::line(
    builder, "bad -" + std::to_string(state));
  const auto output = btor2_dependency_pruning_testt::line(
    builder, "output -" + std::to_string(value));
  const auto justice = btor2_dependency_pruning_testt::line(
    builder,
    "justice 2 -" + std::to_string(state) + " -" + std::to_string(input));

  const auto report = builder.prune_dependencies();
  const std::set<btor2_nid_t> expected = {
    boolean,
    initial_value,
    input,
    value,
    state,
    init,
    next,
    bad,
    output,
    justice};
  REQUIRE(report.retained_nodes == expected);
  REQUIRE_FALSE(builder.contains_node(unused));
  REQUIRE(builder.get_node_count() == justice);
  REQUIRE(
    text(builder).find(
      std::to_string(bad) + " bad -" + std::to_string(state)) !=
    std::string::npos);
}

TEST_CASE(
  "BTOR2 literal bounds and justice arity are not node dependencies",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto boolean = builder.get_bool_sort();
  const auto unused = builder.state(boolean, "unused");
  REQUIRE(unused == 2);
  const auto byte = builder.get_or_create_bitvec_sort(8);
  const auto input = builder.input(byte, "byte");
  const auto literal = builder.constd(byte, 2);
  const auto bit = builder.slice(boolean, input, 2, 2);
  const auto true_value = builder.one(boolean);
  builder.output(literal, "2");
  btor2_dependency_pruning_testt::line(
    builder,
    "justice 2 " + std::to_string(bit) + " " + std::to_string(true_value));

  const auto report = builder.prune_dependencies();
  REQUIRE_FALSE(builder.contains_node(unused));
  REQUIRE(builder.contains_node(input));
  REQUIRE(builder.contains_node(literal));
  REQUIRE(builder.contains_node(bit));
  REQUIRE(report.states_after == 0);
}

TEST_CASE(
  "BTOR2 explicit roots preserve otherwise unobserved state functions",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto boolean = builder.get_bool_sort();
  const auto input = builder.input(boolean);
  const auto state = builder.state(boolean);
  const auto next = builder.next(boolean, state, input);
  const auto unused = builder.state(boolean);
  const auto report = builder.prune_dependencies({state});
  const std::set<btor2_nid_t> expected = {boolean, input, state, next};
  REQUIRE(report.retained_nodes == expected);
  REQUIRE_FALSE(builder.contains_node(unused));
}

TEST_CASE(
  "BTOR2 dependency pruning rejects incomplete graphs before mutating them",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto boolean = builder.get_bool_sort();
  const auto state = builder.state(boolean);
  std::vector<btor2_nid_t> extra_roots;
  SECTION("missing expression reference")
  {
    builder.bad(builder.get_node_count() + 100);
  }
  SECTION("unknown operation")
  {
    btor2_dependency_pruning_testt::line(
      builder,
      "future_operator " + std::to_string(boolean) + " " +
        std::to_string(state));
  }
  SECTION("missing explicit root")
  {
    extra_roots.push_back(builder.get_node_count() + 100);
  }
  SECTION("wrong reference kind")
  {
    builder.bad(boolean);
  }
  const auto before = text(builder);
  REQUIRE_THROWS_AS(builder.prune_dependencies(extra_roots), std::logic_error);
  REQUIRE(text(builder) == before);
  REQUIRE(builder.contains_node(state));
}

TEST_CASE(
  "BTOR2 pruning with no roots removes all numeric declarations",
  "[goto-btor2][dependency-pruning]")
{
  btor2_buildert builder;
  const auto index = builder.get_or_create_bitvec_sort(2);
  const auto element = builder.get_or_create_bitvec_sort(8);
  const auto array = builder.sort_array(index, element);
  const auto state = builder.state(array, "unused", "unused_source");
  builder.next(array, state, state);
  const auto report = builder.prune_dependencies();
  REQUIRE(report.nodes_before == 5);
  REQUIRE(report.nodes_after == 0);
  REQUIRE_FALSE(builder.has_array_sorts());
  REQUIRE_FALSE(builder.contains_node(state));
  REQUIRE(text(builder).empty());
}
