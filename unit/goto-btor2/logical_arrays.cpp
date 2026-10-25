#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-btor2/array_loop_summary.h>
#include <goto-btor2/expr_to_btor2.h>
#include <goto-btor2/goto_btor2.h>
#include <goto-btor2/logical_arrays.h>
#include <goto-btor2/memory_access.h>
#include <testing-utils/use_catch.h>

#include <memory>
#include <sstream>
#include <stdexcept>

namespace
{
struct fixturet
{
  configt::ansi_ct saved = config.ansi_c;
  symbol_tablet symbols;
  namespacet ns{symbols};
  null_message_handlert handler;
  messaget log{handler};
  btor2_buildert builder;
  expr_to_btor2t expressions{builder, ns, log};
  goto_programt program;
  unsignedbv_typet count{32};
  signedbv_typet integer{32};
  fixturet()
  {
    config.ansi_c.set_ILP32();
  }
  ~fixturet()
  {
    config.ansi_c = saved;
  }

  symbol_exprt symbol(
    const char *id,
    const typet &type,
    bool global = false,
    const exprt &init = nil_exprt())
  {
    symbolt s{id, type, ID_C};
    s.is_lvalue = true;
    s.is_static_lifetime = global;
    s.value = init;
    REQUIRE_FALSE(symbols.add(s));
    return s.symbol_expr();
  }
  symbol_exprt array(const char *id, unsigned length, const typet &leaf)
  {
    return symbol(id, array_typet(leaf, from_integer(length, count)));
  }
  index_exprt at(const exprt &array, int index)
  {
    return index_exprt(array, from_integer(index, integer));
  }
  void observe(const exprt &expr)
  {
    program.add(
      goto_programt::make_assertion(
        equal_exprt(expr, from_integer(0, expr.type()))));
  }
  void decl(const symbol_exprt &expr)
  {
    program.add(goto_programt::make_decl(expr));
  }
};

array_encoding_optionst mode(bool bitvectors, bool mixed = false)
{
  array_encoding_optionst result;
  result.bitvectors = bitvectors;
  result.mixed = mixed;
  return result;
}

std::string model(const btor2_buildert &builder)
{
  std::ostringstream out;
  builder.write(out);
  return out.str();
}

const jsont &info(const json_arrayt &metadata, const std::string &symbol)
{
  for(const auto &entry : metadata)
    if(entry["symbol"].value == symbol)
      return entry;
  throw std::logic_error("missing logical-array metadata");
}

btor2_nid_t data(const logical_arrayst &arrays, const std::string &id)
{
  return std::stoul(info(arrays.metadata(), id)["data_state"].value);
}

// A finite expression evaluator checks concrete data behavior. It does not
// search executions, solve constraints, or perform model checking.
class evaluatort
{
  struct arrayvaluet
  {
    mp_integer initial = 0;
    std::map<mp_integer, mp_integer> cells;
  };
  struct valuet
  {
    mp_integer bits = 0;
    std::shared_ptr<arrayvaluet> array;
  };
  struct nodet
  {
    std::string op;
    unsigned sort = 0;
    std::vector<std::string> args;
  };
  std::map<unsigned, nodet> nodes;
  std::map<unsigned, unsigned> widths;
  std::set<unsigned> array_sorts;
  std::map<unsigned, unsigned> initializers;
  std::map<unsigned, valuet> cache;

  mp_integer norm(const mp_integer &v, unsigned width) const
  {
    const mp_integer modulus = mp_integer(1) << width;
    return ((v % modulus) + modulus) % modulus;
  }
  mp_integer signed_value(const mp_integer &v, unsigned width) const
  {
    return v >= (mp_integer(1) << (width - 1)) ? v - (mp_integer(1) << width)
                                               : v;
  }
  valuet eval(unsigned id)
  {
    if(cache.count(id))
      return cache.at(id);
    const auto &node = nodes.at(id);
    auto arg = [&](unsigned i) { return eval(std::stoul(node.args.at(i))); };
    valuet result;
    if(node.op == "state" || node.op == "input")
    {
      if(node.op == "state" && initializers.count(id))
        result = eval(initializers.at(id));
      if(array_sorts.count(node.sort) && !result.array)
      {
        result.array = std::make_shared<arrayvaluet>();
        result.array->initial = result.bits;
      }
    }
    else if(node.op == "zero")
      result.bits = 0;
    else if(node.op == "one")
      result.bits = 1;
    else if(node.op == "ones")
      result.bits = (mp_integer(1) << widths.at(node.sort)) - 1;
    else if(node.op == "constd")
      result.bits = string2integer(node.args.at(0));
    else if(node.op == "ite")
      result = arg(0).bits != 0 ? arg(1) : arg(2);
    else if(node.op == "read")
    {
      const auto array = arg(0).array;
      const auto index = arg(1).bits;
      result.bits =
        array->cells.count(index) ? array->cells.at(index) : array->initial;
    }
    else if(node.op == "write")
    {
      result.array = std::make_shared<arrayvaluet>(*arg(0).array);
      result.array->cells[arg(1).bits] = arg(2).bits;
    }
    else if(node.op == "uext")
      result.bits = arg(0).bits;
    else if(node.op == "sext")
      result.bits = signed_value(
        arg(0).bits, widths.at(nodes.at(std::stoul(node.args.at(0))).sort));
    else if(node.op == "slice")
      result.bits = arg(0).bits >> string2integer(node.args.at(2));
    else if(node.op == "not")
      result.bits = (mp_integer(1) << widths.at(node.sort)) - 1 - arg(0).bits;
    else if(node.op == "add")
      result.bits = arg(0).bits + arg(1).bits;
    else if(node.op == "mul")
      result.bits = arg(0).bits * arg(1).bits;
    else if(node.op == "and")
      result.bits = bitwise_and(arg(0).bits, arg(1).bits);
    else if(node.op == "or")
      result.bits = bitwise_or(arg(0).bits, arg(1).bits);
    else if(node.op == "sll" || node.op == "srl")
    {
      const auto shift = arg(1).bits;
      if(shift < widths.at(node.sort))
        result.bits =
          node.op == "sll" ? arg(0).bits << shift : arg(0).bits >> shift;
    }
    else if(node.op == "ult")
      result.bits = arg(0).bits < arg(1).bits ? 1 : 0;
    else if(node.op == "sgte")
    {
      const auto width = widths.at(nodes.at(std::stoul(node.args.at(0))).sort);
      result.bits =
        signed_value(arg(0).bits, width) >= signed_value(arg(1).bits, width)
          ? 1
          : 0;
    }
    else if(node.op == "neq")
      result.bits = arg(0).bits != arg(1).bits ? 1 : 0;
    else
      throw std::logic_error("unexpected expression " + node.op);
    if(!result.array)
      result.bits = norm(result.bits, widths.at(node.sort));
    cache.emplace(id, result);
    return result;
  }

public:
  explicit evaluatort(const btor2_buildert &builder)
  {
    std::istringstream in(model(builder));
    std::string line;
    while(std::getline(in, line))
    {
      std::istringstream row(line);
      unsigned id;
      nodet node;
      if(!(row >> id >> node.op))
        continue;
      if(node.op == "sort")
      {
        std::string kind;
        row >> kind;
        if(kind == "bitvec")
          row >> widths[id];
        else
          array_sorts.insert(id);
        continue;
      }
      if(node.op == "init")
      {
        unsigned state, value;
        row >> node.sort >> state >> value;
        initializers[state] = value;
        continue;
      }
      row >> node.sort;
      std::string token;
      while(row >> token)
        node.args.push_back(token);
      nodes.emplace(id, node);
    }
  }
  mp_integer value(unsigned id)
  {
    return eval(id).bits;
  }
};
} // namespace

TEST_CASE(
  "Logical arrays conservatively certify the complete use closure",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  auto a = f.array("a", 4, f.integer);
  auto b = f.array("b", 4, f.integer);
  f.decl(a);
  f.decl(b);
  f.observe(f.at(a, 0));
  f.observe(f.at(b, 0));
  SECTION("direct element uses")
  {
    logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
    arrays.collect(f.program);
    REQUIRE(arrays.symbols() == std::set<irep_idt>{"a", "b"});
  }
  SECTION("address of one element declines its entire root")
  {
    f.program.add(
      goto_programt::make_assertion(equal_exprt(
        address_of_exprt(f.at(a, 0)), address_of_exprt(f.at(a, 1)))));
    logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
    arrays.collect(f.program);
    REQUIRE_FALSE(arrays.owns_symbol("a"));
    REQUIRE(arrays.owns_symbol("b"));
  }
  SECTION("whole array copying declines both views")
  {
    f.program.add(goto_programt::make_assignment(a, b));
    logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
    arrays.collect(f.program);
    REQUIRE(arrays.symbols().empty());
  }
  SECTION("unknown pointer inputs keep a single ordinary store")
  {
    const auto p = f.symbol("p", pointer_type(f.integer));
    f.decl(p);
    f.program.add(
      goto_programt::make_assignment(
        p, side_effect_expr_nondett(p.type(), source_locationt::nil())));
    logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
    arrays.collect(f.program);
    REQUIRE(arrays.symbols().empty());
  }
}

TEST_CASE(
  "Logical-array native domains are independent of byte-offset capacity",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const auto n = f.symbol("n", f.count);
  const auto a = f.symbol("a", array_typet(f.integer, n));
  f.decl(n);
  f.program.add(
    goto_programt::make_assignment(n, from_integer(100000000, f.count)));
  f.decl(a);
  f.observe(f.at(a, 99999999));
  f.program.update();
  SECTION("native arrays")
  {
    logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
    arrays.collect(f.program);
    arrays.create_states();
    REQUIRE_FALSE(arrays.failed);
    REQUIRE(f.builder.has_array_sorts());
    REQUIRE(info(arrays.metadata(), "a")["index_width"].value == "32");
  }
  SECTION("pure BV retains its format limit")
  {
    logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(true), true);
    arrays.collect(f.program);
    REQUIRE(arrays.failed);
    REQUIRE(
      arrays.failure_reason.find("packed bitvector width limit") !=
      std::string::npos);
    REQUIRE_FALSE(f.builder.has_array_sorts());
  }
  SECTION("Mixed selects native storage")
  {
    logical_arrayst arrays(
      f.builder, f.expressions, f.ns, mode(false, true), true);
    arrays.collect(f.program);
    arrays.create_states();
    REQUIRE_FALSE(arrays.failed);
    REQUIRE(info(arrays.metadata(), "a")["storage"].value == "array");
    REQUIRE(
      info(arrays.metadata(), "a")["upper_elements"].value == "100000000");
  }
}

TEST_CASE(
  "Multidimension bounds are mathematical products on ILP32",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const auto n = f.symbol("n", f.count);
  const auto a = f.symbol("matrix", array_typet(array_typet(f.integer, n), n));
  f.decl(n);
  f.program.add(
    goto_programt::make_assignment(n, from_integer(65536, f.count)));
  f.decl(a);
  f.observe(f.at(f.at(a, 0), 0));
  f.program.update();
  logical_arrayst arrays(
    f.builder, f.expressions, f.ns, mode(false, true), true);
  arrays.collect(f.program);
  arrays.create_states();
  REQUIRE_FALSE(arrays.failed);
  const auto metadata = arrays.metadata();
  REQUIRE(info(metadata, "matrix")["upper_elements"].value == "4294967296");
  REQUIRE(info(metadata, "matrix")["index_width"].value == "64");
  REQUIRE(info(metadata, "matrix")["storage"].value == "array");
}

TEST_CASE(
  "VLA dimensions latch at DECL and storage refreshes per lifetime",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const auto n = f.symbol("n", f.count);
  const auto a = f.symbol("a", array_typet(f.integer, n));
  f.decl(n);
  f.decl(a);
  f.observe(f.at(a, 0));
  logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
  arrays.collect(f.program);
  arrays.create_states();
  const auto old_size = f.builder.constd(f.builder.sort_bitvec(32), 3);
  f.expressions.register_symbol("n", old_size, f.count);
  const auto active = f.builder.one(f.builder.get_bool_sort());
  arrays.begin(1, active);
  arrays.declaration(a, false);
  const auto first = arrays.values();
  const auto state = data(arrays, "a");
  REQUIRE(first.at(state) != state);
  const auto dimension =
    std::stoul(to_json_array(info(arrays.metadata(), "a")["dimensions"])
                 .begin()
                 ->operator[]("state")
                 .value);
  REQUIRE(first.at(dimension) == old_size);
  const auto new_size = f.builder.constd(f.builder.sort_bitvec(32), 1);
  f.expressions.register_symbol("n", new_size, f.count);
  REQUIRE(arrays.assign(f.at(a, 2), from_integer(7, f.integer)));
  const auto read = arrays.convert(f.at(a, 2));
  REQUIRE(read);
  REQUIRE(evaluatort(f.builder).value(*read) == 7);
  const auto negative = arrays.convert(f.at(a, -1));
  const auto out_of_bounds = arrays.convert(f.at(a, 3));
  REQUIRE(evaluatort(f.builder).value(*negative) == 0);
  REQUIRE(evaluatort(f.builder).value(*out_of_bounds) == 0);
  arrays.end();
  arrays.begin(2, active);
  arrays.declaration(a, false);
  REQUIRE(arrays.values().at(state) != first.at(state));
  REQUIRE(arrays.values().at(dimension) == new_size);
  REQUIRE_FALSE(arrays.failed);
}

TEST_CASE(
  "Logical arrays preserve latest stores and Bool type values",
  "[goto-btor2][logical-arrays]")
{
  for(const bool bv : {false, true})
  {
    fixturet f;
    const auto a = f.array("flags", 4, c_bool_typet(8));
    f.decl(a);
    f.observe(f.at(a, 0));
    logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(bv), true);
    arrays.collect(f.program);
    arrays.create_states();
    arrays.begin(1, f.builder.one(f.builder.get_bool_sort()));
    arrays.declaration(a, false);
    REQUIRE(arrays.assign(f.at(a, 0), from_integer(42, f.integer)));
    REQUIRE(arrays.assign(f.at(a, 1), from_integer(0, f.integer)));
    const auto first = arrays.convert(f.at(a, 0));
    const auto second = arrays.convert(f.at(a, 1));
    REQUIRE(first);
    REQUIRE(second);
    evaluatort evaluator(f.builder);
    REQUIRE(evaluator.value(*first) == 1);
    REQUIRE(evaluator.value(*second) == 0);
    REQUIRE(info(arrays.metadata(), "flags")["element_width"].value == "1");
    REQUIRE(
      info(arrays.metadata(), "flags")["source_element_width"].value == "8");
    REQUIRE(f.builder.has_array_sorts() == !bv);
    const auto latest = arrays.values();
    arrays.bind(latest);
    REQUIRE(arrays.values() == latest);
    arrays.commit(f.builder.one(f.builder.get_bool_sort()), latest);
    arrays.finish();
    REQUIRE_FALSE(arrays.failed);
  }
}

TEST_CASE(
  "Uniform nested static initialization does not enumerate capacity",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const array_typet row(f.integer, from_integer(100000, f.count));
  const array_typet type(row, from_integer(100000, f.count));
  const auto init =
    array_of_exprt(array_of_exprt(from_integer(9, f.integer), row), type);
  const auto a = f.symbol("global", type, true, init);
  f.observe(f.at(f.at(a, 99999), 99999));
  logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
  arrays.collect(f.program);
  arrays.create_states();
  arrays.initialize_static();
  arrays.begin(1, f.builder.one(f.builder.get_bool_sort()));
  const auto read = arrays.convert(f.at(f.at(a, 99999), 99999));
  REQUIRE(read);
  REQUIRE(evaluatort(f.builder).value(*read) == 9);
  REQUIRE(f.builder.get_node_count() < 100);
  REQUIRE_FALSE(arrays.failed);
}

TEST_CASE(
  "Native Bool static fills use literal scalar broadcast initializers",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const c_bool_typet boolean(8);
  const array_typet type(boolean, from_integer(4, f.count));
  const auto a = f.symbol(
    "global_flags", type, true, array_of_exprt(from_integer(1, boolean), type));
  f.observe(f.at(a, 3));
  logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
  arrays.collect(f.program);
  arrays.create_states();
  arrays.initialize_static();
  arrays.begin(1, f.builder.one(f.builder.get_bool_sort()));
  const auto read = arrays.convert(f.at(a, 3));
  REQUIRE(read);
  REQUIRE(evaluatort(f.builder).value(*read) == 1);
  std::map<unsigned, std::pair<std::string, unsigned>> declarations;
  std::set<unsigned> array_sorts;
  std::istringstream in(model(f.builder));
  std::string line;
  unsigned broadcast_count = 0;
  while(std::getline(in, line))
  {
    std::istringstream row(line);
    unsigned id, sort;
    std::string op;
    if(!(row >> id >> op))
      continue;
    if(op == "sort")
    {
      std::string kind;
      row >> kind;
      if(kind == "array")
        array_sorts.insert(id);
      continue;
    }
    row >> sort;
    if(op == "init" && array_sorts.count(sort))
    {
      unsigned state, value;
      row >> state >> value;
      if(!array_sorts.count(declarations.at(value).second))
      {
        const auto kind = declarations.at(value).first;
        REQUIRE(
          (kind == "zero" || kind == "one" || kind == "ones" ||
           kind == "constd" || kind == "const" || kind == "consth"));
        ++broadcast_count;
      }
    }
    declarations.emplace(id, std::make_pair(op, sort));
  }
  REQUIRE(broadcast_count == 2);
  REQUIRE_FALSE(arrays.failed);
}

TEST_CASE(
  "Unsupported literal repetition stays in byte memory before planning",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const array_typet row(f.integer, from_integer(2, f.count));
  const array_typet type(row, from_integer(5000, f.count));
  const array_exprt pattern(
    {from_integer(1, f.integer), from_integer(2, f.integer)}, row);
  const auto a = f.symbol("global", type, true, array_of_exprt(pattern, type));
  f.observe(f.at(f.at(a, 0), 0));
  logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
  arrays.collect(f.program);
  REQUIRE_FALSE(arrays.owns_symbol("global"));
  REQUIRE_FALSE(arrays.failed);
}

TEST_CASE(
  "Unused certified VLA storage needs no BV capacity or states",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const auto n = f.symbol("n", unsignedbv_typet(64));
  const auto a = f.symbol("unused", array_typet(f.integer, n));
  f.decl(n);
  f.decl(a);
  f.program.add(
    goto_programt::make_assignment(f.at(a, 0), from_integer(7, f.integer)));
  logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(true), true);
  arrays.collect(f.program);
  arrays.create_states();
  REQUIRE(arrays.owns_symbol("unused"));
  REQUIRE_FALSE(arrays.failed);
  REQUIRE(arrays.state_sorts().empty());
  REQUIRE(info(arrays.metadata(), "unused")["storage"].value == "unused");
  REQUIRE(info(arrays.metadata(), "unused")["data_state"].is_null());
  arrays.begin(1, f.builder.one(f.builder.get_bool_sort()));
  arrays.declaration(a, false);
  REQUIRE(arrays.assign(f.at(a, 0), from_integer(7, f.integer)));
  REQUIRE_FALSE(arrays.failed);
  REQUIRE_FALSE(f.builder.has_array_sorts());
}

TEST_CASE(
  "Memory adapter reserves logical identities among physical objects",
  "[goto-btor2][logical-arrays]")
{
  for(const bool bv : {false, true})
  {
    fixturet f;
    const auto a = f.symbol("a", unsignedbv_typet(8));
    const auto b = f.array("b", 4, unsignedbv_typet(8));
    const auto z = f.symbol("z", unsignedbv_typet(8));
    f.decl(a);
    f.decl(b);
    f.decl(z);
    f.observe(f.at(b, 0));
    f.program.add(
      goto_programt::make_assertion(
        notequal_exprt(address_of_exprt(a), address_of_exprt(z))));
    f.program.update();
    btor2_buildert old_builder;
    expr_to_btor2t old_expr(old_builder, f.ns, f.log);
    memory_accesst baseline(old_builder, old_expr, f.ns, f.log, 0, mode(bv));
    baseline.collect(f.program);
    memory_accesst memory(
      f.builder, f.expressions, f.ns, f.log, 0, mode(bv), true);
    memory.collect(f.program);
    REQUIRE_FALSE(memory.failed);
    REQUIRE_FALSE(baseline.failed);
    REQUIRE(memory.heap.objects.size() == 2);
    REQUIRE(baseline.heap.objects.size() == 3);
    REQUIRE(memory.heap.static_identity_count() == 3);
    REQUIRE(memory.heap.reserved_root_ids.count("b") == 1);
    REQUIRE(
      memory.heap.objects.at("a").tag == baseline.heap.objects.at("a").tag);
    REQUIRE(
      memory.heap.objects.at("z").tag == baseline.heap.objects.at("z").tag);
    REQUIRE(memory.heap.object_bits == baseline.heap.object_bits);
    REQUIRE(memory.heap.offset_bits == baseline.heap.offset_bits);
    memory.create_states();
    f.expressions.set_memory(&memory);
    memory.initialize_static();
    memory.begin(1, f.builder.one(f.builder.get_bool_sort()));
    memory.declaration(b, false);
    REQUIRE(memory.assign(f.at(b, 0), from_integer(7, unsignedbv_typet(8))));
    const auto read = f.expressions.convert(f.at(b, 0));
    REQUIRE(read != 0);
    REQUIRE(evaluatort(f.builder).value(read) == 7);
    f.builder.output(read, "stored_element");
    memory.end();
    memory.finish();
    REQUIRE_FALSE(memory.failed);
    REQUIRE(memory.metadata()["logical_arrays"].is_array());
    f.builder.prune_dependencies();
    REQUIRE(memory.metadata()["logical_arrays"].is_array());
  }
}

TEST_CASE(
  "Logical arrays require pure integral dimension expressions",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const auto n = f.symbol("n", f.integer);
  f.decl(n);
  f.program.add(goto_programt::make_assignment(n, from_integer(2, f.integer)));
  exprt size;
  SECTION("postincrement remains outside logical ownership")
  {
    size = side_effect_exprt(
      ID_postincrement, {n}, f.integer, source_locationt::nil());
  }
  SECTION("nested side effects are checked before simplification")
  {
    size = plus_exprt(
      from_integer(4, f.integer),
      mult_exprt(
        from_integer(0, f.integer),
        side_effect_expr_nondett(f.integer, source_locationt::nil())));
  }
  SECTION("floating dimensions are not C integral dimensions")
  {
    // A symbol keeps this case independent from the side-effect check.
    size = f.symbol("floating_size", double_type());
  }
  SECTION("pointer dimensions are not C integral dimensions")
  {
    size = null_pointer_exprt(pointer_type(f.integer));
  }
  const auto a = f.symbol("unused", array_typet(f.integer, size));
  f.decl(a);
  f.program.update();
  logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
  arrays.collect(f.program);
  REQUIRE_FALSE(arrays.owns_symbol("unused"));
  REQUIRE_FALSE(arrays.failed);
  arrays.create_states();
  REQUIRE(arrays.state_sorts().empty());
}

TEST_CASE(
  "Unused storage cannot make a side-effecting public GOTO input succeed",
  "[goto-btor2][logical-arrays]")
{
  fixturet f;
  const auto n = f.symbol("n", f.integer);
  const auto size = side_effect_exprt(
    ID_postincrement, {n}, f.integer, source_locationt::nil());
  const auto a = f.symbol("unused", array_typet(f.integer, size));
  goto_functionst::goto_functiont function;
  function.body.add(goto_programt::make_decl(n));
  function.body.add(
    goto_programt::make_assignment(n, from_integer(2, f.integer)));
  function.body.add(goto_programt::make_decl(a));
  function.body.add(
    goto_programt::make_assertion(equal_exprt(n, from_integer(3, f.integer))));
  function.body.add(goto_programt::make_end_function());
  function.body.update();
  for(bool enabled : {false, true})
  {
    std::ostringstream output;
    btor2_optimization_optionst optimize;
    optimize.logical_arrays = enabled;
    REQUIRE(write_goto_function_btor2(
      function,
      "main",
      f.symbols,
      output,
      f.log,
      false,
      nullptr,
      0,
      mode(false),
      {},
      false,
      scalar_projection_modet::NONE,
      optimize));
    REQUIRE(output.str().empty());
  }
}

TEST_CASE(
  "Certified logical-array copies keep source snapshots and latest values",
  "[goto-btor2][logical-arrays][array-copy-summary]")
{
  for(const bool mixed : {false, true})
  {
    fixturet f;
    const auto a = f.array("a", 4, f.integer);
    const auto b = f.array("b", 4, f.integer);
    const auto c = f.array("c", 4, f.integer);
    for(const auto &array : {a, b, c})
    {
      f.decl(array);
      f.observe(f.at(array, 0));
    }
    for(const auto &pair :
        {std::make_pair(b, a), std::make_pair(c, b), std::make_pair(a, a)})
    {
      code_assignt copy(pair.first, pair.second);
      copy.set("c2btor_certified_array_copy", true);
      f.program.add(goto_programt::make_assignment(copy));
    }
    logical_arrayst arrays(
      f.builder, f.expressions, f.ns, mode(false, mixed), true);
    arrays.collect(f.program);
    REQUIRE(arrays.symbols() == std::set<irep_idt>{"a", "b", "c"});
    arrays.create_states();
    arrays.begin(1, f.builder.one(f.builder.get_bool_sort()));
    for(const auto &array : {a, b, c})
      arrays.declaration(array, false);
    REQUIRE(arrays.assign(f.at(a, 0), from_integer(7, f.integer)));
    REQUIRE(arrays.assign(b, a));
    REQUIRE(arrays.assign(f.at(a, 0), from_integer(9, f.integer)));
    REQUIRE(arrays.assign(c, b));
    REQUIRE(arrays.assign(f.at(b, 0), from_integer(11, f.integer)));
    REQUIRE(arrays.assign(a, a));
    const auto av = arrays.convert(f.at(a, 0));
    const auto bv = arrays.convert(f.at(b, 0));
    const auto cv = arrays.convert(f.at(c, 0));
    REQUIRE(av);
    REQUIRE(bv);
    REQUIRE(cv);
    evaluatort evaluate(f.builder);
    REQUIRE(evaluate.value(*av) == 9);
    REQUIRE(evaluate.value(*bv) == 11);
    REQUIRE(evaluate.value(*cv) == 7);
    REQUIRE_FALSE(arrays.failed);
  }
}

TEST_CASE(
  "Certified copy ownership rejects the complete alias-connected chain",
  "[goto-btor2][logical-arrays][array-copy-summary]")
{
  fixturet f;
  const auto a = f.array("a", 4, f.integer);
  const auto b = f.array("b", 4, f.integer);
  const auto c = f.array("c", 4, f.integer);
  for(const auto &array : {a, b, c})
    f.decl(array);
  for(const auto &pair : {std::make_pair(c, b), std::make_pair(b, a)})
  {
    code_assignt copy(pair.first, pair.second);
    copy.set("c2btor_certified_array_copy", true);
    f.program.add(goto_programt::make_assignment(copy));
  }
  f.program.add(
    goto_programt::make_assertion(
      equal_exprt(address_of_exprt(f.at(a, 0)), address_of_exprt(f.at(a, 1)))));
  logical_arrayst arrays(f.builder, f.expressions, f.ns, mode(false), true);
  arrays.collect(f.program);
  REQUIRE(arrays.symbols().empty());
}

TEST_CASE(
  "Copy-loop certification preserves exit state and rejects partial effects",
  "[goto-btor2][array-copy-summary]")
{
  for(const std::string variant :
      {"copy",
       "self",
       "tile",
       "partial",
       "shift",
       "assert",
       "alias",
       "extra_write",
       "zero"})
  {
    INFO(variant);
    fixturet f;
    const auto a = f.array("a", 4, f.integer);
    const auto b = variant == "self" ? a : f.array("b", 4, f.integer);
    const auto i = f.symbol("i", f.integer);
    f.decl(a);
    if(b != a)
      f.decl(b);
    f.decl(i);
    const auto zero = from_integer(0, f.integer);
    const auto one = from_integer(1, f.integer);
    const auto two = from_integer(2, f.integer);
    const int limit = variant == "zero"      ? 0
                      : variant == "tile"    ? 2
                      : variant == "partial" ? 3
                                             : 4;
    f.program.add(goto_programt::make_assignment(i, zero));
    const auto head = f.program.add_instruction(GOTO);
    const exprt index =
      variant == "tile" ? exprt(mult_exprt(two, i)) : exprt(i);
    const exprt source_index =
      variant == "shift" ? exprt(plus_exprt(index, one)) : index;
    f.program.add(
      goto_programt::make_assignment(
        index_exprt(b, index), index_exprt(a, source_index)));
    if(variant == "tile")
      f.program.add(
        goto_programt::make_assignment(
          index_exprt(b, plus_exprt(index, one)),
          index_exprt(a, plus_exprt(index, one))));
    if(variant == "assert")
      f.program.add(goto_programt::make_assertion(true_exprt()));
    if(variant == "extra_write")
      f.program.add(goto_programt::make_assignment(f.at(a, 0), zero));
    f.program.add(goto_programt::make_assignment(i, plus_exprt(i, one)));
    f.program.add(goto_programt::make_goto(head));
    const auto exit = f.program.add(
      goto_programt::make_assertion(
        equal_exprt(i, from_integer(limit, f.integer))));
    *head = goto_programt::make_goto(
      exit,
      not_exprt(
        binary_relation_exprt(i, ID_lt, from_integer(limit, f.integer))));
    f.observe(f.at(a, 3));
    f.observe(f.at(b, 3));
    if(variant == "alias")
      f.program.add(
        goto_programt::make_assertion(equal_exprt(
          address_of_exprt(f.at(a, 0)), address_of_exprt(f.at(a, 1)))));
    f.program.update();
    goto_programt original;
    original.copy_from(f.program);
    const auto report = summarize_array_loops(f.program, f.ns);
    const bool accept =
      variant == "copy" || variant == "self" || variant == "tile";
    REQUIRE(report.copies == (accept ? 1 : 0));
    REQUIRE(report.fills == 0);
    if(accept)
    {
      bool final_counter = false, preserved_assertion = false;
      for(const auto &instruction : f.program.instructions)
      {
        if(
          instruction.is_assign() && instruction.assign_lhs() == i &&
          instruction.assign_rhs() == from_integer(limit, f.integer))
          final_counter = true;
        if(
          instruction.is_assert() &&
          instruction.condition() == exit->condition())
          preserved_assertion = true;
      }
      REQUIRE(final_counter);
      REQUIRE(preserved_assertion);
    }
    else
      REQUIRE(f.program.equals(original));
  }
}

TEST_CASE(
  "Copy certificates compare declaration-time extents even for identical types",
  "[goto-btor2][array-copy-summary]")
{
  fixturet f;
  const auto n = f.symbol("n", f.integer);
  const auto i = f.symbol("i", f.integer);
  const array_typet type(f.integer, n);
  const auto a = f.symbol("a", type);
  const auto b = f.symbol("b", type);
  f.decl(n);
  f.decl(i);
  f.program.add(goto_programt::make_assignment(n, from_integer(4, f.integer)));
  f.decl(a);
  f.program.add(goto_programt::make_assignment(n, from_integer(3, f.integer)));
  f.decl(b);
  f.program.add(goto_programt::make_assignment(i, from_integer(0, f.integer)));
  const auto head = f.program.add_instruction(GOTO);
  f.program.add(
    goto_programt::make_assignment(index_exprt(b, i), index_exprt(a, i)));
  f.program.add(
    goto_programt::make_assignment(
      i, plus_exprt(i, from_integer(1, f.integer))));
  f.program.add(goto_programt::make_goto(head));
  const auto exit = f.program.add(
    goto_programt::make_assertion(equal_exprt(f.at(a, 2), f.at(b, 2))));
  *head = goto_programt::make_goto(
    exit,
    not_exprt(binary_relation_exprt(i, ID_lt, from_integer(3, f.integer))));
  f.program.update();
  goto_programt original;
  original.copy_from(f.program);
  const auto report = summarize_array_loops(f.program, f.ns);
  REQUIRE(report.copies == 0);
  REQUIRE(f.program.equals(original));
}
