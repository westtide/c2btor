#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <goto-btor2/heap_model.h>
#include <goto-btor2/symbolic_heap_cells.h>
#include <testing-utils/use_catch.h>

namespace
{
struct cell_fixturet
{
  configt::ansi_ct saved = config.ansi_c;
  symbol_tablet symbols;
  namespacet ns{symbols};
  goto_programt program;
  signedbv_typet word{64};
  unsignedbv_typet size{32};
  symbol_exprt p{"p", pointer_typet(word, 32)};
  symbol_exprt q{"q", p.type()};
  symbol_exprt n{"n", size};

  cell_fixturet()
  {
    config.ansi_c.set_ILP32();
    for(const auto &symbol : {p, q, n})
    {
      symbols.add(symbolt{symbol.get_identifier(), symbol.type(), ID_C});
      program.add(goto_programt::make_decl(symbol));
    }
  }
  ~cell_fixturet()
  {
    config.ansi_c = saved;
  }
  void allocate(const symbol_exprt &pointer)
  {
    side_effect_exprt allocation(
      ID_allocate, pointer.type(), source_locationt{});
    allocation.operands() = {
      mult_exprt(n, from_integer(8, n.type())), false_exprt()};
    program.add(goto_programt::make_assignment(pointer, allocation));
  }
  exprt shifted(const exprt &pointer, int bytes) const
  {
    pointer_typet character_pointer(unsignedbv_typet(8), 32);
    return typecast_exprt(
      plus_exprt(
        typecast_exprt(pointer, character_pointer), from_integer(bytes, size)),
      p.type());
  }
  void store(const exprt &pointer)
  {
    program.add(
      goto_programt::make_assignment(
        dereference_exprt(pointer), from_integer(7, word)));
  }
  void read(const exprt &pointer)
  {
    program.add(
      goto_programt::make_assertion(
        equal_exprt(dereference_exprt(pointer), from_integer(7, word))));
  }
  symbolic_heap_cell_certificatet certify()
  {
    program.update();
    return certify_symbolic_heap_cells(program, ns);
  }
};
} // namespace

TEST_CASE(
  "Symbolic heap cells preserve allocation alignment through loops",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  f.allocate(f.q);
  f.program.add(
    goto_programt::make_assignment(
      f.n, side_effect_expr_nondett(f.n.type(), source_locationt{})));
  auto head = f.program.add(goto_programt::make_skip());
  f.store(plus_exprt(f.p, f.n));
  f.store(plus_exprt(f.q, f.n));
  f.read(plus_exprt(f.p, f.n));
  f.program.add(
    goto_programt::make_goto(
      head, side_effect_expr_nondett(bool_typet(), source_locationt{})));
  const auto certificate = f.certify();
  REQUIRE(certificate.word64);
  REQUIRE(certificate.accesses == 3);
}

TEST_CASE(
  "Heap cell alignment comes from offsets, not pointer target types",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  bool expected = false;
  SECTION("a character-pointer shift by one invalidates the certificate")
  {
    f.program.add(goto_programt::make_assignment(f.q, f.shifted(f.p, 1)));
  }
  SECTION("a character-pointer shift by eight preserves alignment")
  {
    f.program.add(goto_programt::make_assignment(f.q, f.shifted(f.p, 8)));
    expected = true;
  }
  SECTION("a dynamic integer multiple of eight preserves alignment")
  {
    pointer_typet bytes(unsignedbv_typet(8), 32);
    f.program.add(
      goto_programt::make_assignment(
        f.q,
        typecast_exprt(
          plus_exprt(
            typecast_exprt(f.p, bytes),
            mult_exprt(f.n, from_integer(8, f.n.type()))),
          f.q.type())));
    expected = true;
  }
  SECTION("a conditional copy or NULL preserves the offset residue")
  {
    f.program.add(
      goto_programt::make_assignment(
        f.q,
        if_exprt(
          side_effect_expr_nondett(bool_typet(), source_locationt{}),
          f.p,
          null_pointer_exprt(to_pointer_type(f.q.type())))));
    expected = true;
  }
  SECTION("an uninitialized pointer has no alignment fact")
  {
  }
  SECTION("redeclaration forgets an earlier allocation")
  {
    f.allocate(f.q);
    f.program.add(goto_programt::make_dead(f.q));
    f.program.add(goto_programt::make_decl(f.q));
  }
  SECTION("an integer-to-pointer cast provides no alignment proof")
  {
    f.program.add(
      goto_programt::make_assignment(
        f.q, typecast_exprt(from_integer(8, f.size), f.q.type())));
  }
  f.read(f.q);
  const auto certificate = f.certify();
  REQUIRE(certificate.word64 == expected);
  REQUIRE_FALSE(certificate.reason.empty());
}

TEST_CASE(
  "Heap cell alignment joins every incoming CFG path",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  int alternative_shift = 0;
  SECTION("both branches remain aligned")
  {
    alternative_shift = 8;
  }
  SECTION("one branch becomes unaligned")
  {
    alternative_shift = 1;
  }
  auto branch = f.program.add(goto_programt::make_skip());
  f.program.add(goto_programt::make_assignment(f.q, f.p));
  auto jump = f.program.add(goto_programt::make_skip());
  auto alternative = f.program.add(goto_programt::make_skip());
  f.program.add(
    goto_programt::make_assignment(f.q, f.shifted(f.p, alternative_shift)));
  auto join = f.program.add(goto_programt::make_skip());
  *branch = goto_programt::make_goto(
    alternative, side_effect_expr_nondett(bool_typet(), source_locationt{}));
  *jump = goto_programt::make_goto(join);
  f.read(f.q);
  REQUIRE(f.certify().word64 == (alternative_shift == 8));
}

TEST_CASE(
  "Heap cell alignment reaches a fixed point on pointer-changing backedges",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  bool expected = true;
  auto head = f.program.add(goto_programt::make_skip());
  f.read(f.p);
  SECTION("word stride preserves alignment")
  {
    f.program.add(goto_programt::make_assignment(f.p, plus_exprt(f.p, f.n)));
  }
  SECTION("byte stride loses alignment after the first iteration")
  {
    f.program.add(goto_programt::make_assignment(f.p, f.shifted(f.p, 1)));
    expected = false;
  }
  f.program.add(goto_programt::make_goto(head));
  REQUIRE(f.certify().word64 == expected);
}

TEST_CASE(
  "Address formation does not read heap contents",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  f.program.add(
    goto_programt::make_assignment(
      f.q, address_of_exprt(dereference_exprt(plus_exprt(f.p, f.n)))));
  f.read(f.q);
  const auto certificate = f.certify();
  REQUIRE(certificate.word64);
  REQUIRE(certificate.accesses == 1);
}

TEST_CASE(
  "Mixed heap accesses and unknown effects select byte storage",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  f.read(f.p);
  SECTION("a byte view is a mixed-width memory access")
  {
    f.program.add(
      goto_programt::make_assertion(equal_exprt(
        dereference_exprt(
          typecast_exprt(f.p, pointer_typet(unsignedbv_typet(8), 32))),
        from_integer(7, unsignedbv_typet(8)))));
  }
  SECTION("a copy marker retains its existing byte semantics")
  {
    codet copy("c2btor_copy_byte");
    copy.operands() = {f.p, f.p};
    f.program.add(goto_programt::make_other(copy));
  }
  SECTION("an atomic range copy cannot use the scalar access certificate")
  {
    codet copy("c2btor_copy_range");
    copy.operands() = {f.p, f.p, from_integer(8, f.size)};
    f.program.add(goto_programt::make_other(copy));
  }
  SECTION("byte extraction needs the byte representation")
  {
    exprt extract(ID_byte_extract_little_endian, f.word);
    extract.operands() = {dereference_exprt(f.p), from_integer(0, f.size)};
    f.program.add(goto_programt::make_other(code_expressiont(extract)));
  }
  SECTION("byte update needs the byte representation")
  {
    exprt update(ID_byte_update_little_endian, f.word);
    update.operands() = {
      dereference_exprt(f.p), from_integer(0, f.size), from_integer(1, f.word)};
    f.program.add(goto_programt::make_other(code_expressiont(update)));
  }
  SECTION("an aggregate read is outside the scalar access certificate")
  {
    struct_typet aggregate;
    aggregate.components().emplace_back("value", f.word);
    f.program.add(
      goto_programt::make_other(code_expressiont(
        dereference_exprt(typecast_exprt(f.p, pointer_typet(aggregate, 32))))));
  }
  SECTION("an unknown OTHER operation may invalidate pointer facts")
  {
    f.program.add(goto_programt::make_other(codet("unknown_pointer_effect")));
  }
  SECTION("an unknown call may change memory or pointer values")
  {
    symbol_exprt function("unknown", code_typet({}, empty_typet()));
    f.symbols.add(symbolt{function.get_identifier(), function.type(), ID_C});
    f.program.add(goto_programt::make_function_call(nil_exprt(), function, {}));
  }
  SECTION("volatile data cannot use the certificate")
  {
    auto type = f.word;
    type.set(ID_C_volatile, true);
    f.program.add(
      goto_programt::make_assertion(equal_exprt(
        dereference_exprt(typecast_exprt(f.p, pointer_typet(type, 32))),
        from_integer(7, type))));
  }
  f.read(f.p);
  REQUIRE_FALSE(f.certify().word64);
}

TEST_CASE(
  "Scalar nondet calls and lifetime metadata preserve heap alignment",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  symbol_exprt function("__VERIFIER_nondet_int", code_typet({}, f.size));
  f.symbols.add(symbolt{function.get_identifier(), function.type(), ID_C});
  f.program.add(goto_programt::make_function_call(f.n, function, {}));
  codet release("c2btor_deallocate");
  release.operands() = {f.p};
  f.program.add(goto_programt::make_other(release));
  // Ordinary data access remains independent of live metadata in this model.
  f.read(plus_exprt(f.p, f.n));
  REQUIRE(f.certify().word64);
}

TEST_CASE(
  "Arbitrary address inputs invalidate pointer facts on indirect writes",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  f.program.add(
    goto_programt::make_assignment(
      f.q, side_effect_expr_nondett(f.q.type(), source_locationt{})));
  f.store(f.p);
  f.read(f.p);
  REQUIRE_FALSE(f.certify().word64);
}

TEST_CASE(
  "Indirect writes invalidate addressable pointer states",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  // A word write to p's object can alter the pointer's low offset bits.
  f.store(typecast_exprt(address_of_exprt(f.p), f.p.type()));
  f.read(f.p);
  REQUIRE_FALSE(f.certify().word64);
}

TEST_CASE(
  "Cast lvalue writes invalidate the heap cell certificate",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  f.read(f.p);
  REQUIRE(f.certify().word64);
  // Raw GOTO can write the pointer representation through a cast lvalue.
  // The source pointer type alone must not retain its earlier alignment fact.
  f.program.add(
    goto_programt::make_assignment(
      typecast_exprt(f.p, f.size), from_integer(1, f.size)));
  f.read(f.p);
  REQUIRE_FALSE(f.certify().word64);
}

TEST_CASE(
  "Source assertions cannot provide heap alignment premises",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  f.allocate(f.p);
  f.program.add(goto_programt::make_assignment(f.p, f.shifted(f.p, 1)));
  SECTION("asserting an aligned offset does not refine pointer facts")
  {
    f.program.add(
      goto_programt::make_assertion(equal_exprt(
        mod_exprt(pointer_offset_exprt(f.p, f.size), from_integer(8, f.size)),
        from_integer(0, f.size))));
  }
  SECTION("a false assertion still advances to the following memory access")
  {
    f.program.add(goto_programt::make_assertion(false_exprt()));
  }
  f.read(f.p);
  const auto certificate = f.certify();
  REQUIRE_FALSE(certificate.word64);
  REQUIRE(certificate.accesses == 1);
}

TEST_CASE(
  "A narrow offset domain keeps compact symbolic heap storage byte addressed",
  "[goto-btor2][symbolic-heap-cells]")
{
  cell_fixturet f;
  struct restore_bv_configt
  {
    configt::bv_encodingt saved = config.bv_encoding;
    ~restore_bv_configt()
    {
      config.bv_encoding = saved;
    }
  } restore_bv_config;
  config.bv_encoding.object_bits = 30;
  config.bv_encoding.is_object_bits_default = false;
  f.program.add(
    goto_programt::make_assignment(
      f.n, side_effect_expr_nondett(f.n.type(), source_locationt{})));
  f.program.add(
    goto_programt::make_assumption(and_exprt(
      binary_relation_exprt(f.n, ID_ge, from_integer(0, f.size)),
      binary_relation_exprt(f.n, ID_le, from_integer(1, f.size)))));
  side_effect_exprt allocation(ID_allocate, f.p.type(), source_locationt{});
  allocation.operands() = {f.n, false_exprt()};
  f.program.add(goto_programt::make_assignment(f.p, allocation));
  f.read(f.p);
  // Alignment certification does not assume that an eight-byte access is
  // within the allocated extent. The storage planner must also certify its
  // representation domain before selecting an indexed 64-bit cell.
  const auto certificate = f.certify();
  REQUIRE(certificate.word64);
  REQUIRE(certificate.accesses == 1);
  btor2_buildert builder;
  array_encoding_optionst mode;
  mode.bitvectors = false;
  mode.symbolic_heap = true;
  mode.symbolic_heap_arrays = true;
  mode.symbolic_heap_compact = true;
  heap_modelt heap(builder, f.ns, 0, mode);
  heap.has_dynamic_allocations = true;
  heap.plan_capacity(f.program);
  REQUIRE_FALSE(heap.failed);
  REQUIRE(heap.offset_bits == 2);
  REQUIRE(heap.uses_symbolic_allocation_storage());
  heap.create_states();
  REQUIRE_FALSE(heap.failed);
  const auto metadata = heap.metadata();
  REQUIRE(metadata["symbolic_heap"]["word64_certified"].is_false());
  REQUIRE(
    metadata["symbolic_heap"]["cell_certificate_reason"].value.find(
      "too narrow") != std::string::npos);
  const auto &storage = to_json_array(metadata["object_storage"]);
  REQUIRE(storage.size() == 1);
  const auto &object = *storage.begin();
  REQUIRE(object["element_bits"].value == "8");
  REQUIRE(object["index_bits"].value == "2");
  REQUIRE(object["capacity_bytes"].is_null());
  REQUIRE(object["data_encoding"].value == "array");
}
