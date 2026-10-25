#include <goto-btor2/heap_model.h>
#include <goto-btor2/memory_capacity.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include "finite_btor2_replay.h"

namespace
{
struct symbolic_heap_fixturet
{
  configt::ansi_ct saved = config.ansi_c;
  symbol_tablet symbols;
  namespacet ns{symbols};
  goto_programt program;
  unsignedbv_typet size_type{32};
  symbol_exprt n{"n", size_type};
  symbol_exprt p{"p", pointer_typet(signedbv_typet(64), 32)};

  symbolic_heap_fixturet()
  {
    config.ansi_c.set_ILP32();
    config.ansi_c.endianness =
      configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
    symbols.add(symbolt{"n", n.type(), ID_C});
    symbols.add(symbolt{"p", p.type(), ID_C});
  }
  void bounded_nondet()
  {
    program.add(goto_programt::make_assignment(
      n, side_effect_expr_nondett(n.type(), source_locationt{})));
    program.add(goto_programt::make_assumption(and_exprt(
      binary_relation_exprt(n, ID_ge, from_integer(1, n.type())),
      binary_relation_exprt(n, ID_le, from_integer(3, n.type())))));
  }
  ~symbolic_heap_fixturet()
  {
    config.ansi_c = saved;
  }
  exprt bytes() const
  {
    return mult_exprt(n, from_integer(8, size_type));
  }
  void allocate(const exprt &size)
  {
    side_effect_exprt allocation(ID_allocate, p.type(), source_locationt{});
    allocation.operands() = {size, false_exprt()};
    program.add(goto_programt::make_assignment(p, allocation));
  }
};
} // namespace

TEST_CASE(
  "Symbolic allocation sizes and event counts", "[goto-btor2][symbolic-heap]")
{
  symbolic_heap_fixturet f;
  f.program.add(goto_programt::make_assignment(
    f.n, side_effect_expr_nondett(f.n.type(), source_locationt{})));
  f.program.add(goto_programt::make_assumption(
    and_exprt(
      binary_relation_exprt(f.n, ID_ge, from_integer(1, f.n.type())),
      binary_relation_exprt(f.n, ID_le, from_integer(3, f.n.type())))));
  f.allocate(f.bytes());
  f.allocate(f.bytes());
  const auto tail = f.program.add(goto_programt::make_skip());
  f.program.add(goto_programt::make_goto(tail, true_exprt()));
  f.program.update();
  const auto bounds = infer_memory_capacity(f.program, f.ns, {});
  REQUIRE(bounds.allocation_complete);
  REQUIRE(bounds.allocation == 24);
  REQUIRE(bounds.allocation_sizes.size() == 2);
  for(const auto &site : bounds.allocation_sizes)
  {
    REQUIRE(site.alloc_size_expr == f.bytes());
    REQUIRE(site.interval.has_value());
    REQUIRE(site.interval->first == 8);
    REQUIRE(site.interval->second == 24);
  }
  REQUIRE(infer_allocation_slots(f.program, 3) == 2);
}

TEST_CASE(
  "Allocation capacity arithmetic keeps its GOTO width",
  "[goto-btor2][symbolic-heap]")
{
  symbolic_heap_fixturet f;
  f.program.add(goto_programt::make_assignment(
    f.n, from_integer(mp_integer(536870912), f.n.type())));
  f.allocate(f.bytes());
  f.program.update();
  const auto bounds = infer_memory_capacity(f.program, f.ns, {});
  REQUIRE(bounds.allocation_complete);
  REQUIRE(bounds.allocation == 0);
  REQUIRE(bounds.allocation_sizes.size() == 1);
  REQUIRE(bounds.allocation_sizes.front().alloc_size_expr.type() == f.size_type);
  REQUIRE(bounds.allocation_sizes.front().interval->first == 0);
  REQUIRE(bounds.allocation_sizes.front().interval->second == 0);
}

TEST_CASE(
  "Allocation size is a snapshot, not a later scalar use",
  "[goto-btor2][symbolic-heap]")
{
  symbolic_heap_fixturet f;
  f.program.add(goto_programt::make_assignment(f.n, from_integer(3, f.n.type())));
  f.allocate(f.bytes());
  f.program.update();
  btor2_buildert b;
  array_encoding_optionst mode;
  mode.bitvectors = false;
  mode.symbolic_heap = true;
  heap_modelt heap(b, f.ns, 0, mode);
  heap.has_dynamic_allocations = true;
  heap.plan_capacity(f.program);
  REQUIRE_FALSE(heap.failed);
  heap.create_states();
  REQUIRE_FALSE(heap.failed);
  const auto scalar = b.get_or_create_bitvec_sort(32);
  const auto n = b.state(scalar, "n");
  b.init(scalar, n, b.constd(scalar, 3));
  b.next(scalar, n, b.one(scalar));
  const auto once = b.state(b.get_bool_sort(), "once");
  b.init(b.get_bool_sort(), once, b.one(b.get_bool_sort()));
  b.next(b.get_bool_sort(), once, b.zero(b.get_bool_sort()));
  const auto p = b.state(heap.pointer_sort, "p");
  b.init(heap.pointer_sort, p, b.zero(heap.pointer_sort));
  heap.begin(0, once);
  const auto captured = b.mul(scalar, n, b.constd(scalar, 8));
  const auto allocation_expr = f.bytes();
  const auto allocated = heap.allocate(
    captured, b.zero(b.get_bool_sort()), false, &allocation_expr);
  b.next(heap.pointer_sort, p, b.ite(heap.pointer_sort, once, allocated, p));
  heap.end();
  heap.finish();
  heap.begin(1, b.zero(b.get_bool_sort()));
  const auto size = heap.size(p);
  std::ostringstream out;
  b.write(out);
  btor2_test::trace_replayt replay(out.str());
  replay.step();
  REQUIRE(replay.value(n) == 1);
  REQUIRE(replay.value(size) == 24);
  replay.step();
  REQUIRE(replay.value(size) == 24);
  const auto info = heap.metadata();
  REQUIRE(info["allocation_storage_slots"].value == "1");
  REQUIRE(info["symbolic_heap"]["size_snapshot_width"].value == "32");
  const auto &sites = to_json_array(info["allocation_sites"]);
  REQUIRE(sites.size() == 1);
  REQUIRE((*sites.begin())["size_node"].value == std::to_string(captured));
  REQUIRE(
    (*sites.begin())["alloc_size_expr"]["id"].value == id2string(ID_mult));
  REQUIRE(out.str().find(" bad ") == std::string::npos);
}

TEST_CASE(
  "Symbolic heap storage has a fixed native index domain",
  "[goto-btor2][symbolic-heap]")
{
  symbolic_heap_fixturet f;
  f.bounded_nondet();
  f.allocate(f.bytes());
  f.allocate(f.bytes());
  f.program.update();
  btor2_buildert b;
  array_encoding_optionst mode;
  mode.bitvectors = false;
  mode.symbolic_heap = true;
  mode.symbolic_heap_arrays = true;
  SECTION("Array uses one fixed-domain backing for each event identity")
  {
    heap_modelt heap(b, f.ns, 0, mode);
    heap.has_dynamic_allocations = true;
    heap.plan_capacity(f.program);
    REQUIRE_FALSE(heap.failed);
    REQUIRE(heap.uses_symbolic_allocation_storage());
    heap.create_states();
    REQUIRE_FALSE(heap.failed);
    const auto metadata = heap.metadata();
    REQUIRE(metadata["allocation_storage_slots"].value == "2");
    REQUIRE(metadata["allocation_capacity_bytes"].is_null());
    const auto &storage = to_json_array(metadata["object_storage"]);
    REQUIRE(storage.size() == 2);
    for(const auto &object : storage)
    {
      REQUIRE(object["capacity_bytes"].is_null());
      REQUIRE(object["elements"].is_null());
      REQUIRE(object["index_bits"].value == std::to_string(heap.offset_bits));
      REQUIRE(object["element_bits"].value == "8");
      REQUIRE(object["data_encoding"].value == "array");
      REQUIRE(object["states"]["size"].is_number());
    }
  }
  SECTION("Mixed keeps its certified small bound in BV storage")
  {
    mode.mixed = true;
    heap_modelt heap(b, f.ns, 0, mode);
    heap.has_dynamic_allocations = true;
    heap.plan_capacity(f.program);
    REQUIRE_FALSE(heap.failed);
    REQUIRE_FALSE(heap.uses_symbolic_allocation_storage());
    heap.create_states();
    const auto metadata = heap.metadata();
    for(const auto &object : to_json_array(metadata["object_storage"]))
    {
      REQUIRE(object["capacity_bytes"].value == "24");
      REQUIRE(object["data_encoding"].value == "bv");
    }
  }
}

TEST_CASE(
  "Symbolic object stores use the captured byte extent",
  "[goto-btor2][symbolic-heap]")
{
  symbolic_heap_fixturet f;
  f.bounded_nondet();
  f.allocate(f.bytes());
  f.program.update();
  SECTION("little endian byte lanes")
  {
  }
  SECTION("big endian byte lanes")
  {
    config.ansi_c.endianness =
      configt::ansi_ct::endiannesst::IS_BIG_ENDIAN;
  }
  btor2_buildert b;
  array_encoding_optionst mode;
  mode.bitvectors = false;
  mode.symbolic_heap = mode.symbolic_heap_arrays = true;
  heap_modelt heap(b, f.ns, 0, mode);
  heap.has_dynamic_allocations = true;
  heap.plan_capacity(f.program);
  REQUIRE_FALSE(heap.failed);
  heap.create_states();
  const auto sort = b.get_or_create_bitvec_sort(32);
  const auto phase = b.state(sort, "phase");
  b.init(sort, phase, b.zero(sort));
  b.next(
    sort,
    phase,
    b.ite(
      sort,
      b.ult(b.get_bool_sort(), phase, b.constd(sort, 3)),
      b.add(sort, phase, b.one(sort)),
      phase));
  heap.begin(0, b.eq(b.get_bool_sort(), phase, b.zero(sort)));
  heap.allocate(b.constd(sort, 24), b.zero(b.get_bool_sort()), false);
  heap.end();
  const auto pointer = heap.base(3);
  const auto last = heap.add_offset(pointer, b.constd(sort, 16));
  const auto past = heap.add_offset(pointer, b.constd(sort, 24));
  heap.begin(1, b.eq(b.get_bool_sort(), phase, b.one(sort)));
  const auto word = b.get_or_create_bitvec_sort(64);
  heap.store(last, b.constd(word, 7), 64);
  heap.store(past, b.constd(word, 99), 64);
  heap.end();
  heap.begin(2, b.eq(b.get_bool_sort(), phase, b.constd(sort, 2)));
  heap.deallocate(pointer);
  heap.end();
  heap.finish();
  heap.begin(3, b.zero(b.get_bool_sort()));
  const auto legal = heap.load(last, 64);
  const auto out_of_extent = heap.load(past, 64);
  const auto live = heap.is_live(pointer);
  std::ostringstream out;
  b.write(out);
  btor2_test::trace_replayt replay(out.str());
  replay.step();
  replay.step();
  REQUIRE(replay.value(legal) == 7);
  REQUIRE(replay.value(out_of_extent) == 0);
  REQUIRE(replay.value(live) == 1);
  replay.step();
  REQUIRE(replay.value(live) == 0);
  // The existing ReachSafety totalization does not gate data by lifetime.
  // This supplied post-free observation is not a standard-C safety verdict.
  REQUIRE(replay.value(legal) == 7);
  REQUIRE(out.str().find(" bad ") == std::string::npos);
  REQUIRE(out.str().find(" constraint ") == std::string::npos);
}

TEST_CASE(
  "Wide symbolic offsets isolate large allocation events",
  "[goto-btor2][symbolic-heap]")
{
  symbolic_heap_fixturet f;
  f.program.add(goto_programt::make_assignment(
    f.n, side_effect_expr_nondett(f.n.type(), source_locationt{})));
  f.allocate(f.bytes());
  f.allocate(f.bytes());
  f.program.update();
  btor2_buildert b;
  array_encoding_optionst mode;
  mode.bitvectors = false;
  mode.symbolic_heap = mode.symbolic_heap_arrays = true;
  mode.symbolic_heap_wide_offsets = true;
  SECTION("native Array")
  {
  }
  SECTION("explicit BV dynamic Array fallback")
  {
    mode.bitvectors = true;
    mode.symbolic_heap_bv_array_fallback = true;
  }
  SECTION("big endian native Array")
  {
    config.ansi_c.endianness =
      configt::ansi_ct::endiannesst::IS_BIG_ENDIAN;
  }
  heap_modelt heap(b, f.ns, 0, mode);
  heap.has_dynamic_allocations = true;
  heap.plan_capacity(f.program);
  REQUIRE_FALSE(heap.failed);
  REQUIRE(heap.pointer_bits == 32);
  REQUIRE(heap.offset_bits == 32);
  REQUIRE(heap.pointer_value_bits == heap.object_bits + 32);
  REQUIRE(config.ansi_c.pointer_width == 32);
  REQUIRE(heap.metadata()["allocation_storage_slots"].value == "2");
  heap.create_states();
  REQUIRE_FALSE(heap.failed);
  const auto scalar = b.get_or_create_bitvec_sort(32);
  REQUIRE(heap.size_sort == scalar);
  REQUIRE(heap.pointer_sort != scalar);
  const auto phase = b.state(scalar, "phase");
  b.init(scalar, phase, b.zero(scalar));
  b.next(scalar, phase, b.add(scalar, phase, b.one(scalar)));
  heap.begin(0, b.eq(b.get_bool_sort(), phase, b.zero(scalar)));
  const auto extent = b.constd(scalar, mp_integer(4294967288));
  heap.allocate(extent, b.zero(b.get_bool_sort()), false);
  heap.allocate(extent, b.zero(b.get_bool_sort()), false);
  heap.end();
  const auto a = heap.base(3);
  const auto other = heap.base(4);
  const auto last = heap.add_offset(a, b.constd(scalar, mp_integer(4294967280)));
  const auto b8 = heap.add_offset(other, b.constd(scalar, 64));
  const auto past = heap.add_offset(a, extent);
  const auto wrapped = heap.add_offset(
    heap.add_offset(a, b.constd(scalar, mp_integer(4294967295))),
    b.one(scalar));
  const auto word = b.get_or_create_bitvec_sort(64);
  heap.begin(1, b.eq(b.get_bool_sort(), phase, b.one(scalar)));
  heap.store(a, b.constd(word, 11), 64);
  heap.store(b8, b.constd(word, 22), 64);
  heap.store(last, b.constd(word, 33), 64);
  heap.store(past, b.constd(word, 44), 64);
  heap.end();
  heap.finish();
  heap.begin(2, b.zero(b.get_bool_sort()));
  const auto a0_value = heap.load(a, 64);
  const auto b8_value = heap.load(b8, 64);
  const auto last_value = heap.load(last, 64);
  const auto past_value = heap.load(past, 64);
  const auto legal = heap.accessible(last, b.constd(scalar, 8), false);
  const auto illegal = heap.accessible(past, b.constd(scalar, 8), false);
  const auto wrapped_tag = heap.tag(wrapped);
  const auto wrapped_offset = heap.offset(wrapped);
  const auto size = heap.size(a);
  std::ostringstream out;
  b.write(out);
  btor2_test::trace_replayt replay(out.str());
  replay.step();
  replay.step();
  REQUIRE(replay.value(a0_value) == 11);
  REQUIRE(replay.value(b8_value) == 22);
  REQUIRE(replay.value(last_value) == 33);
  REQUIRE(replay.value(past_value) == 0);
  REQUIRE(replay.value(legal) == 1);
  REQUIRE(replay.value(illegal) == 0);
  REQUIRE(replay.value(wrapped_tag) == 3);
  REQUIRE(replay.value(wrapped_offset) == 0);
  REQUIRE(replay.value(size) == mp_integer(4294967288));
  REQUIRE(out.str().find(" bad ") == std::string::npos);
  REQUIRE(out.str().find(" constraint ") == std::string::npos);
  if(mode.bitvectors)
  {
    heap.copy_range(a, other, b.constd(scalar, 8));
    REQUIRE(heap.failed);
    REQUIRE(heap.failure_reason.find("native Array") != std::string::npos);
  }
}

TEST_CASE(
  "Pure BV does not silently truncate symbolic allocations",
  "[goto-btor2][symbolic-heap]")
{
  symbolic_heap_fixturet f;
  f.program.add(goto_programt::make_assignment(
    f.n, side_effect_expr_nondett(f.n.type(), source_locationt{})));
  f.allocate(f.bytes());
  f.program.update();
  btor2_buildert b;
  array_encoding_optionst mode;
  mode.symbolic_heap = mode.symbolic_heap_arrays = true;
  mode.symbolic_heap_wide_offsets = true;
  heap_modelt heap(b, f.ns, 0, mode);
  heap.has_dynamic_allocations = true;
  heap.plan_capacity(f.program);
  REQUIRE(heap.failed);
  REQUIRE((heap.failure_reason.find("storage size") != std::string::npos ||
           heap.failure_reason.find("bitvector width") != std::string::npos));
}
