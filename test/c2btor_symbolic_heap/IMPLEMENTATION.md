# Symbolic allocation implementation and boundaries

The four default-off stages extend the existing object-memory implementation.
They do not add a second heap, a heap safety property, an assumption, or an
allocation-count cutoff. Only the selected original ASSERTs produce bad.

## Source changes and main call chain

| Files | Responsibility and core structures |
| --- | --- |
| src/cbmc/cbmc_parse_options.{h,cpp}, README.md, array_encoding.h | Register staged flags and dependencies; keep object/BV/Array/Mixed choices; explicit native-Array permission in BV mode. |
| memory_capacity.{h,cpp} | allocation_size_infot holds the actual typed alloc_size_expr, instruction and optional interval. Recording bytes does not change event-count analysis. |
| heap_model.{h,cpp} | Existing objectt, local_objectt, updatet and fresh/live/size/readonly states remain authoritative. Separate source pointer_bits/size_sort from internal pointer_value_bits/pointer_sort. |
| memory_access.{h,cpp} | Object collection, typed allocation operand conversion, pointer arithmetic and explicit unsupported serialization checks. |
| object_memory.cpp | local_objectt.symbolic_capacity selects fixed-domain native data Arrays. Size remains an allocation-time byte snapshot. Optional certified cells and seed-state deduplication. |
| expr_to_btor2.{h,cpp}, goto_btor2.cpp | Configure hidden scalar-pointer width before state creation; permit Array sorts only with explicit BV fallback; keep property/mapping generation. |
| goto_btor2_format.cpp, object_copy.cpp | Machine-size arithmetic remains source width; native packed-range events fail explicitly, while CLI copies use existing byte lowering. |
| symbolic_heap_cells.{h,cpp}, CMakeLists.txt, Makefile | Independent conservative CFG alignment certificate; no program rewrite. |
| unit/goto-btor2/symbolic_heap*.cpp, finite_btor2_replay.h | Capacity, snapshots, full offsets, byte aliases, cast/unknown pointer boundaries, assertion order and cell-certificate regressions; supplied-value evaluator only. |
| test/c2btor_symbolic_heap | T1–T9 C fixtures, parser/finite/dataset harnesses, frozen comparison ledgers and failure exports. |

The CLI first performs existing heap/library lowering and function inlining.
Function-parameter conversions therefore happen before the allocation operand
is recorded. In particular, original nsqm's ILP32 unsigned-int malloc argument
is not silently replaced by an infinite-precision or hard-coded 64-bit product.
Size-t arithmetic and an unsigned wrapper parameter are tested separately under
ILP32/LP64. The CLI's existing malloc_failure_mode_none policy remains unchanged.

write_goto_function_btor2 → converter.convert → memory.collect →
heap.plan_capacity → collect_variables/locations/plan_blocks →
memory.create_states and scalar/PC state creation → memory.initialize_static →
process_instructions/process_block →
memory.convert(ID_allocate) → heap.allocate → write_meta(size/live), fresh update
→ heap.end/finish → generate_transitions/properties → builder.write/source map.
Ordinary loads/stores share object-local data selected by tag and byte offset.
No object base is computed by adding a preceding object's symbolic length.

## The old rejection and its independent count boundary

plan_capacity previously rejected incomplete allocation byte bounds with
“cannot determine storage size for an allocation”, or rejected a large bound
against the signed offset payload left after the object-tag bits. Merely
removing that check would lose valid high offsets on ILP32. The native symbolic
path instead records size, uses a fixed index sort and, when required, a hidden
tag plus full machine-width byte offset. Small bounded allocations retain the
old pointer representation and constant/Mixed optimizations.

Event identities still use finite_slots → infer_allocation_slots. If needed,
unroll_malloc_counted_loops summarizes only the private sizing copy, then count
analysis runs again. An unbounded allocating cycle or explicit identity budget
still rejects conversion. nsqm has two events before three nonallocating loops;
the emitted loops retain PC backedges. Neither N nor its upper bound is enumerated.

Allocation evaluates its already-converted byte expression once at that event,
stores it in the existing size state and obtains a fresh tag. Later changes of
N cannot resize it. free updates live and does not recycle identities or discard
the retained size/data. Malloc contents remain arbitrary and stable; calloc
uses the existing zero-storage update.

## The performance switch

--goto-btor2-symbolic-heap-compact operates only on symbolic dynamic slots.
Untouched initialization states are used directly as runtime states; their
initial next declarations are deferred so each state gets exactly one next.
If initialization changed a field, the old two-state initialization is preserved.

The independent cell certificate tracks sets of byte-offset residues modulo 8
at CFG joins and backedges. Allocation/NULL, copies, casts and typed strides
propagate facts. Unknown effects and alias writes conservatively lose facts.
Every actual indirect access must be a scalar 64-bit, eight-byte access proven
aligned. Byte operations, mixed widths, aggregates, volatile/atomic values,
unknown calls and cast-lvalue writes select the original byte backing. ASSERT
conditions are never premises, and ASSERT(false) does not terminate analysis.
Too-narrow offset domains also keep bytes.

Certified storage uses Array(BV(offset_bits-3), BV64). Pointers and sizes remain
in bytes; indexing discards only the proven-zero low three offset bits. Each
whole-word access still uses the existing tag and W+1 byte-range guard. All
other cases keep byte lanes and one authoritative backing. No bounds-dependent
bitmap or per-element initialization is created.

## Explicit boundaries and validation scope

- Native symbolic storage currently requires --memory object. Global-heap
  storage, unrelated VLA sizing and automatic-lifetime certification are unchanged.
- Pure BV retains packing limits. --goto-btor2-symbolic-heap-bv-array-fallback
  explicitly allows dynamic native Arrays; its output includes Array sorts and
  is not a pure-BV model. Insufficient explicit storage/identity limits reject.
- When hidden widening is necessary, arbitrary machine-pointer inputs, non-null
  integer/pointer serialization, addressable pointer-bearing objects and pointer
  byte/bit views reject with no model. NULL, pointer copies/casts, Boolean tests,
  tag-preserving offset arithmetic and same-object differences are supported.
- Legal 8/16/32/64-bit data aliases share bytes. A failed cell certificate uses
  bytes; it does not mark a supported mixed access unsupported. Raw native
  packed-range events require prior byte lowering and otherwise reject explicitly.
- Existing UB totalization is retained and depends on encoding. Data access is
  not newly gated by live/readonly; W+1 storage range selection is not a new bad
  or constraint. Deliberate one-past/post-free observations are not C verdicts.
- The huge ILP32 isolation tests use the existing abstract allocation-success
  premise; they do not claim a physical process can allocate almost 8 GiB while
  exposing standard 32-bit address bytes. Unsupported serialization is explicit.
- Missing rules/representations emit no model. No incomplete encoding is labeled
  SAFE. Local backend SAFE/FALSE/UNKNOWN verdicts are NOT_RUN as requested.

catbtor checks syntax/types. BtorSim and the unit evaluator only replay fully
supplied finite prefixes. T1 reaches its source failure before abort constraints
become false. T2, snapshots, aliases, initialization and changing nondet ports
are independently checked; those successful prefixes do not prove safety.
Source map version/locations remain intact, with additive memory metadata and
actual node references. Original model/map hashes and observation-model hashes
are kept separate. No local solver, model checker or CPAchecker is invoked.
