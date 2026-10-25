# Phase 3 finite execution evidence

`finite-phase3-results.json` passes with **108 configurations: 90 finite
regression passes, 18 explicit expected rejections, and zero discrepancies**.
Array/Mixed contribute 72 configurations (60/12); BV with the explicit Array
fallback contributes 36 (30/6). Rejections cover unbounded allocation events and
the two unsupported pointer serialization boundaries.

The reviewed frozen converter SHA256 is
`1044d1eefec21314869c54fbaf74f89033b08598cc2b04a495a0eac63cb6343d`.
Each accepted configuration has a fixed supplied trace and a trace whose source
nondet input ports change after their call frames. In total, 180 fixture traces
and 24 same-backend constant-size UB counterpart traces were replayed. All
emitted input ports are explicitly supplied. Array input elements use a
constant repeated 0x3d byte pattern. The original P3 harness did not explicitly
assign no-init Array states at `#0`; BtorSim selected their checking-mode
defaults. Thus this old ledger's raw-initial-state coverage is incomplete,
although its recorded conversions and supplied port traces remain unchanged.
`phase3-explicit-state-recheck.json` and the new
`results/finite-phase3-explicit-states` directories supersede only that initial
state coverage after replay with explicit repeated-byte state assignments.
These are chosen arbitrary initial values, not a default malloc-zero rule.
Every source ASSERT is
checked at its actual executed frame, so an early return cannot masquerade as a
successful positive regression.

The explicit-state recheck includes the two subsequently added calloc and
non-singleton mixed-byte fixtures: **120 configurations, 102 finite passes,
18 expected rejections, zero discrepancies**. It replays 204 fixture traces,
24 same-backend UB counterpart traces and four initial-cell readback traces.
All 388 no-init Array state assignments across fixture traces are supplied at
`#0`; initializer-constrained states are excluded. Independent readback observes
0x3d in byte cells and 0x3d3d3d3d in the two UB fixtures' 32-bit cells, while
the calloc zero helper remains zero. The earlier 108 source/status/model/map
records match exactly. P4 records are unchanged.

Original nsqm-iff remains the ILP32 file in lab1-data. At supplied N=1, its
source unreach-call executes and fails at frame 64 in all three encodings. Both
existing source-abort constraints still hold there; the first becomes false at
frame 66. Only frames 0 through 65 form the scored valid prefix. The two
constraints are individually attributed to `<builtin-library-abort>` ASSUME
instructions, not heap helper properties. Later requested frames are excluded.

The genuine non-singleton T2 source is replayed at N=10 and N=536870911. Both
values use the **same model hash for each target/encoding**, and all six pairs
pass. Maps show two object slots, 8-bit local arrays, null materialized
capacity/element counts, no byte bitmap, and
symbolic allocation expressions with bounds 80..4294967288 bytes. The source
assertion checks a[0], b[8], both last elements, distinct tags, sizes, last legal
byte offsets, and target pointer sizeof. The large offset is 4294967280.

Wide offsets activate only when capacity is unknown or exceeds the existing
signed offset range. T2's ILP32 interval activates full 32-bit offsets and a
35-bit hidden pointer. Its LP64 interval fits the existing signed range, so
the model preserves the existing 61-bit offset/64-bit pointer encoding and C
pointer serialization. Small/constant fixtures also retain their old pointer
path. The two rejection fixtures use a broad unsigned-long-long size range to
require widening in both targets, rather than rejecting harmless small pointer
serialization. The BV fallback's packed-data capacity limit is distinct from
the pointer's signed offset range.

T3 observes a 24-byte size snapshot after n changes to 1. T7 preserves n=3 and
both 24-byte sizes even when the input ports subsequently vary. Legal union and
unsigned-char byte aliases pass. Deliberate one-past/post-free numeric behavior
matches a generated constant-size counterpart **within the same encoding**;
those comparisons are not C safety claims. The configured size_t arithmetic
and original-style ILP32 malloc parameter conversions also pass.

Actual CLI probes reject malloc failure switches. The existing BTOR2
malloc-success policy remains unchanged; no failure input is synthesized.
Observation aliases append after the original maximum node ID, preserving
original bytes, source namespace markers, map and node IDs. Their models are
separate from no-LBE conversion/hash metrics. Compact static VCD suffixes are
carried only after confirmed simulator completion and a mapped terminal PC
self-loop. Every constraint is tested before scoring that frame.

Artifacts are in ignored `results/finite-phase3-reviewed` and
`results/finite-phase3-reviewed-bv-fallback`. Earlier
`results/finite-phase3`, `results/finite-phase3-bv-fallback`, and the initial
harness exploration `results/finite-phase3-initial` are retained and superseded.
Conversion/parser/simulation
timeouts were 20/10/30 seconds and output files were limited to 64MiB. This
environment provides no RSS measurement or memory cap.

Only parser/type acceptance, supplied finite executions and explicit rejection
checks were run. No solver/model checker was invoked, and no C SAFE/UNSAFE or
unconditional standard-C equivalence verdict is claimed. Rebuild the summary
without rerunning any tool using:

```sh
python3 test/c2btor_symbolic_heap/summarize_finite.py
```

Regenerate the current explicit-state coverage ledger separately:

```sh
python3 test/c2btor_symbolic_heap/summarize_phase3_recheck.py
```
