# Phase 3: full offsets and byte semantics

`--goto-btor2-symbolic-heap-wide-offsets` permits an internal object tag plus a
full machine-width byte offset **when the allocation extent needs it**. Small
bounded allocations retain the original pointer representation and layout.
The source pointer type, sizeof, integer widths and object byte layouts stay
unchanged. Machine-size expressions use size_sort; hidden pointers use
pointer_sort. Pointer difference uses W+1 bits before narrowing to ptrdiff_t.

Native Array and Mixed admit symbolic extents without materializing their
elements. Pure BV still rejects sizes it cannot pack. Explicit
`--goto-btor2-symbolic-heap-bv-array-fallback` permits native storage for the
dynamic slots; static objects/logical arrays keep their selected backend.
The CLI lowers Array copies to existing byte operations. Raw packed-range
events incompatible with native storage fail explicitly rather than abort.

The unit suite passes 1768 assertions in 83 cases. The conversion cohort has
108 configurations: 80 conversion/parser passes, 28 explicit unsupported;
Array and Mixed each pass 30/36, pure BV 20/36. Explicit BV Array fallback
passes 30/36. The six per-backend rejections are unbounded event counts and
the two wide-pointer serialization boundaries under 32/64-bit targets.
With new switches off, all 70 successful models have identical hashes to the
parent snapshot on the same updated fixtures. See phase3-results.json and
README-finite-phase3.md for separate conversion and finite-trace evidence.

Original nsqm-iff without LBE has 2 event identities, 2 active data Arrays,
4 data Array states including old seeds, 2 active/4 total size states, 35
total states, 111 PC positions and 2276 nodes. It has one source bad and zero
auxiliary bads. Two constraints are the existing library abort ASSUME false
instructions. Neither N nor its 536870911 upper bound is enumerated/unrolled.
The same variable-extent source is replayed with small and large supplied N;
the model hash stays the same. T2 independently checks object isolation.

Hidden-width mode explicitly rejects arbitrary machine-pointer inputs,
non-null integer/pointer serialization, pointer-bearing byte storage and
byte/bit views of pointers. Scalar pointer copies/casts, NULL, Boolean casts,
tag-preserving arithmetic and same-object differences remain supported.
Ordinary data access retains existing live-independent UB totalization;
the widened size guard is a storage-selection expression, not a new property
or path constraint. UB observations are not C safety verdicts.

No local model checker or solver ran. SAFE/FALSE/UNKNOWN backend verdicts are
NOT_RUN, as requested. A supplied T1 failure is a finite regression observation.
An initial whole-cohort batch used incomplete FILE declarations; its artifacts
are superseded. The checked-in aiob compatibility header copies its original
FILE layout for the separate library frontend. Final cohort counts are reported
with the phase 4 frozen binary and repaired declarations.
