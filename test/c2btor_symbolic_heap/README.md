# Symbolic heap regressions

These fixtures exercise the implemented, default-off symbolic heap flags.
They do not invoke an operating-system allocation,
model checker, SAT/SMT solver, or report C SAFE/UNSAFE verdicts.

The staged flags are recorded in the manifest: phase1 retains allocation size
expressions/snapshots under `--goto-btor2-symbolic-heap` while preserving existing
capacity rejection thresholds; phase2 adds `--goto-btor2-symbolic-heap-arrays`;
phase3 adds `--goto-btor2-symbolic-heap-wide-offsets`. `expected_on` describes
the completed feature, not phase1 acceptance. Phase4 adds
`--goto-btor2-symbolic-heap-compact`: only symbolic dynamic slots reuse their
initial/runtime states, and only a conservative CFG certificate permits
aligned uniform 64-bit accesses to use 64-bit cells. Mixed-width aliases retain
byte cells.

Delivery overview: IMPLEMENTATION.md describes the changed structures/call chain
and explicit boundaries. README-phase4.md and phase4-results.json give final
on/off metrics. lab1-final-results.json and FAILED_CASES.md give the exact
nonrecursive Lab1 conversion cohort. The phase3 explicit-state recheck corrects
the initial Array seed coverage of its earlier finite runs.

Example final Array command (select --32/--64 from the task YAML):

```sh
build/bin/c2btor program.c --32 --goto-btor2 --inline \
  --memory object --array array --goto-btor2-merge-bads \
  --goto-btor2-symbolic-heap --goto-btor2-symbolic-heap-arrays \
  --goto-btor2-symbolic-heap-wide-offsets --goto-btor2-symbolic-heap-compact \
  --goto-btor2-out model.btor2
catbtor model.btor2
```

For BV with dynamic Array fallback, select --array bv and explicitly add
--goto-btor2-symbolic-heap-bv-array-fallback. Such output contains Array sorts.

`check_conversion.py` reuses the existing bounded subprocess/parser/metrics
helpers without changing their file. It freezes a binary when requested and
only writes under this directory. The default records 20s conversion and 10s
parser timeouts plus a 64MiB output-file limit. RSS sampling (`ps`) and lowering
RLIMIT_DATA are unavailable in this macOS sandbox, so the recorded baseline has
no memory limit or peak RSS measurement. Example baseline (output must be new):

```sh
python3 test/c2btor_symbolic_heap/check_conversion.py \
  --catbtor /Users/west/Developer/btor2tools/build/bin/catbtor \
  --output test/c2btor_symbolic_heap/baseline/off --freeze-binary
```

Add repeated `--feature-flag=...` arguments for a staged run. This recorder is
descriptive: inspect status/count mismatches and diagnostics in results.json;
its exit status does not assert semantic correctness. All output directories
are ignored by the new directory's `.gitignore`.

`cases.json` is the expectation manifest. T1 refers to the original
`../lab1-data/array-fpi/nsqm-iff.c` and its ILP32 task in place; no replacement
benchmark is copied here. Its actual malloc parameter is `unsigned int`.
All new fixtures use `fixture_types.h`, where `typeof(sizeof(int))` selects
size_t/uintptr_t from the CBMC target rather than unavailable host SDK headers.
The supported object-size primitive is `__CPROVER_OBJECT_SIZE` (uppercase).

Every source fixture has one intentional source assertion. With merge-bads,
conversion should retain one bad and no heap-created property roots. Tests use
ordinary `if (...) return` guards for malloc failure and nondet choices. No
fixture adds an assume or an auxiliary memory-safety property. `r_ok` assertions
are source assertions deliberately testing already supported metadata queries.

| Group | Intent and expected observations |
| --- | --- |
| T1 | Two symbolic-sized events, original source bad; supplied N=1 successful-allocation trace should exhibit original assertion failure. |
| T2 | 4294967288-byte objects stay isolated at a[0]/b[8]; a second fixture also writes offset 4294967280 in both objects. No capacity-sized enumeration. |
| T3 | `__CPROVER_OBJECT_SIZE` is 24 before and after n changes to 1; p[2] remains accessible and holds 7. |
| T4 | Existing constant 16-byte alias path still shares bytes and metadata. |
| T5 | Last element and legal one-past pointer formation are separated from a deliberate one-past dereference fixture. |
| T6 | An unbounded loop of constant 8-byte events still rejects; a certified three-iteration site creates three identities. |
| T7 | Two allocation expressions reuse the one saved n result across intervening state transitions. |
| T8 | Legal C union representation/unsigned-char aliases cover 8/16/32/64-bit views; a separate deliberate post-free fixture observes existing totalization. |
| T9 | Size-t multiplication differs under 32/64-bit targets; an unsigned-int wrapper parameter truncates to 8 in both. The actual original-style malloc declaration is tested only under ILP32, where it matches the library model. |
| Boundaries | Pointer/integer round trip and addressable pointer storage must reject explicitly until C-width serialization of hidden pointers is implemented faithfully. |

The 32-bit T2 successful-allocation branch uses the existing abstract malloc
success semantics. It is a representation test, not a claim that a concrete
32-bit process can obtain two allocations totaling nearly 8 GiB. Report the
success premise explicitly. The offset must still preserve every target-width
bit; using tag bits to truncate the offset is not an acceptable success model.

`t2_symbolic_extent.c` adds a genuine non-singleton size range
`10 <= n <= 536870911`, without an assume or equality guard. Two manifest
entries supply n=10 and n=536870911 to that same source. They exercise symbolic
byte-array storage at 80 and 4294967288 bytes, respectively, while the emitted
model remains the same apart from supplied trace inputs. Each trace checks
first/last values, b[8], distinct tags, both size snapshots, last legal offsets,
and unchanged pointer sizeof. The original equality-guard T2 fixtures remain
as compatibility checks. Neither different initial values across these supplied
traces nor successful replay establishes C SAFE or standard-C equivalence.

All successful symbolic models must use Array storage without creating elements
or per-byte initialization bitmaps proportional to capacity. Use `--array array`
first. BV/flatten modes may explicitly reject or select a documented equivalent
backend. Constants must preserve the existing optimized path. Exactly two heap
events in T1/T2 and no bounds-dependent node growth should be checked separately
from parser acceptance and finite data observations.

T5's one-past dereference and T8's post-free access contain deliberate C UB.
Their numeric data observations have no standard-C expected verdict. Compare
the symbolic case against a generated constant-size counterpart **within the
same existing backend**, under the same fully supplied inputs and seed policy.
Metadata stays independently observable. Ordinary post-free reads/writes must
not silently acquire new live/size gating or an extra bad/constraint.

The existing `scripts/check_c2btor_optimizations.py` offers reusable helpers:
`run` records command/result/logs with wall/RSS/file limits; `nodes_from` and
`structural_metrics` read emitted nodes; `vcd_frames` reads concrete observations.
Its `simulate` is intentionally tailored to fixtures whose target assertion
fails: it expects exactly one target failure and constant nondet port values in
every frame. Do not pass these positive assertions directly to that function.
A focused harness here can reuse the parser and trace mechanics while checking
assertions only when their mapped ASSERT executed signal is true. It should
require no executed source failure for T2/T3/T4/T5-last/T7/T8-legal/T9, require
the original source failure for T1 at supplied N=1, and observe UB data without
calling it C SAFE.

`check_finite.py` implements the focused finite harness. It creates a separate
model with LBE observation outputs, checks every mapped source ASSERT's executed
frame, and records source failures only at those frames. These observation
models are not used in the no-LBE conversion/hash comparisons. T1 supplies N=1
and expects the original source failure; positive fixtures require actual
assertion execution and no source failure during their supplied prefix. T5/T8
UB fixtures additionally generate a constant-allocation counterpart and compare
their numeric observations within the same backend.

T7 additionally uses a supplied frame-varying schedule for the **nondet n port**
after its call executes. Keeping that port fixed for all frames cannot catch a
translator that rereads the input instead of saved n state. Maps identify the
call/result state and executed frame. The script first records each call's
frame using a fixed supplied trace, then supplies the chosen result at that
frame and different input values at other frames. Every emitted input,
unwritten-byte array seed, and initialization input is explicitly supplied.
Use `--vary-all-source-inputs` to repeat this schedule for all other fixtures.
`--array-seed-byte 0x3d` supplies the same repeated byte pattern to every Array
element width (8-bit 0x3d or 64-bit 0x3d3d3d3d3d3d3d3d), consistently across
frames. The default byte is 0. This chooses a fully supplied arbitrary value;
it does not define malloc's general contents as zero. The new symbolic calloc
fixture uses n in 2..3, supplied n=3, to verify that untouched cells are zero
even with the nonzero raw seed, and that writing the first word leaves the
last word zero.

The current BTOR2 CLI has an existing **malloc-success policy**:
`cbmc_parse_options.cpp` forces `malloc_failure_mode_none`, and the CLI does not
register `--malloc-may-fail`, `--malloc-fail-null`, or `--no-malloc-may-fail`.
The harness probes and records those options' actual rejection. It does not
invent a failure input. This actual CLI path is narrower than AGENTS.md's
general statement that malloc failure branches are BTOR2 inputs. Success
traces and their source guard/assertion execution remain mandatory.

Example after the full-offset feature is available (choose fresh output):

```sh
python3 test/c2btor_symbolic_heap/check_finite.py \
  --output test/c2btor_symbolic_heap/results/finite-phase3 \
  --freeze-binary --vary-all-source-inputs \
  --feature-flag=--goto-btor2-symbolic-heap \
  --feature-flag=--goto-btor2-symbolic-heap-arrays \
  --feature-flag=--goto-btor2-symbolic-heap-wide-offsets
```

Simulator success means only that these fully supplied finite executions met
their observation contract. It is neither bounded safety proof nor C SAFE.

T1's original source calls abort twice on different paths. Existing CBMC
library lowering represents those aborts as two mapped ASSUME-false constraints;
they are not newly generated heap constraints. The harness accepts only that
explicit provenance and scores each frame only while every constraint holds.
At supplied N=1, source failure precedes the abort constraint becoming false.
No subsequent invalid frame contributes to the scored execution prefix.

BtorSim may omit a static VCD suffix after all signals stop changing. The
harness carries that suffix only if simulator stdout confirms all requested
steps and the last observed PC is a mapped END_FUNCTION self-loop. It does not
accept an unexplained truncated VCD trace.

For the range helper, add a structural check that byte_offset + access_bytes is
compared at least one bit wider than the widest operand, and a supplied-offset
wraparound metadata fixture if such a wider pointer can be formed faithfully.
Source `r_ok` queries must not introduce a hidden constraint or property.
