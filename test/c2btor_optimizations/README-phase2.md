# Phase 2 logical-array regressions

`cases-phase2.json` is separate from the phase 1 manifest. It covers element-only
multidimensional arrays, VLA dimensions after their DECL-time value changes,
static zero/explicit initialization, automatic partial initialization, stable
unwritten byte behavior, and repeated stores to the same element. Pointer
address escape and unsigned-char byte aliases exercise object-storage fallbacks
and require direct element reads to observe the indirect mutation.

Boolean arrays check normalization of nonzero initializers and stores to 1,
zero stores to 0, and implicit zeros in automatic partial initialization. The
eligible pointer-identity case places an element-only array before an
addressable scalar. The generic-pointer case supplies a fixed NULL input and
requires object storage for its array. Both observe the integer value of
`&other` and compare the exact bits between flag settings; the generic case
uses the existing map observation of an inlined auxiliary return. Neither
case assumes a particular object tag.

Float and double arrays check nonzero static and automatic initializers and
successive exact 1.5/2.5 overwrites. Negative-zero signs are observed through
the converter's supported IEEE reciprocal comparison, `1.0 / value < 0.0`,
since the converter does not dispatch the frontend's `signbit` expression.
This checks the converter's IEEE modeling contract for the supplied inputs.

Each array has an explicit metadata expectation. With logical arrays enabled,
eligible arrays must appear in `memory.logical_arrays`, have the declared rank
and element width, preserve dynamic dimension states, use the requested
BV/Array/Mixed backend, and retain reserved object identities. Fallback arrays
must remain in `memory.objects` with canonical byte-storage data. With the
flag disabled, all arrays use object storage. These structural checks are
separate from the finite property replay.

`logical-large-used-vla` uses 100,000,000 unsigned elements on ILP32 and touches
both the first and last element. Its 400,000,000-byte extent exceeds the object
byte-offset capacity. With logical arrays disabled, all encodings must reject
conversion for that capacity reason and leave no model. With logical arrays
enabled, Array/Mixed must convert, parse, and replay; BV must reject the
3,200,000,000-bit packed width with the declared format-limit reason. Expected
rejections are passed cases with `model_passed=false`, never parser/replay
successes.

`logical-large-write-only-vla` gives an equally large array a nondeterministic
size and RHS, but never reads the array. An unrelated `&other` retains observable
object identities and prevents the state prepass from deleting the object.
Without logical arrays, conversion must reject the object extent. With logical
arrays, all three backends must accept it, reserve its identity, classify it as
`storage=unused` with no data or dimension state, and preserve both nondet call
observations. A separate normalized C `unsigned a[n++]` fixture checks that the
frontend-lowered increment still changes `n` from 2 to 3 even when the unused
array has no data storage. An unrelated address observation keeps object
identities visible. Its disabled-flag object state may be pruned after planning.
The default matrix has 180 cases: 168 ordinary runs, 6 large used
VLA runs, and 6 large write-only VLA runs. Seven expected representation
rejections leave 173 models to parse and replay.

The stable-byte case checks the converter's explicit stable-unwritten-byte model
contract. It does not claim to establish standard C semantics for indeterminate
values. Its fixed trace gives nondet calls their manifest values and gives all
other inputs the seed `17 * frame + input_ordinal + 1`, reduced to the input bit
width. Array inputs use the same reduced seed as their default element value.
This detects accidental resampling at a later read.

```sh
python3 scripts/check_c2btor_optimizations.py \
  --regression-manifest test/c2btor_optimizations/cases-phase2.json \
  --before /path/to/frozen/c2btor \
  --common-arg=--goto-btor2-optimize-state \
  --after-arg=--goto-btor2-logical-arrays \
  --catbtor /path/to/catbtor --btorsim /path/to/btorsim \
  --output-dir test/c2btor_optimizations/results/phase2-regressions
```

The logical-array flag must exist in the selected converter. Both variants use
state optimization so that the comparison isolates logical storage. The harness
supports per-case `configs` and conditional `conversion_rejections` in the
manifest, and reports paired value comparisons in `comparisons.json`. Use the
separate `cases-witness-phase2.json` manifest for the export/translate/offline-lint
smoke, with the same common and after flags. Neither suite invokes a solver or
CPAchecker. Its two supplied nondet values initialize an eligible logical array;
a copied element and direct read lead to `reach_error`. The 12 runs must retain
both distinct call observations, bind the export hashes, and produce both return
waypoints followed by the target.

The final frozen converter has SHA256
`057d6b9881b361b0f123b1c7a21f9612097658ce37b101db45cb72ddb658b442`.
Its 449 assertions in 43 `[goto-btor2]` unit cases passed. All 180 finite cases
passed: 173 conversion/parser/replay successes and 7 expected representation
rejections. All 12 paired identity observations and all 12 witness round trips
passed. No model checker, solver, or CPAchecker was run.

The exact 770-record matrix completed all 4,620 conversion/parser attempts using
the same converter for flag off/on, common state optimization, 3 workers, a
4 GiB process-tree RSS limit, a 128 MiB model-file limit, and 60/30 second
conversion/parser limits. Maps were omitted from benchmark models. The original
770 records include four recursive sources; the separate nonrecursive cohort
contains 766. Raw conversion/parser counts are retained here and in
[phase2-results.json](phase2-results.json).

| Encoding | Raw 770 off pass / fail | Raw 770 on pass / fail | Nonrecursive 766 off pass / fail | Nonrecursive 766 on pass / fail | Newly converted |
|---|---:|---:|---:|---:|---:|
| BV | 554 / 216 | 554 / 216 | 553 / 213 | 553 / 213 | 0 |
| Array | 554 / 216 | 604 / 166 | 553 / 213 | 603 / 163 | 50 |
| Mixed | 554 / 216 | 604 / 166 | 553 / 213 | 603 / 163 | 50 |

All failures were conversion rejections. There were no new failures among
previously successful tasks, no bad-count mismatches, and no constraint-count
increases on comparable models. The 554 common-success tasks per encoding are
the cohort for the following model-size comparison; newly converted models are
excluded from these reductions.

| Encoding | States off → on | Numeric nodes off → on | Read ops off → on | Write ops off → on | Bytes off → on | Byte reduction |
|---|---:|---:|---:|---:|---:|---:|
| BV | 5,526 → 5,377 | 1,477,176 → 1,341,412 | 0 → 0 | 0 → 0 | 33,031,876 → 29,846,567 | 9.64% |
| Array | 5,120 → 5,330 | 2,234,524 → 1,815,879 | 22,889 → 4,663 | 18,774 → 9,981 | 51,773,340 → 41,578,270 | 19.69% |
| Mixed | 5,139 → 5,333 | 2,231,774 → 1,812,379 | 20,531 → 2,446 | 18,450 → 9,720 | 51,695,240 → 41,489,212 | 19.74% |

Array/Mixed state counts increased on this cohort while node, read/write, and
byte counts decreased. Instruction positions (107,500), PC positions (30,775),
active PC entry guards (30,680), and PC equality guards (32,224) were unchanged
for each encoding. The totals below instead include **all successful on models**,
including the 50 newly converted Array/Mixed tasks.

| Encoding | Successful on models | States | Numeric nodes | Read ops | Write ops | Bytes |
|---|---:|---:|---:|---:|---:|---:|
| BV | 554 | 5,377 | 1,341,412 | 0 | 0 | 29,846,567 |
| Array | 604 | 5,981 | 1,845,539 | 4,825 | 10,153 | 42,152,556 |
| Mixed | 604 | 5,984 | 1,842,039 | 2,608 | 9,892 | 42,063,498 |

The raw failure taxonomy before optimization was 138 allocation-byte-capacity,
55 runtime-object-byte-capacity, 21 automatic-object-lifetime, 1 allocation-count,
and 1 no-selected-source-property rejection per encoding. With logical arrays
enabled, Array/Mixed retain 138, 5, 21, 1, and 1 respectively. BV additionally
rejects 50 logical arrays for packed-width/bound limits. The property-free source
`array-examples/sanfoundry_43_ground.i` deliberately remains a rejection. The
three additional local-manifest tasks are listed separately in the JSON and
were not silently included. Thus phase 2 improves conversion coverage but does
not complete conversion of all 770 targets; general heap/byte capacity and
lifetime/count requirements remain.

All 770 primary source hashes agree across flag settings, current files, and
the phase 1 ledger; task YAML hashes also agree. All 3,424 successful benchmark
model hashes and all converter/parser/simulator hashes were rechecked without
drift. The ignored evidence directories are `results/phase2-final-regressions`,
`results/phase2-final-witness-smoke`, and `results/phase2-final-lab1-full`. The
last directory contains the exact selection, per-case commands/logs/models,
aggregate summaries, `source-hashes.json`, and `analyze_phase2.py`; the JSON report
records their hashes, resource limits, cohorts, and newly converted task names.
These checks establish conversion/parser acceptance and finite regression
behavior, not unbounded safety or semantic equivalence proofs.
