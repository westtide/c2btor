# Phase 3 scalar-block regressions

The converter flag is `--goto-btor2-scalar-blocks`. Both comparison variants
use `--goto-btor2-optimize-state` and `--goto-btor2-logical-arrays` so the
comparison isolates scalar block encoding.

Eleven finite scenarios produce 132 runs over ILP32/LP64, BV/Array/Mixed, and
flag off/on. They exercise unsigned wrap, signed/unsigned truncation, a diamond
with a skipped assertion, both branch results, 70 loop iterations with a static
accumulator, block-local temporary elimination, two distinct nondet calls copied
through the same source destination, and an assertion violation observed before
a later false assumption. Loops remain PC transitions; a supplied finite trace
of 2,049 frames allows the 70-iteration fixture to finish without unwinding or
searching for a path. Each scenario checks its source assertions and reaches one
deliberate target violation in the valid prefix.

The loop source expects total 7,455 and static accumulator 77 after 70 iterations.
The repeated-call source saves exact values 5 and 9 into separate copies, with
mapped assignment observations compared across flag settings and checked against
the exact values 5 and 9. The map must keep both distinct call/result
observations. `state_checks` require the static accumulator's state and forbid
block-local `block_temp`/`result` states when scalar blocks are enabled. Their
retained value observations must have the declared 32-bit type. An eliminated
state must not be replaced by a named free input; actual source DECL inputs are
allowed only when mapped to their declaration event.

Two existing phase 2 sources, `phase2_vla_latched.c` and the actual dimension
effect filename `phase2_dimension_effect.c`, add 24 runs. They require retained
DECL-time dimension state and preservation of the frontend-lowered increment
under scalar blocks. A further 12 runs cast supplied binary32 bits `0x3fc00000`
(1.5) into an unused int. An unrelated `&other` keeps the prepass from deleting
the expression before conversion. The mapped cast value must be exactly 1 even
if its destination has no state. `expected_unsigned_value` checks this supplied
value. A baseline pilot confirmed the discarded cast remains observable.

The separate scalar witness has exactly one conditional `reach_error` property:
`sum == 14 && first == 5 && current == 9`. The supplied 5/9 call values make its
arithmetic and branch observable. Twelve runs must export with matching hashes,
replay the supplied prefix, translate the two return waypoints and final target,
and pass offline lint. The BTOR witness header labels a supplied simulation
trace; it does not represent a solver SAT result. No solver or CPAchecker is run.

Scalar structural verification checks that ASSUME and nondet events stay
singleton blocks and each merged ASSERT is the last instruction in its block.
The local-temp and wrap cases require a merged terminal ASSERT. The skipped
diamond assertion must retain its source line/column metadata and have an
unexecuted observation over the supplied valid prefix.
Handcrafted terminal-IR edge cases are covered by the production unit-test owner.

```sh
python3 scripts/check_c2btor_optimizations.py \
  --regression-manifest /path/to/cases-phase3.json \
  --before /path/to/frozen/c2btor --frames 2048 \
  --common-arg=--goto-btor2-optimize-state \
  --common-arg=--goto-btor2-logical-arrays \
  --after-arg=--goto-btor2-scalar-blocks \
  --catbtor /path/to/catbtor --btorsim /path/to/btorsim \
  --output-dir test/c2btor_optimizations/results/phase3-regressions
```

Use `cases-witness-phase3.json` for the separate witness smoke. Final acceptance
also needs the frozen-binary unit run and exact 770-task conversion/parser
matrix, with common-success model metrics separated from newly converted models.

The final frozen converter SHA256 is
`2bbf68319ae180760e98be7c2cead25cf312ccd65e4686b91c008c90848e70a9`.
Its 598 assertions in 60 `[goto-btor2]` unit cases passed. All 132 finite
conversion/parser/replay runs and all 12 witness round trips passed. The 12
paired value comparisons retained exact copied values 5/9 and discarded cast
value 1. The static accumulator stayed in state; initialized local temporaries
lost their states while retaining 32-bit event observations and actual DECL
inputs. The skipped diamond ASSERT retained source line 11 and never executed
on the supplied path. Its column field is empty in the frontend map; the harness
records that actual value. The 70-iteration loop reached its target at frame 75
with scalar blocks enabled, using the supplied 2,049-frame trace.

The exact 770-record benchmark completed all 4,620 conversion/parser attempts
with common phase 1/2 flags, three workers, a 4 GiB process-tree RSS limit, a
128 MiB model-file limit, and 60/30 second conversion/parser limits. Maps were
omitted from benchmark models. Counts below include all original records and a
separate nonrecursive 766 cohort. They are conversion/parser outcomes, not
SAFE/UNSAFE results.

| Encoding | Raw 770 off pass / fail | Raw 770 on pass / fail | Nonrecursive 766 off pass / fail | Nonrecursive 766 on pass / fail |
|---|---:|---:|---:|---:|
| BV | 554 / 216 | 554 / 216 | 553 / 213 | 553 / 213 |
| Array | 604 / 166 | 604 / 166 | 603 / 163 | 603 / 163 |
| Mixed | 604 / 166 | 604 / 166 | 603 / 163 | 603 / 163 |

There were no newly converted tasks, no new failures, no bad-count mismatches,
and no constraint-count increases. Therefore the common-success cohort and all
successful on models coincide for each encoding. Their structural changes are:

| Encoding | PC positions off → on | Active PC entries off → on | PC equality guards off → on | Numeric nodes off → on | Bytes off → on | Byte reduction |
|---|---:|---:|---:|---:|---:|---:|
| BV | 30,775 → 28,245 | 30,680 → 28,155 | 32,224 → 28,883 | 1,341,412 → 1,340,147 | 29,846,567 → 29,763,358 | 0.28% |
| Array | 32,683 → 29,863 | 32,588 → 29,773 | 34,299 → 30,618 | 1,845,539 → 1,844,785 | 42,152,556 → 42,074,624 | 0.18% |
| Mixed | 32,683 → 29,863 | 32,588 → 29,773 | 34,299 → 30,618 | 1,842,039 → 1,841,286 | 42,063,498 → 41,985,621 | 0.19% |

PC positions decreased 8.22% in BV and 8.63% in Array/Mixed; equality guards
decreased 10.37% and 10.73%. Aggregate state counts were unchanged at 5,377,
5,981, and 5,984 respectively. Bitvector state bits decreased by 146 in BV and
158 in Array/Mixed. Array-state counts remained 0/558/505, read operations
0/4,825/2,608, and write operations 0/10,153/9,892. Instruction positions were
unchanged at 107,500 in BV and 110,680 in Array/Mixed. Thus this benchmark shows
control-position reduction with small node/byte reductions; it does not show
an aggregate state-count reduction. The explicit ASSERT fixtures separately
demonstrate block-local state elimination.

All failures remained conversion rejections. The raw taxonomy is unchanged from
phase 2 on: 138 allocation-byte-capacity, 5 runtime-object-byte-capacity,
21 automatic-object-lifetime, 1 allocation-count, and 1 no-selected-source-property
rejection per encoding; BV also has 50 logical-array packed-width/bound
rejections. `array-examples/sanfoundry_43_ground.i` deliberately remains a
property-free rejection. Four recursive sources are excluded only from the
secondary cohort, and the three additional local-manifest tasks remain outside
the exact 770 selection. Conversion of all 770 targets is still incomplete.

[phase3-results.json](phase3-results.json) records full metric totals, failure
taxonomies, exact flags, selected cases, and hashes. All 770 primary source and
YAML hashes agree across variants and current files; primary source hashes also
agree with phase 1 and phase 2. All 11 fixture-source hashes, all 3,524 successful
benchmark model hashes, and frozen converter/parser/simulator/harness hashes
were checked without drift. Ignored evidence is in
`results/phase3-reviewed-regressions`, `results/phase3-reviewed-witness-smoke`, and
`results/phase3-reviewed-lab1-full`, including the last directory's
`source-hashes.json` and `analyze_phase3.py`. No model checker, solver, or CPAchecker
was run; parser acceptance and these finite prefixes do not prove unbounded
safety or semantic equivalence.
